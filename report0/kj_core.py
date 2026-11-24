# -*- coding: utf-8 -*-
"""kj_core.py -- 「虚実行」レポート用の計算コア。

ELDE (Exhaustive Lock Dependency Emulator, JRF 2011/2018, Perl) の考え方を
Python で再実装し、さらに拡張する。

プログラム(プロセス)の書き方:
    プロセスは「ジェネレータ関数 prog(out)」として書く。
      s = yield LOCK          # ロックを取る。共有状態 s を受け取る。
      s = put(s, "a", 1)      # 状態は不変(immutable)な辞書として扱う。
      yield unlock(s)         # 新しい状態 s を置いてロックを外す。
      s = yield WLOCK         # wait_and_lock (ELDE その2)
    out はリストで、print の代わりに out.append(...) する。
    複数ロックは lock("A") / unlock_("A", s) を使う(第 9 節)。

要件: ELDE と同じく、プロセスは状態に関して「関数的」(決定的)であること。
"""
from __future__ import annotations
import itertools
from functools import lru_cache
from collections import Counter, defaultdict
# ------------------------------------------------------------------
# 状態: 不変辞書 (sorted tuple of items)
# ------------------------------------------------------------------
EMPTY = ()


def get(s, k, default=None):
    for kk, v in s:
        if kk == k:
            return v
    return default


def put(s, k, v):
    d = dict(s)
    d[k] = v
    return tuple(sorted(d.items()))


def sdict(s):
    return dict(s)


LOCK = ("lock", "L")
WLOCK = ("wlock", "L")


def unlock(s, name="L"):
    return ("unlock", name, s)


def lock(name):
    return ("lock", name)
# ------------------------------------------------------------------
# 1 プロセスの再生(replay)
#   inputs[k] = k 番目の lock で受け取る状態。
#   返り値: (status, unlock_states, outputs, kinds)
#     status = "done"  : プロセスは終了した(全 lock を消化)
#              "need"  : inputs が足りない(次の lock を待っている)
#     kinds[k] = k 番目の lock 要求の種類 ("lock" / "wlock")
# ------------------------------------------------------------------
class Proc:
    def __init__(self, prog, name=None):
        self.prog = prog
        self.name = name or prog.__name__
        self._memo = {}

    def replay(self, inputs):
        inputs = tuple(inputs)
        if inputs in self._memo:
            return self._memo[inputs]
        out = []
        g = self.prog(out)
        ustates, kinds = [], []
        try:
            req = next(g)
            k = 0
            while True:
                assert req[0] in ("lock", "wlock"), req
                kinds.append(req[0])
                if k >= len(inputs):
                    res = ("need", tuple(ustates), tuple(out), tuple(kinds))
                    break
                msg = g.send(inputs[k])
                assert msg[0] == "unlock", msg
                ustates.append(msg[2])
                k += 1
                req = next(g)
        except StopIteration:
            res = ("done", tuple(ustates), tuple(out), tuple(kinds))
        self._memo[inputs] = res
        return res
# ------------------------------------------------------------------
# 実行の表現: 読み出し関係 rf (reads-from)
#   ノード (q, m) = プロセス q の m 番目のクリティカルセクション(CS)。
#   rf[(q,m)] = 読んだ状態を書いた CS。初期状態は INIT。
# ------------------------------------------------------------------
INIT = ("I", 0)


def readers(rf):
    """各ノード(INIT 含む)がいくつの CS に読まれたか。"""
    c = Counter(rf.values())
    return c


def is_linear(rf):
    """定理 1: 虚実行が実実行である ⇔ どの状態も高々一度しか読まれない。"""
    return all(v <= 1 for v in readers(rf).values())


def linear_order(rf):
    """実実行なら CS の全順序(列)を返す。"""
    child = {v: k for k, v in rf.items()}
    seq, cur = [], INIT
    while cur in child:
        cur = child[cur]
        seq.append(cur)
    assert len(seq) == len(rf)
    return seq


def canon(rf):
    return tuple(sorted(rf.items()))


def world_finals(res):
    """虚実行の各「世界」(木の葉)の最終状態。"""
    return [res.states[v] for v in leaves(res.rf)]


def leaves(rf):
    nodes = set(rf) | {INIT}
    return sorted(nodes - set(rf.values()))
# ------------------------------------------------------------------
# 実実行の総当り (ELDE その3 = elde_2.pl に相当。lock_limit 不要)
#   単一グローバルロック。wait_and_lock 対応。
# ------------------------------------------------------------------
class Result:
    def __init__(self, rf, outputs, finals, status, seq=None):
        self.rf = rf
        self.outputs = outputs      # tuple: プロセスごとの出力
        self.finals = finals        # tuple: プロセスごとの最後の unlock 状態
        self.status = status        # "ok" / "deadlock" / "wait"
        self.seq = seq

    def key(self):
        return canon(self.rf)

    def __repr__(self):
        return f"Result({self.status}, seq={self.seq}, out={self.outputs})"


def spec_str(seq):
    return ",".join(f"P{q}L{m}" for (q, m) in seq)


def enumerate_real(procs, init=EMPTY, max_steps=60):
    """すべての実実行(CS の全順序)を深さ優先で列挙する。

    wait_and_lock: プロセスが WLOCK を要求したとき、自分の直前の unlock
    以後に他プロセスの CS が 1 つ以上あった場合に限りロックを取れる。
    どのプロセスも進めず、未終了のプロセスがあれば "deadlock"。
    """
    P = len(procs)
    results = []

    def rec(inputs, seq, cur_state, last_writer, last_own_pos):
        stats = [procs[q].replay(inputs[q]) for q in range(P)]
        movable = []
        for q in range(P):
            st, us, out, kinds = stats[q]
            if st == "done":
                continue
            m = len(inputs[q])
            if kinds[m] == "wlock":
                # 自分の最後の CS の後に他者の CS があるか
                lp = last_own_pos[q]
                start = 0 if lp is None else lp + 1
                if not any(seq[i][0] != q for i in range(start, len(seq))):
                    continue
            movable.append(q)
        if not movable or len(seq) >= max_steps:
            rf = {}
            prev = INIT
            for node in seq:
                rf[node] = prev
                prev = node
            unfinished = [q for q in range(P) if stats[q][0] != "done"]
            status = "ok" if not unfinished else ("deadlock" if len(seq) < max_steps else "cutoff")
            results.append(Result(rf, tuple(s[2] for s in stats),
                                  tuple((s[1][-1] if s[1] else None) for s in stats),
                                  status, tuple(seq)))
            return
        for q in movable:
            m = len(inputs[q])
            new_inputs = list(inputs)
            new_inputs[q] = inputs[q] + (cur_state,)
            st, us, out, kinds = procs[q].replay(new_inputs[q])
            new_state = us[m]
            lop = list(last_own_pos)
            lop[q] = len(seq)
            rec(tuple(new_inputs), seq + [(q, m)], new_state, (q, m), tuple(lop))

    rec(tuple(() for _ in range(P)), [], init, INIT, tuple(None for _ in range(P)))
    return results
# ------------------------------------------------------------------
# 虚実行の総当り (ELDE その1 = elde_0.pl の意味論)
#   各 CS (q,m) は「自分の直前の unlock 状態(m=0 なら初期状態)」か
#   「他プロセスのいずれかの unlock 状態」を読む。
#   因果的に可能(rf ∪ プログラム順序 が非巡回)なものすべて。
#   level="imag" : ELDE0 そのもの
#   level="fork" : 各プロセスは自分の分岐から離れない(fork 線形化可能)
# ------------------------------------------------------------------
def enumerate_imag(procs, init=EMPTY, level="imag", max_events=40):
    P = len(procs)
    seen = set()
    results = {}

    def ancestors(rf, node):
        a = set()
        while node != INIT:
            a.add(node)
            node = rf[node]
        a.add(INIT)
        return a

    def rec(rf, inputs, ustate):
        key = canon(rf)
        if key in seen:
            return
        seen.add(key)
        stats = [procs[q].replay(inputs[q]) for q in range(P)]
        pending = [q for q in range(P) if stats[q][0] != "done"]
        if not pending:
            res = Result(dict(rf), tuple(s[2] for s in stats),
                         tuple((s[1][-1] if s[1] else None) for s in stats), "ok")
            res.states = dict(ustate)       # 各 CS の unlock 状態
            res.states[INIT] = init
            results[key] = res
            return
        if len(rf) >= max_events:
            return
        for q in pending:
            m = len(inputs[q])
            own = (q, m - 1) if m > 0 else INIT
            cands = [own] + [node for node in ustate if node[0] != q]
            for par in cands:
                if level == "fork" and m > 0 and par != own:
                    # 親が自分の直前 CS の子孫でなければならない
                    if own not in ancestors(rf, par):
                        continue
                s_in = init if par == INIT else ustate[par]
                new_inputs = list(inputs)
                new_inputs[q] = inputs[q] + (s_in,)
                st, us, out, kinds = procs[q].replay(new_inputs[q])
                rf2 = dict(rf)
                rf2[(q, m)] = par
                us2 = dict(ustate)
                us2[(q, m)] = us[m]
                rec(rf2, tuple(new_inputs), us2)

    rec({}, tuple(() for _ in range(P)), {})
    return list(results.values())
# ------------------------------------------------------------------
# ELDE その1 (elde_0.pl) の忠実な移植: lock 仕様 P{p}U{n}->P{q}L{m} の木
# ------------------------------------------------------------------
class Elde0:
    def __init__(self, procs, lock_limits, init=EMPTY):
        self.procs = procs
        self.L = lock_limits
        self.init = init
        self.rc = {}        # spec(tuple) -> result context (list per proc of unlock states) / None
        self.log = []

    def make_tree(self, spec=()):
        P = len(self.procs)
        max_u = [-1] * P
        max_l = [-1] * P
        for (p, n, q, m) in spec:
            max_u[p] = n + 1
            max_l[p] = n + 1
            max_u[q] = m
            max_l[q] = m + 1
        tree = {}
        for p in range(P):
            for q in range(P):
                if p == q:
                    continue
                for n in range(max(max_u[p], 0), self.L[p]):
                    for m in range(max(max_l[q], 0), self.L[q]):
                        part = (p, n, q, m)
                        tree[part] = self.make_tree(spec + (part,))
        return tree

    def _run_proc(self, q, spec):
        inputs = []
        own_last = self.init
        m = 0
        while True:
            st, us, out, kinds = self.procs[q].replay(tuple(inputs))
            if st == "done":
                break
            if m >= self.L[q]:
                raise RuntimeError("Reach the limit of lock count.")
            s_in = None
            for i, (p, n, qq, mm) in enumerate(spec):
                if qq == q and mm == m:
                    rc = self.rc.get(spec[:i])
                    if rc is None or n >= len(rc[p]):
                        return None  # lock spec is too long -> cut
                    s_in = rc[p][n]
                    break
            if s_in is None:
                s_in = own_last
            inputs.append(s_in)
            st, us, out, kinds = self.procs[q].replay(tuple(inputs))
            own_last = us[m]
            m += 1
        # 終了後: 仕様が実行されなかった lock/unlock を参照していたら cut
        for (p, n, qq, mm) in spec:
            if (p == q and n >= m) or (qq == q and mm >= m):
                return None
        return (tuple(us), tuple(out), tuple(inputs))

    def run_spec(self, spec):
        if spec in self.rc:
            return self.rc[spec]
        if spec and self.run_spec(spec[:-1]) is None:
            self.rc[spec] = None
            return None
        res = []
        for q in range(len(self.procs)):
            r = self._run_proc(q, spec)
            if r is None:
                self.rc[spec] = None
                self.log.append((spec, "cut!"))
                return None
            res.append(r)
        self.rc[spec] = [r[0] for r in res]
        self.log.append((spec, [r[1] for r in res]))
        self._last = res
        return self.rc[spec]

    def run(self):
        tree = self.make_tree()
        alive = []

        def walk(spec, node):
            if self.run_spec(spec) is None:
                return
            alive.append(spec)
            for part, sub in node.items():
                walk(spec + (part,), sub)
        walk((), tree)
        return alive

    def rf_of(self, spec):
        """生き残った仕様から読み出し関係 rf を作る。"""
        rf = {}
        for q in range(len(self.procs)):
            r = self._run_proc(q, spec)
            nlocks = len(r[0])
            for m in range(nlocks):
                par = (q, m - 1) if m > 0 else INIT
                for (p, n, qq, mm) in spec:
                    if qq == q and mm == m:
                        par = (p, n)
                        break
                rf[(q, m)] = par
        return rf

    def outputs_of(self, spec):
        return tuple(self._run_proc(q, spec)[1] for q in range(len(self.procs)))


def elde0_str(spec):
    return ",".join(f"P{p}U{n}->P{q}L{m}" for (p, n, q, m) in spec)
# ------------------------------------------------------------------
# 抽象的な「直線プログラム」(lock 回数だけを与える)での数え上げ
# ------------------------------------------------------------------
def straight_procs(Ls):
    """各プロセスは Ls[q] 回 CS を実行し、CS で自分の印を状態に追記する。"""
    procs = []
    for q, L in enumerate(Ls):
        def prog(out, q=q, L=L):
            for m in range(L):
                s = yield LOCK
                s = put(s, "log", get(s, "log", ()) + ((q, m),))
                yield unlock(s)
        prog.__name__ = f"P{q}"
        procs.append(Proc(prog))
    return procs


def count_levels(Ls):
    procs = straight_procs(Ls)
    real = enumerate_real(procs)
    fork = enumerate_imag(procs, level="fork")
    imag = enumerate_imag(procs, level="imag")
    return len(real), len(fork), len(imag)


def count_rf_only(Ls):
    """rf のみ非巡回(プログラム順序を無視: 「時間逆行」を許す) / 巡回も許す、の数。"""
    nodes = [(q, m) for q, L in enumerate(Ls) for m in range(L)]
    cands = {}
    for (q, m) in nodes:
        own = (q, m - 1) if m > 0 else INIT
        cands[(q, m)] = [own] + [(p, n) for (p, n) in nodes if p != q]
    n_acyc = 0
    n_all = 0
    for choice in itertools.product(*[cands[v] for v in nodes]):
        n_all += 1
        rf = dict(zip(nodes, choice))
        ok = True
        for v in nodes:
            seen = set()
            x = v
            while x != INIT:
                if x in seen:
                    ok = False
                    break
                seen.add(x)
                x = rf[x]
            if not ok:
                break
        if ok:
            n_acyc += 1
    return n_acyc, n_all


def cross_edges(rf):
    """他プロセスからの読み出し(ELDE0 の lock 仕様の各項 P p U n -> P q L m)。"""
    return sorted((v[0], v[1], k[0], k[1]) for k, v in rf.items()
                  if v != INIT and v[0] != k[0])


def is_elde0(rf):
    """ELDE0 の lock 仕様として表せるか。

    各項 e=(p,n,q,m) はプロセス p の局所時刻 2n+1(unlock n) と
    プロセス q の局所時刻 2m(lock m) を占める「受け渡し」。
    受け渡しの列が、関与する各プロセスの局所時刻について狭義単調に
    並べられる ⇔ 受け渡し間の先後グラフが非巡回で、同じ局所時刻の衝突がない。
    """
    es = cross_edges(rf)
    pts = defaultdict(list)          # process -> [(local_time, edge_index)]
    for i, (p, n, q, m) in enumerate(es):
        pts[p].append((2 * n + 1, i))
        pts[q].append((2 * m, i))
    succ = defaultdict(set)
    for r, lst in pts.items():
        lst.sort()
        for (t1, i1), (t2, i2) in zip(lst, lst[1:]):
            if t1 == t2:
                return False
            succ[i1].add(i2)
    # 非巡回判定
    color = {}

    def dfs(u):
        color[u] = 1
        for w in succ[u]:
            if color.get(w) == 1:
                return False
            if w not in color and not dfs(w):
                return False
        color[u] = 2
        return True
    return all(dfs(i) for i in range(len(es)) if i not in color)
