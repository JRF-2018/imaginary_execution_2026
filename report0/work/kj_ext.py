# -*- coding: utf-8 -*-
"""kj_ext.py -- 「虚実行」レポートの拡張計算。

  * 2 プロセスの ELDE0 仕様数の漸化式(パリティ制限付き Delannoy 型)
  * トンネル意味論(進行グラフの禁止領域を「すり抜ける」道)
  * 枝分かれ(葉の数)の母関数と、単位円上の積分による実実行の抽出
  * 複数ロック版モデル検査器(デッドロック検出・進行グラフ)
  * 確率的スケジューラ(ELDE その2 の「今後の課題」)
  * 時間ループ(自己参照 CS)の自己無撞着解と虚数
  * 階層の上(時間逆行 B・時間ループ L)での、自己無撞着性による実行の決まり方
"""
from __future__ import annotations
import cmath
import itertools
import math
from collections import Counter, defaultdict
from fractions import Fraction

from kj_core import (INIT, EMPTY, canon, get, put, Proc, LOCK, unlock,
                     enumerate_imag, enumerate_real, is_linear, is_elde0,
                     leaves, straight_procs)


# ------------------------------------------------------------------
# 2 プロセスの ELDE0 仕様の数
# ------------------------------------------------------------------
def elde0_count_2(a, b):
    """プロセス 0 が a 回、プロセス 1 が b 回 CS を持つときの ELDE0 lock 仕様数。

    局所時刻: lock m -> 2m, unlock n -> 2n+1。仕様の各項は
    「一方の unlock 点と他方の lock 点」の組 = 偶奇の異なる点の組。
    項の列は両プロセスの局所時刻について単調 = 単調な部分マッチング。
    f(i,j) = f(i-1,j) + f(i,j-1) - f(i-1,j-1) + [偶奇が異なる] f(i-1,j-1)
    """
    A, B = 2 * a, 2 * b
    f = [[1] * (B + 1) for _ in range(A + 1)]
    for i in range(1, A + 1):
        for j in range(1, B + 1):
            diag = f[i - 1][j - 1]
            f[i][j] = f[i - 1][j] + f[i][j - 1] - diag + (diag if (i - 1) % 2 != (j - 1) % 2 else 0)
    return f[A][B]


# ------------------------------------------------------------------
# トンネル意味論: 排他を無視した lock/unlock の任意のインタリーブで、
# lock は「その時点で最も新しい unlock 状態」を読む。
# ------------------------------------------------------------------
def tunnel_paths(Ls):
    """(rf, 道) の対応を返す。道は ((q, 'L'|'U', m), ...)。"""
    P = len(Ls)
    out = defaultdict(list)

    def rec(pos, last_unlock, rf, path):
        if all(pos[q] == 2 * Ls[q] for q in range(P)):
            out[canon(rf)].append(tuple(path))
            return
        for q in range(P):
            if pos[q] == 2 * Ls[q]:
                continue
            m = pos[q] // 2
            p2 = list(pos)
            p2[q] += 1
            if pos[q] % 2 == 0:
                rf2 = dict(rf)
                rf2[(q, m)] = last_unlock
                rec(tuple(p2), last_unlock, rf2, path + [(q, "L", m)])
            else:
                rec(tuple(p2), (q, m), rf, path + [(q, "U", m)])
    rec(tuple([0] * P), INIT, {}, [])
    return out


def path_crosses_forbidden(path):
    """道が「2 プロセスが同時にロックを持つ」状態を通るか。"""
    held = set()
    for (q, k, m) in path:
        if k == "L":
            held.add(q)
            if len(held) >= 2:
                return True
        else:
            held.discard(q)
    return False


# ------------------------------------------------------------------
# 枝分かれ母関数
#   虚実行 E の葉(誰にも読まれない状態)の数 ℓ(E)。
#   実実行 ⇔ ℓ(E) = 1 (N 本の辺を持つ根付き木で葉が 1 つ ⇔ 一本道)。
#   G(x) = Σ_E x^{ℓ(E)-1}。 #実 = G(0) = (1/2π)∫ G(e^{iθ}) dθ。
# ------------------------------------------------------------------
def leaf_poly(execs, weight=None):
    """execs の葉の数の分布 {ℓ-1: 重み和}。"""
    c = Counter()
    for e in execs:
        w = 1 if weight is None else weight(e)
        c[len(leaves(e.rf)) - 1] += w
    return dict(c)


def poly_eval(poly, z):
    return sum(c * z ** k for k, c in poly.items())


def circle_filter(poly, K=None):
    """単位円上の K 点平均 (1/K) Σ G(ω^k) で定数項を取り出す。"""
    deg = max(poly) if poly else 0
    if K is None:
        K = deg + 1
    vals = [poly_eval(poly, cmath.exp(2j * math.pi * k / K)) for k in range(K)]
    return sum(vals) / K, vals


# ------------------------------------------------------------------
# 複数ロック版のモデル検査器
#   プロセスは yield ("lock", name) で name の状態を受け取り、
#   yield ("unlock", name, s) で返す。yield ("wlock", name) は wait_and_lock。
# ------------------------------------------------------------------
class MProc:
    def __init__(self, prog, name=None):
        self.prog = prog
        self.name = name or prog.__name__
        self._memo = {}

    def replay(self, inputs):
        """inputs: 各 lock で受け取った状態の列。
        返り値: (status, next_req, events, held, out)
          events: 実行済みイベント列 [("L", name) / ("U", name, state)]
        """
        inputs = tuple(inputs)
        if inputs in self._memo:
            return self._memo[inputs]
        out = []
        g = self.prog(out)
        events = []
        held = []
        k = 0
        try:
            req = next(g)
            while True:
                if req[0] in ("lock", "wlock"):
                    if k >= len(inputs):
                        res = ("need", req, tuple(events), tuple(held), tuple(out))
                        break
                    events.append(("L", req[1]))
                    held.append(req[1])
                    req = g.send(inputs[k])
                    k += 1
                elif req[0] == "unlock":
                    events.append(("U", req[1], req[2]))
                    held.remove(req[1])
                    req = next(g)
                else:
                    raise ValueError(req)
        except StopIteration:
            res = ("done", None, tuple(events), tuple(held), tuple(out))
        self._memo[inputs] = res
        return res


def model_check(procs, lock_names, init=None, max_depth=200):
    """全インタリーブを状態の記憶つき深さ優先で探索する(lock_limit 不要)。

    大域状態 = (各プロセスの入力履歴の長さと内容, 各ロックの状態, 最終 unlock 者)。
    同じ大域状態は二度展開しない(ELDE その3 の「中途のコンテクストが同じもの
    は二度と実行しない」の一般化)。
    返り値: dict(終状態 -> 到達する lock 順序の例), deadlocks, n_states
    """
    P = len(procs)
    if init is None:
        init = {n: EMPTY for n in lock_names}
    finals = {}
    deadlocks = {}
    visited = set()
    n_edges = [0]

    def gstate(inputs, lstate, since):
        stats = [procs[q].replay(inputs[q]) for q in range(P)]
        # プロセスの局所状態は「出力と、今後の挙動を決める入力履歴」で決まる。
        return stats

    def rec(inputs, lstate, since, trace):
        stats = [procs[q].replay(inputs[q]) for q in range(P)]
        # 現在の各ロック状態: lstate (最後の unlock の状態)
        key = (inputs, tuple(sorted(lstate.items())), since)
        if key in visited:
            return
        visited.add(key)
        holders = {}
        for q in range(P):
            for n in stats[q][3]:
                holders[n] = q
        movable = []
        for q in range(P):
            st, req, ev, held, out = stats[q]
            if st == "done":
                continue
            name = req[1]
            if name in holders:
                continue
            if req[0] == "wlock" and not since[q]:
                continue
            movable.append(q)
        if not movable:
            unfinished = [q for q in range(P) if stats[q][0] != "done"]
            outs = tuple(s[4] for s in stats)
            fin = (tuple(sorted(lstate.items())), outs)
            if unfinished:
                deadlocks.setdefault(fin, trace)
            else:
                finals.setdefault(fin, trace)
            return
        if len(trace) >= max_depth:
            return
        for q in movable:
            st, req, ev, held, out = stats[q]
            name = req[1]
            new_inputs = list(inputs)
            new_inputs[q] = inputs[q] + (lstate[name],)
            st2, req2, ev2, held2, out2 = procs[q].replay(new_inputs[q])
            # lock を取ってから次の lock 要求(か終了)までのイベントをまとめて反映
            ls2 = dict(lstate)
            for e in ev2[len(ev):]:
                if e[0] == "U":
                    ls2[e[1]] = e[2]
            sn = list(since)
            sn[q] = False
            for r in range(P):
                if r != q:
                    sn[r] = True
            n_edges[0] += 1
            rec(tuple(new_inputs), ls2, tuple(sn), trace + ((q, name),))

    rec(tuple(() for _ in range(P)), dict(init), tuple(False for _ in range(P)), ())
    return finals, deadlocks, len(visited)


def progress_events(prog):
    """直線的なプログラムの lock/unlock 列を(状態に依存しない前提で)取り出す。"""
    p = MProc(prog)
    inputs = []
    while True:
        st, req, ev, held, out = p.replay(tuple(inputs))
        if st == "done":
            return [(e[0], e[1]) for e in ev]
        inputs.append(EMPTY)


def forbidden_rects(ev0, ev1):
    """進行グラフの禁止領域: 両プロセスが同じロックを持つ区間の直積。"""
    def intervals(ev):
        res = []
        open_ = {}
        for i, e in enumerate(ev):
            t = i + 1
            if e[0] == "L":
                open_[e[1]] = t
            else:
                res.append((e[1], open_.pop(e[1]), t))
        return res
    rects = []
    for (n0, a0, b0) in intervals(ev0):
        for (n1, a1, b1) in intervals(ev1):
            if n0 == n1:
                rects.append((n0, a0, b0, a1, b1))
    return rects


# ------------------------------------------------------------------
# 確率的スケジューラ
#   直前に走ったプロセスが続けて走れるなら確率 1-ε で続け、
#   ε で他の走れるプロセスへ(一様に)切り換える。
# ------------------------------------------------------------------
def scheduled_distribution(procs, eps, observe):
    """実実行の木を確率つきで辿り、observe(Result) の分布を Fraction/float で返す。"""
    P = len(procs)
    dist = defaultdict(float)

    def rec(inputs, seq, cur_state, last_own_pos, prob):
        stats = [procs[q].replay(inputs[q]) for q in range(P)]
        movable = []
        for q in range(P):
            st, us, out, kinds = stats[q]
            if st == "done":
                continue
            m = len(inputs[q])
            if kinds[m] == "wlock":
                lp = last_own_pos[q]
                start = 0 if lp is None else lp + 1
                if not any(seq[i][0] != q for i in range(start, len(seq))):
                    continue
            movable.append(q)
        if not movable:
            unfinished = any(stats[q][0] != "done" for q in range(P))
            key = "DEADLOCK" if unfinished else observe(tuple(s[2] for s in stats), cur_state)
            dist[key] += prob
            return
        last = seq[-1][0] if seq else None
        for q in movable:
            if last is None:
                pq = 1.0 / len(movable)
            elif last in movable:
                if len(movable) == 1:
                    pq = 1.0
                elif q == last:
                    pq = 1 - eps
                else:
                    pq = eps / (len(movable) - 1)
            else:
                pq = 1.0 / len(movable)
            if pq == 0:
                continue
            m = len(inputs[q])
            new_inputs = list(inputs)
            new_inputs[q] = inputs[q] + (cur_state,)
            st, us, out, kinds = procs[q].replay(new_inputs[q])
            lop = list(last_own_pos)
            lop[q] = len(seq)
            rec(tuple(new_inputs), seq + [(q, m)], us[m], tuple(lop), prob * pq)

    rec(tuple(() for _ in range(P)), [], EMPTY, tuple(None for _ in range(P)), 1.0)
    return dict(dist)


# ------------------------------------------------------------------
# 時間ループと虚数
#   CS が「n 回後の自分の出力」を入力として読む(超虚実行)。
#   自己無撞着な状態 = f^n の不動点。
#   f(x) = (x + t)/(1 - t x)  (t = tan θ) は tan の加法定理 = 角 θ の回転。
# ------------------------------------------------------------------
def mobius_rot(theta):
    c, s = math.cos(theta), math.sin(theta)
    return (c, s, -s, c)   # (a, b, c, d) : x -> (a x + b)/(c x + d) = (x + tanθ)/(1 - x tanθ)


def mobius_compose(M, N):
    a, b, c, d = M
    e, f, g, h = N
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)


def mobius_power(M, n):
    R = (1.0, 0.0, 0.0, 1.0)
    for _ in range(n):
        R = mobius_compose(M, R)
    return R


def mobius_fixed_points(M, tol=1e-9):
    """(a x + b)/(c x + d) = x  ⇔  c x^2 + (d - a) x - b = 0。"""
    a, b, c, d = M
    if abs(c) < tol:
        if abs(d - a) < tol:
            return "all" if abs(b) < tol else []
        return [b / (d - a)]
    disc = cmath.sqrt((d - a) ** 2 + 4 * b * c)
    return [((a - d) + disc) / (2 * c), ((a - d) - disc) / (2 * c)]


def mobius_apply(M, x):
    a, b, c, d = M
    den = c * x + d
    if den == 0:
        return math.inf
    return (a * x + b) / den


# ------------------------------------------------------------------
# 自己無撞着性による実行の決まり方(§5.5)
#   プロセスには局所変数があるので、CS (q,m) の出力は q の 0..m 番目の lock で
#   受け取った状態すべてに依存する。依存関係は rf ∪ po。
#   rf ∪ po が循環しなければ前から計算でき、循環すれば「一周して整合する」ものだけが存在する。
# ------------------------------------------------------------------
def cs_nodes(Ls):
    return [(q, m) for q, L in enumerate(Ls) for m in range(L)]


def all_rf(Ls):
    """各 CS が「自分の直前(m=0 なら ⊥)」か「他プロセスの任意の CS」を読む rf をすべて作る(循環も含む)。"""
    nodes = cs_nodes(Ls)
    cands = []
    for (q, m) in nodes:
        own = (q, m - 1) if m > 0 else INIT
        cands.append([own] + [u for u in nodes if u[0] != q])
    for choice in itertools.product(*cands):
        yield dict(zip(nodes, choice))


def _acyclic(edges, nodes):
    succ = {n: [] for n in nodes}
    for a, b in edges:
        succ[a].append(b)
    color = {}

    def dfs(u):
        color[u] = 1
        for w in succ[u]:
            if color.get(w) == 1 or (w not in color and not dfs(w)):
                return False
        color[u] = 2
        return True
    return all(dfs(n) for n in nodes if n not in color)


def dep_level(rf, Ls):
    """'I' : rf ∪ po が非巡回(I 以下), 'B' : rf だけ非巡回, 'L' : rf が循環。"""
    nodes = cs_nodes(Ls)
    rf_e = [(p, v) for v, p in rf.items() if p != INIT]
    po_e = [((q, m - 1), (q, m)) for (q, m) in nodes if m > 0]
    if _acyclic(rf_e + po_e, nodes):
        return "I"
    return "B" if _acyclic(rf_e, nodes) else "L"


def is_consistent(procs, rf, Ls, inputs, init=EMPTY, eq=None):
    """各 CS が受け取る状態の組 inputs ({CS: 状態}) が rf の下で自己無撞着かを調べる。

    ELDE と同じ再生(replay)で各 CS の unlock 状態を計算し、
    「(q,m) が受け取った状態 = rf(q,m) が置いた状態(⊥ なら init)」がすべての CS で成り立つかを返す。
    eq は状態の比較(既定は ==。浮動小数点の状態なら誤差を許す比較を渡す)。"""
    if eq is None:
        eq = lambda a, b: a == b
    outs = {}
    for q, L in enumerate(Ls):
        st, us, out, _ = procs[q].replay(tuple(inputs[(q, m)] for m in range(L)))
        for m in range(L):
            outs[(q, m)] = us[m]
    return all(eq(inputs[v], init if rf[v] == INIT else outs[rf[v]]) for v in cs_nodes(Ls))


def consistent_executions(procs, rf, Ls, domain, init=EMPTY):
    """rf の下で自己無撞着な実行を、状態の候補 domain(有限)から総当りですべて探す。

    返り値: [{CS: 受け取った状態}] のリスト。状態が連続量のときは総当りできないので、
    候補を別の方法(方程式を解くなど)で作って is_consistent で確かめる。"""
    nodes = cs_nodes(Ls)
    sols = []
    for assign in itertools.product(domain, repeat=len(nodes)):
        inp = dict(zip(nodes, assign))
        if is_consistent(procs, rf, Ls, inp, init):
            sols.append(inp)
    return sols
