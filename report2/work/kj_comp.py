# -*- coding: utf-8 -*-
"""kj_comp.py -- 「部品の意味と計算量」(report2)の計算コア。

* CS 単位のプロセス(各 CS は状態から状態への関数。記憶のあるプロセスは、それまでに読んだ値すべてに依存する表)
* 並列合成の結果(すべてのインタリーブの最終状態の集合)と、文脈同値
* スレッド・モジュラー検査(Flanagan & Qadeer 2003 の考え方)と、全状態探索の比較
* 一度しか再開できない継続(Python のジェネレータ)と再実行による、何度でも再開できる継続
"""
from __future__ import annotations
import itertools
import random
import time
from collections import defaultdict, deque


# ------------------------------------------------------------------
# CS 単位のプロセスと並列合成
#   記憶のないプロセス: CS の関数の列。関数 S→S は値の組 (f(0), f(1), ...) で表す。
#   記憶のあるプロセス: m 番目の CS の出力が、そのプロセスが 0..m 番目に読んだ値すべてに依存する表。
# ------------------------------------------------------------------
def functions(nS):
    return list(itertools.product(range(nS), repeat=nS))


def finals(P, Q, init=0, memP=False, memQ=False, nS=None):
    """P と Q のすべてのインタリーブ(CS 単位)を実行し、最終状態の集合を返す。"""
    res = set()

    def step(proc, mem, k, s, hist):
        if not mem:
            return proc[k][s]
        idx = 0
        for v in hist + (s,):
            idx = idx * nS + v
        return proc[k][idx]

    def rec(i, j, s, hp, hq):
        if i == len(P) and j == len(Q):
            res.add(s)
            return
        if i < len(P):
            rec(i + 1, j, step(P, memP, i, s, hp), hp + (s,), hq)
        if j < len(Q):
            rec(i, j + 1, step(Q, memQ, j, s, hq), hp, hq + (s,))
    rec(0, 0, init, (), ())
    return frozenset(res)


def compose(P, nS):
    """記憶のないプロセスを、途中で邪魔されずに走らせたときの全体の関数(実実行だけの意味)。"""
    out = []
    for s in range(nS):
        for f in P:
            s = f[s]
        out.append(s)
    return tuple(out)


def memory_contexts(nS, L):
    """長さ L の記憶のある文脈をすべて作る。"""
    tabs = [list(itertools.product(range(nS), repeat=nS ** (m + 1))) for m in range(L)]
    return list(itertools.product(*tabs))


def context_classes(procs, contexts, nS, memQ=False):
    """文脈ごとの観測(最終状態の集合)の組で、プロセスを類に分ける。"""
    sig = {P: tuple(finals(P, Q, memQ=memQ, nS=nS) for Q in contexts) for P in procs}
    return sig


def refines(procs, key, sig):
    """key が同じなら文脈同値か(合成的・健全)、文脈同値なら key が同じか(完全)。"""
    by_key, by_sig = defaultdict(set), defaultdict(set)
    for P in procs:
        by_key[key(P)].add(sig[P])
        by_sig[sig[P]].add(key(P))
    return all(len(v) == 1 for v in by_key.values()), all(len(v) == 1 for v in by_sig.values())


# ------------------------------------------------------------------
# スレッド・モジュラー検査
#   スレッド i の局所状態 l、共有状態 g。遷移 step_i(l, g) -> [(l', g')]。
#   全状態探索: 大域状態 (l_0, ..., l_{N-1}, g) をすべてたどる。
#   スレッド・モジュラー: 各スレッドについて (l, g) の集合 R_i を、自分の遷移と、
#   他のスレッドが起こしうる共有状態の変化 g -> g'(保証 G_j)で閉じるまで広げる。
# ------------------------------------------------------------------
def explore_global(N, init_local, init_shared, step):
    start = (tuple(init_local for _ in range(N)), init_shared)
    seen = {start}
    dq = deque([start])
    while dq:
        ls, g = dq.popleft()
        for i in range(N):
            for l2, g2 in step(i, ls[i], g):
                st = (ls[:i] + (l2,) + ls[i + 1:], g2)
                if st not in seen:
                    seen.add(st)
                    dq.append(st)
    return seen


def explore_modular(N, init_local, init_shared, step):
    R = [{(init_local, init_shared)} for _ in range(N)]
    G = [set() for _ in range(N)]          # スレッド j が起こしうる共有状態の変化
    changed = True
    work = 0
    while changed:
        changed = False
        for i in range(N):
            new = set()
            for (l, g) in R[i]:
                for l2, g2 in step(i, l, g):
                    work += 1
                    new.add((l2, g2))
                    if g2 != g and (g, g2) not in G[i]:
                        G[i].add((g, g2)); changed = True
            for j in range(N):             # 他のスレッドによる共有状態の変化(虚の入力)
                if j == i:
                    continue
                for (l, g) in R[i]:
                    for (ga, gb) in G[j]:
                        if ga == g:
                            work += 1
                            new.add((l, gb))
            if not new <= R[i]:
                R[i] |= new; changed = True
    return R, G, work


# ------------------------------------------------------------------
# 継続: 一度しか再開できない継続(ジェネレータ)を、最初から再実行することで何度でも再開する
#   プログラムはジェネレータで、 x = yield ("callcc",) で「現在の継続」を受け取る。
#   受け取った値が ("right", k) のとき、後で yield ("throw", k, v) すると、
#   その callcc の時点に戻って ("left", v) を受け取ったかのように、最初から再実行する。
# ------------------------------------------------------------------
class Jump(Exception):
    pass


def run_with_callcc(program, max_worlds=50):
    """世界(再実行)の列と、各世界の結果を返す。"""
    answers = {}            # callcc の番号 -> 与える値
    worlds = []
    for _ in range(max_worlds):
        g = program()
        log = []
        n_callcc = 0
        try:
            req = next(g)
            while True:
                if req[0] == "callcc":
                    k = n_callcc
                    n_callcc += 1
                    val = answers.get(k, ("right", k))
                    log.append(f"callcc#{k} → {val[0]}")
                    req = g.send(val)
                elif req[0] == "throw":
                    _, k, v = req
                    log.append(f"継続#{k} を値 {v!r} で再開(この世界は捨てる)")
                    answers[k] = ("left", v)
                    answers = {kk: vv for kk, vv in answers.items() if kk <= k}
                    raise Jump()
                else:
                    raise ValueError(req)
        except StopIteration as e:
            worlds.append((log, e.value))
            return worlds
        except Jump:
            worlds.append((log, None))
    raise RuntimeError("too many worlds")


# ------------------------------------------------------------------
# 大きめの場合の文脈同値の類の数(numpy で全プロセスをまとめて計算する)
#   controlled=True : 検査者がスケジュールを選ぶ(ELDE の lock 仕様)。観測は各スケジュールの最終状態。
#   controlled=False: スケジュールは選べない。観測は全スケジュールの最終状態の集合。
#   相手 Q の関数を L+1 個の連続ブロックに分ける切り方が、スケジュールに対応する(定理 H の分解の補題)。
# ------------------------------------------------------------------
def count_classes_np(nS, L, ctx_lens, controlled, sample=None, seed=0):
    import numpy as np
    import random
    F = np.array(list(itertools.product(range(nS), repeat=nS)))
    ID = np.arange(nS)
    P = np.array(list(itertools.product(range(len(F)), repeat=L)))
    nP = len(P)
    fs = [F[P[:, k]] for k in range(L)]
    idx = np.arange(nP)
    rng = random.Random(seed)

    def comp(qs):
        r = ID.copy()
        for q in qs:
            r = q[r]
        return r
    sig = np.zeros(nP, dtype=np.uint64)
    out = []
    for m in ctx_lens:
        if sample is None or len(F) ** m <= sample:
            Qs = itertools.product(range(len(F)), repeat=m)
            nq = len(F) ** m
        else:
            Qs = [tuple(rng.randrange(len(F)) for _ in range(m)) for _ in range(sample)]
            nq = sample
        for Q in Qs:
            qf = [F[i] for i in Q]
            mask = np.zeros(nP, dtype=np.uint64)
            for cuts in itertools.combinations_with_replacement(range(m + 1), L):
                cut = (0,) + cuts + (m,)
                hs = [comp(qf[cut[j]:cut[j + 1]]) for j in range(L + 1)]
                x = np.full(nP, hs[0][0])
                for k in range(L):
                    x = hs[k + 1][fs[k][idx, x]]
                if controlled:
                    sig = sig * np.uint64(1000003) + x.astype(np.uint64) + np.uint64(1)
                else:
                    mask |= (np.uint64(1) << x.astype(np.uint64))
            if not controlled:
                sig = sig * np.uint64(1000003) + mask
        out.append((m, nq, len(np.unique(sig))))
    return out


def interference_classes_np(nS, L):
    """割り込みの意味(各 CS の前に任意の関数を一つずつ割り込ませた実行)で同値な類の数。"""
    import numpy as np
    F = np.array(list(itertools.product(range(nS), repeat=nS)))
    P = np.array(list(itertools.product(range(len(F)), repeat=L)))
    nP = len(P)
    fs = [F[P[:, k]] for k in range(L)]
    idx = np.arange(nP)
    sig = np.zeros(nP, dtype=np.uint64)
    for hs in itertools.product(range(len(F)), repeat=L - 1):
        for x0 in range(nS):
            x = fs[0][idx, np.full(nP, x0)]
            for k in range(1, L):
                x = fs[k][idx, F[hs[k - 1]][x]]
            sig = sig * np.uint64(1000003) + x.astype(np.uint64) + np.uint64(1)
    return len(np.unique(sig))


# ------------------------------------------------------------------
# 記憶のある相手に対する観測を、全プロセスについてまとめて計算する(予想 2′ の検証用)
#   相手から見ると、P の CS は連続したブロック A_0, …, A_T として相手の CS の間に入る。
#   x_1 = A_0(init), y_t = Q_t(x_1..x_t), x_{t+1} = A_t(y_t), 最終状態 = A_T(y_T)。
# ------------------------------------------------------------------
class MemObs:
    def __init__(self, nS, L, procs=None, init=0):
        import numpy as np
        self.np = np
        self.nS, self.L, self.init = nS, L, init
        self.F = np.array(list(itertools.product(range(nS), repeat=nS)))
        if procs is None:
            procs = list(itertools.product(range(len(self.F)), repeat=L))
        self.P = np.array(procs)
        nP = len(self.P)
        self.idx = np.arange(nP)
        ident = np.tile(np.arange(nS), (nP, 1))
        self.seg = {}
        for i in range(L + 1):
            cur = ident
            self.seg[(i, i)] = cur
            for j in range(i + 1, L + 1):
                cur = self.F[self.P[:, j - 1]][self.idx[:, None], cur]
                self.seg[(i, j)] = cur

    def mask(self, Q, sub=None):
        """相手 Q(表の列)に対する観測(最終状態の集合のビット列)を、プロセスごとに返す。"""
        np = self.np
        idx = self.idx if sub is None else sub
        T, L, nS = len(Q), self.L, self.nS
        m = np.zeros(len(idx), dtype=np.int64)
        for cuts in itertools.combinations_with_replacement(range(L + 1), T):
            x = self.seg[(0, cuts[0])][idx, self.init]
            h = x.copy()
            for t in range(T):
                y = np.asarray(Q[t])[h]
                nxt = cuts[t + 1] if t + 1 < T else L
                x = self.seg[(cuts[t], nxt)][idx, y]
                h = h * nS + x
            m |= (1 << x)
        return m


# ------------------------------------------------------------------
# 予想 2′ の有限の場合の完全な検証:
#   恒等写像を消した形ごとに代表を一つとり(定理 I)、記憶のある相手で観測を比べて、
#   すべての代表が区別されるまで分割を細かくする。
# ------------------------------------------------------------------
def verify_conj2(nS, L, seed=0, budget=200000, log=print):
    import numpy as np
    F = list(itertools.product(range(nS), repeat=nS))
    ident = F.index(tuple(range(nS)))
    nonid = [i for i in range(len(F)) if i != ident]
    reps = [tuple(seq) + (ident,) * (L - len(seq))
            for n in range(L + 1) for seq in itertools.product(nonid, repeat=n)]
    mo = MemObs(nS, L, reps)
    group = np.zeros(len(reps), dtype=np.int64)
    rng = random.Random(seed)
    t0 = time.time()
    used = []
    for trial in range(budget):
        sizes = np.bincount(group)
        active = np.nonzero(sizes[group] > 1)[0]
        if len(active) == 0:
            break
        T = rng.choice([1, 2, 3, 4, 5])
        Q = [tuple(rng.randrange(nS) for _ in range(nS ** (t + 1))) for t in range(T)]
        m = mo.mask(Q, active)
        key = group[active] * (1 << nS) + m
        _, newid = np.unique(key, return_inverse=True)
        before = len(np.unique(group))
        g2 = group.copy()
        g2[active] = newid + group.max() + 1
        _, group = np.unique(g2, return_inverse=True)
        if len(np.unique(group)) > before:
            used.append(Q)
        if trial % 2000 == 0:
            log(f"  試行 {trial}: 類 {len(np.unique(group))} / {len(reps)}  ({time.time() - t0:.0f} 秒)")
    n = len(np.unique(group))
    log(f"|S|={nS}, CS {L} 個以下: 代表 {len(reps)} 個、区別された類 {n}、"
        f"役に立った相手 {len(used)} 個、{time.time() - t0:.0f} 秒")
    return n == len(reps), used


# ------------------------------------------------------------------
# 記憶のある相手で二つのプロセスを区別できるかの厳密な判定(予想 2′ の反例の確認用)
#   相手の一回の手番 = 状態を読み、書く。相手から見た知識は (読んだ値, P がどこまで進んだかの可能性の集合,
#   P' の同じ集合) に尽きる。相手が勝つ = ある値 v を、P のあるスケジュールは出し、P' のどのスケジュールも
#   出さない(または逆)。相手の長さは max(L, L') + 1 で足りる(記憶版の分割の補題)ので、有限の判定になる。
# ------------------------------------------------------------------
def distinguishable(A, B, nS, init=0, extra_depth=0):
    """記憶のある相手で A と B を区別できれば (v, 向き) を、できなければ None を返す。

    A, B は関数(値の組)の列。"""
    from functools import lru_cache

    def segs(P):
        L = len(P)
        seg = {}
        for i in range(L + 1):
            cur = tuple(range(nS))
            seg[(i, i)] = cur
            for j in range(i + 1, L + 1):
                cur = tuple(P[j - 1][c] for c in cur)
                seg[(i, j)] = cur
        return seg

    sa, sb = segs(A), segs(B)
    La, Lb = len(A), len(B)
    depth0 = max(La, Lb) + 1 + extra_depth

    def advance(seg, L, belief, y):
        """値 y を書いた後、P が 0 歩以上進んでから読まれる値ごとの、新しい位置の集合。"""
        out = {}
        for i in belief:
            for j in range(i, L + 1):
                out.setdefault(seg[(i, j)][y], set()).add(j)
        return out

    for v in range(nS):
        for (sP, LP, sQ, LQ) in [(sa, La, sb, Lb), (sb, Lb, sa, La)]:
            @lru_cache(maxsize=None)
            def safe(bp, bq, d):
                # bq(避けたい側)のどの分岐も v を出さないようにできるか。bp は使わない
                if not bq:
                    return True
                for y in range(nS):
                    if all(sQ[(j, LQ)][y] != v for j in bq):
                        return True                     # ここで止める
                    if d > 0:
                        ch = advance(sQ, LQ, bq, y)
                        if all(safe(frozenset(), frozenset(s), d - 1) for s in ch.values()):
                            return True
                return False

            @lru_cache(maxsize=None)
            def good(bp, bq, d):
                # bp(出させたい側)のある分岐で v を出し、bq のどの分岐も v を出さないようにできるか
                if not bp:
                    return False
                for y in range(nS):
                    if any(sP[(i, LP)][y] == v for i in bp) and all(sQ[(j, LQ)][y] != v for j in bq):
                        return True
                    if d > 0:
                        cp, cq = advance(sP, LP, bp, y), advance(sQ, LQ, bq, y)
                        keys = set(cp) | set(cq)
                        kids = {x: (frozenset(cp.get(x, ())), frozenset(cq.get(x, ()))) for x in keys}
                        if all(safe(frozenset(), q, d - 1) for p, q in kids.values()) and \
                                any(good(p, q, d - 1) for p, q in kids.values()):
                            return True
                return False

            # 相手がいない場合
            if sP[(0, LP)][init] == v and sQ[(0, LQ)][init] != v:
                return (v, "相手なし")
            # 最初の手番の前に、P が 0 歩以上進んでいる
            cp, cq = advance(sP, LP, {0}, init), advance(sQ, LQ, {0}, init)
            kids = {x: (frozenset(cp.get(x, ())), frozenset(cq.get(x, ()))) for x in set(cp) | set(cq)}
            if all(safe(frozenset(), q, depth0 - 1) for p, q in kids.values()) and \
                    any(good(p, q, depth0 - 1) for p, q in kids.values()):
                return (v, "A が出し B が出さない" if sP is sa else "B が出し A が出さない")
    return None


# ------------------------------------------------------------------
# 潰す一手と定理 K(予想 2″ の CS ≦ |S|−1 の部分)
#   接尾写像 s_j = f_L ∘ … ∘ f_{j+1}: 位置 j から邪魔されずに最後まで走ったときの効果(s_L = id)。
#   位置の集合 B が v について「潰せる」: ある w について、どの j ∈ B でも s_j(w) ≠ v。
#   プロセスが「満ちている」: どの w についても {s_0(w), …, s_L(w)} = S。
# ------------------------------------------------------------------
def suffix_maps(P, nS):
    out = [tuple(range(nS))]
    for f in reversed(P):
        s = out[0]
        out.insert(0, tuple(s[f[x]] for x in range(nS)))
    return out


def prefix_maps(P, nS):
    out = [tuple(range(nS))]
    for f in P:
        p = out[-1]
        out.append(tuple(f[p[x]] for x in range(nS)))
    return out


def killer(P, nS, B, v):
    """B を v について潰す値 w(なければ None)。"""
    sf = suffix_maps(P, nS)
    for w in range(nS):
        if all(sf[j][w] != v for j in B):
            return w
    return None


def is_full(P, nS):
    sf = suffix_maps(P, nS)
    return all(len({s[w] for s in sf}) == nS for w in range(nS))


def run_with_partner(P, partner, T, init=0):
    """記憶のない P と、読んだ値の履歴から書く値を決める相手(T 手)の、すべてのインタリーブの最終状態の集合。"""
    out = set()

    def rec(i, t, s, hist):
        if i == len(P) and t == T:
            out.add(s)
            return
        if i < len(P):
            rec(i + 1, t, P[i][s], hist)
        if t < T:
            h = hist + (s,)
            rec(i, t + 1, partner(h), h)
    rec(0, 0, init, ())
    return frozenset(out)


def separating_partner(A, B, nS, init=0):
    """定理 K の証明どおりの相手を作る。返り値: (出す側, 避ける側, 相手, 手数, v)。
    A, B は恒等写像を含まない異なるプロセスで、避ける側が「満ちていない」か CS が nS−1 個であること。"""
    LA, LB = len(A), len(B)
    probe = None
    if LA != LB:
        P, X = (A, B) if LA > LB else (B, A)
    else:
        t0 = next(t for t in range(LA) if A[t] != B[t])
        b = next(b for b in range(nS) if A[t0][b] != B[t0][b])
        P, X = (A, B) if A[t0][b] != b else (B, A)
        probe = (t0, b)
    L, M = len(P), len(X)
    ys = [probe[1] if probe and t == probe[0] else next(y for y in range(nS) if P[t][y] != y)
          for t in range(L)]
    sX, pX = suffix_maps(X, nS), prefix_maps(X, nS)
    if not is_full(X, nS):
        v = next(v for v in range(nS) if any(all(s[w] != v for s in sX) for w in range(nS)))
    else:
        assert M == nS - 1, "定理 K の仮定の外"
        v = sX[0][init]
    expected = [init] + [P[t][ys[t]] for t in range(L)]

    def belief(h):
        Bs = {j for j in range(M + 1) if pX[j][init] == h[0]}
        for t in range(1, len(h)):
            y = ys[t - 1]
            Bs = {j for i in Bs for j in range(i, M + 1)
                  if suffix_seg(X, i, j, y) == h[t]}
        return Bs

    def partner(h):
        t = len(h) - 1
        for k in range(len(h)):
            if h[k] != expected[k]:
                if k == t:                         # いま外れた: X の信念を潰す
                    return killer(X, nS, belief(h), v)
                return h[-1]                       # 潰した後は、読んだ値を写すだけ
        return ys[t] if t < L else v
    return P, X, partner, L + 1, v


def suffix_seg(P, i, j, y):
    for f in P[i:j]:
        y = f[y]
    return y
