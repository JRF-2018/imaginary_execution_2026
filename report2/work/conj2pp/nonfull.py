# 定理 K の確認: 「満ちていない」(ある w について、w を書いて手を引いたときの結果の集合が S 全体でない)
# プロセスの組は必ず区別できるか。また、満ちたプロセスはどれくらいあるか。
import sys, itertools, random, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import segs, dist_kill

def suffixes(P, nS):
    s = segs(P, nS); L = len(P)
    return [s[(j, L)] for j in range(L + 1)]

def full(P, nS):
    """どの w についても {s_j(w) : j = 0..L} = S なら True(満ちている)。"""
    sf = suffixes(P, nS)
    return all(len({f[w] for f in sf}) == nS for w in range(nS))

def thmK_applies(A, B, nS):
    LA, LB = len(A), len(B)
    if LA > LB: return not full(B, nS)
    if LA < LB: return not full(A, nS)
    t0 = next(t for t in range(LA) if A[t] != B[t])
    f, g = A[t0], B[t0]
    ok = False
    for b in range(nS):
        if f[b] != g[b]:
            if f[b] != b and not full(B, nS): ok = True
            if g[b] != b and not full(A, nS): ok = True
    return ok

if __name__ == "__main__":
    for nS, Lmax in [(2, 3), (3, 3), (4, 3)]:
        F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
        for L in range(Lmax + 1):
            tot = len(F) ** L
            if tot > 300000:
                rng = random.Random(0); sample = [tuple(rng.choice(F) for _ in range(L)) for _ in range(100000)]
            else:
                sample = list(itertools.product(F, repeat=L))
            nf = sum(full(P, nS) for P in sample)
            print(f"|S|={nS} CS {L} 個: 満ちている割合 {nf}/{len(sample)}", flush=True)
    rng = random.Random(1); bad = 0; app = 0; tot = 0
    for nS, Lmax, N in [(3, 4, 5000), (4, 5, 2000), (5, 4, 500)]:
        F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
        for _ in range(N):
            La = rng.randint(1, Lmax); A = [rng.choice(F) for _ in range(La)]; B = A[:]
            B[rng.randrange(La)] = rng.choice(F)
            if rng.random() < 0.3 and len(B) > 1: B.pop(rng.randrange(len(B)))
            if A == B: continue
            tot += 1
            if thmK_applies(tuple(A), tuple(B), nS):
                app += 1
                if dist_kill(tuple(A), tuple(B), nS) is None: bad += 1; print("反例?", A, B)
    print(f"定理 K が当てはまる組 {app}/{tot}、そのうち区別できなかったもの {bad}")
