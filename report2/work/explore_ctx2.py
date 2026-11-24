import itertools, sys
from functools import lru_cache
nS, LP, LQmax, mem = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == "mem"
S = range(nS)
FUNCS = list(itertools.product(S, repeat=nS))
def inter(a, b):
    if not a: yield b; return
    if not b: yield a; return
    for r in inter(a[1:], b): yield (("P", a[0]),) + r if False else (a[0],) + r
    for r in inter(a, b[1:]): yield (b[0],) + r
# 文脈 Q: mem なら各 CS が「Q がそれまでに読んだ値すべて」に依存する表
def ctx_list(L):
    if not mem:
        return list(itertools.product(FUNCS, repeat=L))
    out = []
    tabs = [list(itertools.product(S, repeat=nS ** (m + 1))) for m in range(L)]
    for combo in itertools.product(*tabs):
        out.append(combo)
    return out
def run(P, Q, init=0):
    res = set()
    LPn, LQn = len(P), len(Q)
    def rec(i, j, s, hist):
        if i == LPn and j == LQn: res.add(s); return
        if i < LPn: rec(i + 1, j, P[i][s], hist)
        if j < LQn:
            h = hist + (s,)
            if mem:
                idx = 0
                for v in h: idx = idx * nS + v
                rec(i, j + 1, Q[j][idx], h)
            else:
                rec(i, j + 1, Q[j][s], h)
    rec(0, 0, init, ())
    return frozenset(res)
procs = list(itertools.product(FUNCS, repeat=LP))
sig = {P: () for P in procs}
print(f"|S|={nS} LP={LP} 文脈の記憶={'あり' if mem else 'なし'}: プロセス {len(procs)}")
for L in range(0, LQmax + 1):
    cs = ctx_list(L) if L > 0 else [()]
    for P in procs:
        sig[P] = sig[P] + tuple(run(P, Q) for Q in cs)
    print(f"  文脈の CS ≤ {L} (文脈 {len(cs)} 個追加): 文脈同値の類 {len(set(sig.values()))}")
