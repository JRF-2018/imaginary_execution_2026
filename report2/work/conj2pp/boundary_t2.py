# 尾が満ちていない場合: v0 = 尾で出ない値、w0 = その w。どの探り・動かす値で失敗するか、失敗の場所はどこか
import sys, itertools, random, pickle
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from kj_comp import suffix_maps, killer
from boundary_study import probes
from lockstep import belief_step
from killchar import segs
from collections import Counter

def where_fail(P, X, nS, ys, v, init=0):
    sX = segs(X, nS); M = len(X); L = len(P)
    xs = [init] + [P[t][ys[t]] for t in range(L)]
    B = frozenset(j for j in range(M + 1) if sX[(0, j)][init] == init)
    for x in range(nS):
        if x != init:
            side = frozenset(j for j in range(M + 1) if sX[(0, j)][init] == x)
            if side and killer(X, nS, side, v) is None: return ("read1", side)
    for t in range(L):
        for x in range(nS):
            if x != xs[t + 1]:
                side = belief_step(sX, M, B, ys[t], x)
                if side and killer(X, nS, side, v) is None:
                    return (("T2" if (t == 0 and x == ys[0]) else f"read{t+2}" + ("=y" if x == ys[t] else "")), side)
        B = belief_step(sX, M, B, ys[t], xs[t + 1])
    if any(sX[(j, M)][v] == v for j in B): return ("final", B)
    return None

if __name__ == '__main__':
    n = int(sys.argv[1]); N = int(sys.argv[2]); rng = random.Random(9)
    fulls = pickle.load(open(f"conj2pp/full_n{n}.pkl", "rb"))
    F = [f for f in itertools.product(range(n), repeat=n) if f != tuple(range(n))]
    st = Counter(); ex = []
    for _ in range(N):
        X = rng.choice(fulls); P = list(X); P[rng.randrange(n)] = rng.choice(F)
        if rng.random() < 0.3: P = list(rng.choice(fulls))
        P = tuple(P)
        pr = probes(P, X, n)
        if P == X or not pr: continue
        sX = suffix_maps(X, n)
        tnf = [(v, w) for v in range(n) for w in range(n) if all(s[w] != v for s in sX[1:])]
        if not tnf: continue
        movers = [[y for y in range(n) if P[t][y] != y] for t in range(n)]
        for (t0, b) in pr:
            for ys in itertools.product(*[movers[t] if t != t0 else [b] for t in range(n)]):
                for v in {v for v, _ in tnf}:
                    r = where_fail(P, X, n, ys, v)
                    st[r[0] if r else "ok"] += 1
                    if r and r[0] != "T2" and len(ex) < 3: ex.append((P, X, ys, v, r))
    print(n, dict(st)); print(ex)
