# 境界の組で、規則 R1(P の最初の CS が初期値を動かすなら y_1 = 初期値)がどこまで効くか
import sys, itertools, random, pickle
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from kj_comp import suffix_maps
from boundary_study import probes, lock_ok
from boundary_t2 import where_fail
from collections import Counter

def classify(X, n):
    sX = suffix_maps(X, n)
    tail_full = all(len({s[w] for s in sX[1:]}) == n for w in range(n))
    return "尾が満ちている" if tail_full else "尾が満ちていない"

if __name__ == "__main__":
    n = int(sys.argv[1]); N = int(sys.argv[2]); rng = random.Random(11)
    fulls = pickle.load(open(f"conj2pp/full_n{n}.pkl", "rb"))
    F = [f for f in itertools.product(range(n), repeat=n) if f != tuple(range(n))]
    st = Counter(); fails = Counter()
    for _ in range(N):
        X = rng.choice(fulls); P = list(X); P[rng.randrange(n)] = rng.choice(F)
        if rng.random() < 0.3: P = list(rng.choice(fulls))
        P = tuple(P); pr = probes(P, X, n)
        if P == X or not pr: continue
        if P[0][0] == 0: st["f1(init)=init"] += 1; continue
        kind = classify(X, n); c = suffix_maps(X, n)[0][0]
        movers = [[y for y in range(n) if P[t][y] != y] for t in range(n)]
        ok = False; reasons = Counter()
        for (t0, b) in pr:
            if t0 == 0 and b != 0: continue
            for ys in itertools.product(*[([0] if t == 0 else movers[t]) if t != t0 else [b] for t in range(n)]):
                for v in range(n):
                    if v == c: continue
                    r = where_fail(P, X, n, ys, v)
                    if r is None: ok = True
                    else: reasons[r[0]] += 1
        st[(kind, ok)] += 1
        if not ok: fails[tuple(sorted(reasons))] += 1
    print(n, dict(st)); print(dict(fails))
