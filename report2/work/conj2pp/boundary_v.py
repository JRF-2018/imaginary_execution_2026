import sys, itertools, random, pickle, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from kj_comp import suffix_maps, is_full
from boundary_study import study, probes
from collections import Counter
n = int(sys.argv[1]); N = int(sys.argv[2]); rng = random.Random(5)
fulls = pickle.load(open(f"conj2pp/full_n{n}.pkl", "rb"))
F = [f for f in itertools.product(range(n), repeat=n) if f != tuple(range(n))]
st = Counter()
for _ in range(N):
    X = rng.choice(fulls); P = list(X); P[rng.randrange(n)] = rng.choice(F)
    if rng.random() < 0.3: P = list(rng.choice(fulls))
    P = tuple(P)
    if P == X or not probes(P, X, n): continue
    r = study(P, X, n)
    sX = suffix_maps(X, n)
    tail_full = all(len({s[w] for s in sX[1:]}) == n for w in range(n))
    vs = {v for (_, _, _, v) in r}
    v0 = sX[0][0]
    # 尾が満ちていない v(ある w で尾に出ない)
    tail_nf = {v for v in range(n) if any(all(s[w] != v for s in sX[1:]) for w in range(n))}
    # どの ys でも(各探りについて)効く v があるか
    allys = {}
    for (t0, b, ys, v) in r: allys.setdefault((t0, b, v), set()).add(ys)
    st["組"] += 1
    st["尾が満ちている"] += tail_full
    st["v=s0(init) で可"] += v0 in vs
    st["尾で出ない v で可(あれば)"] += bool(tail_nf & vs) if tail_nf else 0
    st["尾で出ない v がある"] += bool(tail_nf)
    st["効く v ⊆ 尾で出ない v"] += vs <= tail_nf
print(n, dict(st))
