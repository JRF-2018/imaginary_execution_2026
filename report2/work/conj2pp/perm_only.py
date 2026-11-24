# 置換だけのプロセスでは、長くても予想 2′ が成り立つか(無作為な一か所違いの組を厳密に判定)
import itertools, random, sys, time
sys.path.insert(0, '.')
from kj_comp import distinguishable
n = int(sys.argv[1]); L = int(sys.argv[2]); N = int(sys.argv[3])
rng = random.Random(1); I = tuple(range(n))
perms = [p for p in itertools.permutations(range(n)) if p != I]
bad = 0; t0 = time.time()
for _ in range(N):
    A = [rng.choice(perms) for _ in range(L)]
    k = rng.randrange(L); B = A[:]
    B[k] = rng.choice([p for p in perms if p != A[k]])
    if rng.random() < 0.3:     # 長さの違う組も
        B.pop(rng.randrange(L))
    if not distinguishable(tuple(A), tuple(B), n):
        bad += 1
        if bad <= 3: print("区別できない:", A, B)
print(f"n={n} L={L}: {N} 組中 区別できない {bad} ({time.time()-t0:.0f}s)")
