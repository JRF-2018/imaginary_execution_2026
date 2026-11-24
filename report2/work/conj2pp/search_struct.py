# 予想 2″ の調査: |S|=n で「定数 c0 → 置換 → (0 で一致する二つ) → 置換」型の反例を探す
import itertools, random, sys, time
sys.path.insert(0, '.')
from kj_comp import distinguishable
n = int(sys.argv[1]); L = int(sys.argv[2]); N = int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = random.Random(seed)
perms = [p for p in itertools.permutations(range(n)) if p != tuple(range(n))]
allf = [f for f in itertools.product(range(n), repeat=n) if f != tuple(range(n))]
c0 = (0,) * n
found = 0; t0 = time.time()
for trial in range(N):
    k = L - 2           # 差の位置(0 始まり)。前は c0 と置換、後ろは置換一つ
    pre = [c0] + [rng.choice(perms) for _ in range(k - 1)]
    x = 0
    for f in pre: x = f[x]
    pool = perms if rng.random() < 0.5 else allf
    s = rng.choice(pool)
    cand = [g for g in pool if g[x] == s[x] and g != s]
    if not cand: continue
    t = rng.choice(cand)
    post = [rng.choice(perms)]
    A, B = tuple(pre + [s] + post), tuple(pre + [t] + post)
    if not distinguishable(A, B, n):
        found += 1
        if found <= 5: print("区別できない:", A, B, flush=True)
print(f"n={n} L={L}: {N} 組中 区別できない {found} ({time.time()-t0:.0f}s)")
