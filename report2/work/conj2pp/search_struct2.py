# 予想 2″ の調査(2): 前半の置換を「0 を動かさない置換」に寄せた形も含めて探す
import itertools, random, sys, time
sys.path.insert(0, '.')
from kj_comp import distinguishable
n = int(sys.argv[1]); L = int(sys.argv[2]); N = int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = random.Random(seed)
I = tuple(range(n))
perms = [p for p in itertools.permutations(range(n)) if p != I]
fix0 = [p for p in perms if p[0] == 0]
allf = [f for f in itertools.product(range(n), repeat=n) if f != I]
consts = [(c,) * n for c in range(n)]
pools = {"perm": perms, "fix0": fix0, "all": allf, "const": consts}
found = 0; t0 = time.time(); kinds = {}
for trial in range(N):
    k = rng.randrange(0, L)              # 差の位置
    pre = []
    for i in range(k):
        pool = pools[rng.choice(["perm", "fix0", "fix0", "all", "const"] if i else ["const", "const", "perm", "all"])]
        pre.append(rng.choice(pool))
    x = 0
    for f in pre: x = f[x]
    pool = pools[rng.choice(["perm", "all"])]
    s = rng.choice(pool)
    cand = [g for g in pool if g[x] == s[x] and g != s]
    if not cand: continue
    t = rng.choice(cand)
    post = [rng.choice(pools[rng.choice(["perm", "all"])]) for _ in range(L - k - 1)]
    A, B = tuple(pre + [s] + post), tuple(pre + [t] + post)
    if not distinguishable(A, B, n):
        found += 1
        if found <= 8: print("区別できない:", A, B, flush=True)
print(f"n={n} L={L}: {N} 組中 区別できない {found} ({time.time()-t0:.0f}s)")
