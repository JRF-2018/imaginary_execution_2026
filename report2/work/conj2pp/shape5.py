# |S|=4・CS 5 個で、見つかった反例(CS 6 個)と同じ形の組を全数で判定する
import itertools, sys, time
sys.path.insert(0, '.')
from kj_comp import distinguishable
n = 4; I = tuple(range(n)); c0 = (0,) * n
perms = [p for p in itertools.permutations(range(n)) if p != I]
fix0 = [p for p in perms if p[0] == 0]
pairs = [(s, t) for s in perms for t in perms if s < t and s[0] == t[0]]
t0 = time.time(); cnt = 0; bad = []
shapes = {"c0,π,差,ρ,ρ": lambda: ((c0, p, s, r1, r2), (c0, p, t, r1, r2)) }
for p in fix0:
    for s, t in pairs:
        for r1 in perms:
            for r2 in perms:
                A, B = (c0, p, s, r1, r2), (c0, p, t, r1, r2); cnt += 1
                if not distinguishable(A, B, n): bad.append((A, B))
print("c0,π,差,ρ,ρ:", cnt, "組、区別できない", len(bad), f"({time.time()-t0:.0f}s)", bad[:3], flush=True)
t0 = time.time(); cnt = 0; bad = []
for p in fix0:
    for q in fix0:
        for s, t in pairs:
            for r1 in perms:
                A, B = (c0, p, q, s, r1), (c0, p, q, t, r1); cnt += 1
                if not distinguishable(A, B, n): bad.append((A, B))
print("c0,π,π,差,ρ:", cnt, "組、区別できない", len(bad), f"({time.time()-t0:.0f}s)", bad[:3], flush=True)
