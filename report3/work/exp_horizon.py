# §4 の補強: 地平(T)の格子で、x = 0 との差(対にした差)の平均と標準誤差
import sys, time, statistics, math
sys.path.insert(0, '.')
from kj_loop import NK, copy_discard_search, surviving_lineages
t0 = time.time()
xs = [0.0, 0.05, 0.2, 1.0]; Ts = [10, 30, 100, 300, 1000]; L = 60
for T in Ts:
    diffs = {x: [] for x in xs[1:]}
    for s in range(L):
        land = NK(64, 4, s)
        base = copy_discard_search(land, 20, T, 0.0, 1000 + s)[0]
        for x in xs[1:]:
            diffs[x].append(copy_discard_search(land, 20, T, x, 1000 + s)[0] - base)
    row = []
    for x in xs[1:]:
        m = statistics.mean(diffs[x]); se = statistics.stdev(diffs[x]) / math.sqrt(L)
        row.append(f"x={x}: {m*1000:+.1f}±{se*1000:.1f}")
    print(f"T={T:5d}: " + "  ".join(row), flush=True)
print(f"({time.time()-t0:.0f}s)")
