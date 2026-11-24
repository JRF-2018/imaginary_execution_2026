import sys, statistics, math
sys.path.insert(0, '.')
from kj_loop import NK, copy_discard_search, surviving_lineages

class Flat:
    def __init__(self, N): self.N = N
    def fitness(self, s): return 0.0

def predicted(n0, p, t):
    return 1.0 / (1.0 - (1.0 - 1.0 / n0) * math.exp(-p * t / 2.0))

K = 20; T = 400
for x in [0.05, 0.2]:
    p = (2 * x - x * x) / K
    for name, mk in [("中立(平らな景観)", lambda s: Flat(64)), ("NK 景観", lambda s: NK(64, 4, s))]:
        runs = []
        for s in range(40):
            _, hist, _ = copy_discard_search(mk(s), K, T, x, 50 + s)
            lin = surviving_lineages(hist, K)       # lin[t] = 時刻 t に生きている祖先の数
            runs.append(lin)
        for lag in [10, 50, 100, 200, 400]:
            m = statistics.mean(r[T - lag] for r in runs)
            print(f"x={x} {name}: {lag} 時刻さかのぼると系統 {m:5.2f}  (中立の予測 {predicted(K, p, lag):5.2f})")
