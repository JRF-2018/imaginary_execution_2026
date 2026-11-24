# 切り換わる地平 T* は、独立な山登りが局所的な山頂に着くまでの時間に比例するか
import sys, time, statistics, math, random
sys.path.insert(0, '.')
from kj_loop import NK, copy_discard_search

def climb_time(land, seed, Tmax=5000):
    """x=0 の一つの世界が、どの 1 ビットの変更でも良くならない状態に初めて着く時刻。"""
    rng = random.Random(seed); N = land.N
    w = [rng.randrange(2) for _ in range(N)]; f = land.fitness(w)
    def local_opt(w, f):
        for j in range(N):
            w[j] ^= 1; g = land.fitness(w); w[j] ^= 1
            if g > f: return False
        return True
    for t in range(Tmax):
        if t % 5 == 0 and local_opt(w, f): return t
        j = rng.randrange(N); w2 = w[:]; w2[j] ^= 1; g = land.fitness(w2)
        if g >= f: w, f = w2, g
    return Tmax

def crossover(N, Ts, L=30):
    out = []
    for T in Ts:
        d = []
        for s in range(L):
            land = NK(N, 4, s)
            d.append(copy_discard_search(land, 20, T, 1.0, 1000 + s)[0] - copy_discard_search(land, 20, T, 0.0, 1000 + s)[0])
        out.append(statistics.mean(d))
    # 符号が + から − に変わるところを線形補間(log T で)
    for (T1, d1), (T2, d2) in zip(zip(Ts, out), zip(Ts[1:], out[1:])):
        if d1 > 0 >= d2:
            a = math.log(T1) + (math.log(T2) - math.log(T1)) * d1 / (d1 - d2)
            return math.exp(a), out
    return None, out

t0 = time.time()
for N in [24, 48, 96]:
    ct = statistics.mean(climb_time(NK(N, 4, s), 7 + s) for s in range(30))
    Ts = [int(N * f) for f in (0.5, 1, 2, 4, 8, 16)]
    Tstar, out = crossover(N, Ts)
    print(f"N={N}: 山頂までの平均時間 {ct:.0f}(N ln N = {N*math.log(N):.0f}),  切り換わる地平 T* ≈ {Tstar and round(Tstar)}  "
          f"[x=1 − x=0 (×1000): " + ", ".join(f"T={T}:{d*1000:+.0f}" for T, d in zip(Ts, out)) + "]", flush=True)
print(f"({time.time()-t0:.0f}s)")
