# -*- coding: utf-8 -*-
"""予想 2′ の計算機による完全な検証(有限の場合)。

恒等写像を消した形(恒等写像のない長さ L 以下の列)ごとに代表を一つとり(定理 I により、同じ形のものは
どの相手に対しても同じ観測を出す)、記憶のある相手で観測を比べて、すべての代表が互いに区別されるまで
分割を細かくする。すべて区別されれば、その (|S|, L) で予想 2′ が成り立つ。
"""
import itertools, random, sys, time
import numpy as np
from kj_comp import MemObs


def verify(nS, L, seed=0, budget=200000, log=print):
    F = list(itertools.product(range(nS), repeat=nS))
    ident = F.index(tuple(range(nS)))
    nonid = [i for i in range(len(F)) if i != ident]
    reps = [tuple(seq) + (ident,) * (L - len(seq))
            for n in range(L + 1) for seq in itertools.product(nonid, repeat=n)]
    mo = MemObs(nS, L, reps)
    group = np.zeros(len(reps), dtype=np.int64)
    rng = random.Random(seed)
    t0 = time.time()
    used = []
    for trial in range(budget):
        sizes = np.bincount(group)
        active = np.nonzero(sizes[group] > 1)[0]
        if len(active) == 0:
            break
        T = rng.choice([1, 2, 3, 4, 5])
        Q = [tuple(rng.randrange(nS) for _ in range(nS ** (t + 1))) for t in range(T)]
        m = mo.mask(Q, active)
        key = group[active] * (1 << nS) + m
        _, newid = np.unique(key, return_inverse=True)
        before = len(np.unique(group))
        g2 = group.copy()
        g2[active] = newid + group.max() + 1
        _, group = np.unique(g2, return_inverse=True)
        if len(np.unique(group)) > before:
            used.append(Q)
        if trial % 2000 == 0:
            log(f"  試行 {trial}: 類 {len(np.unique(group))} / {len(reps)}  ({time.time() - t0:.0f} 秒)")
    n = len(np.unique(group))
    log(f"|S|={nS}, CS {L} 個以下: 代表 {len(reps)} 個、区別された類 {n}、"
        f"役に立った相手 {len(used)} 個、{time.time() - t0:.0f} 秒")
    return n == len(reps), used


if __name__ == "__main__":
    for nS, L in [(3, 2), (3, 3), (4, 2)]:
        ok, used = verify(nS, L)
        print("予想 2′ が成り立つ:", ok, flush=True)
