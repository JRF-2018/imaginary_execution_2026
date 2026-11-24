# -*- coding: utf-8 -*-
"""予想 2(記憶のある相手、スケジュールを選べない観測)の探索。ノートの外で回した計算(約 1〜2 時間)。

結果(2026-11-24):
  |S|=3, CS 2 個: 記憶のある相手 長さ 1(全 27)→310, 長さ 2(20000 個)→617, 長さ 3(20000 個)→703 類。
                  「恒等写像を消して一致」で分けた類の数 703 にちょうど一致。
  |S|=3, CS 3 個(1353 個の部分集合、似た形の組を多く含む): 長さ 4 まで(各 3000〜4000 個)で 1310/1312、
                  残る 2 組も狙った探索で長さ 4 の相手により区別された。
  |S|=2, CS 3 個: 長さ 6 まで(各 30000 個)で 35/40。区別できない 4 組(いずれも最後が not)は、
                  長さ 3〜7 の相手 30 万個の狙った探索でも区別されなかった。
"""
import itertools, random
from collections import defaultdict
from kj_comp import finals, functions, memory_contexts


def erase(P, nS):
    idf = tuple(range(nS))
    return tuple(f for f in P if f != idf)


def run(nS, LP, lens, samp, seed=11):
    F = functions(nS)
    procs = list(itertools.product(F, repeat=LP))
    sig = {P: () for P in procs}
    rng = random.Random(seed)
    for L in lens:
        tabs = [nS ** (m + 1) for m in range(L)]
        total = 1
        for t in tabs:
            total *= nS ** t
        cs = memory_contexts(nS, L) if total <= samp else \
            [tuple(tuple(rng.randrange(nS) for _ in range(t)) for t in tabs) for _ in range(samp)]
        for P in procs:
            sig[P] += tuple(finals(P, Q, memQ=True, nS=nS) for Q in cs)
        print(nS, LP, L, len(cs), len(set(sig.values())), len({erase(P, nS) for P in procs}), flush=True)
    return sig


if __name__ == "__main__":
    run(3, 2, (1, 2, 3), 20000)
    run(2, 3, (1, 2, 3, 4, 5, 6), 30000)
