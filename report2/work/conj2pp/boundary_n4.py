# |S|=4・CS 4 個の境界の完全な検証: 定理 K が当てはまらない組だけを調べる。
#  (a) 両方とも満ちている組 → 記憶のある相手で分割し、残りを厳密に判定
#  (b) X が満ちていて Y は満ちていない組のうち、X が出す向きの探り(X_t(b) ≠ b かつ X_t(b) ≠ Y_t(b))がないもの
import sys, itertools, pickle, random, time
import numpy as np
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import dist_kill
from nonfull import full
from kj_comp import MemObs
n = 4; I = tuple(range(n))
fulls = pickle.load(open("conj2pp/full_n4.pkl", "rb")); fullset = set(fulls)
t0 = time.time()
# (b)
cnt = 0; und = 0
for X in fulls:
    opts = []
    for f in X:
        fix = [b for b in range(n) if f[b] == b]
        alts = []
        for vals in itertools.product(range(n), repeat=len(fix)):
            g = list(f)
            for b, v in zip(fix, vals): g[b] = v
            g = tuple(g)
            if g != I: alts.append(g)
        opts.append(alts)
    for Y in itertools.product(*opts):
        if Y == X or Y in fullset: continue
        cnt += 1
        if dist_kill(X, Y, n) is None:
            und += 1; print("(b) 区別できない:", X, Y, flush=True)
print(f"(b) 調べた組 {cnt}、区別できない {und} ({time.time()-t0:.0f}s)", flush=True)
# (a)
F = list(itertools.product(range(n), repeat=n)); idx = {f: i for i, f in enumerate(F)}
reps = [tuple(idx[f] for f in X) for X in fulls]
mo = MemObs(n, 4, reps); group = np.zeros(len(reps), dtype=np.int64); rng = random.Random(0); stall = 0
for trial in range(200000):
    sizes = np.bincount(group); active = np.nonzero(sizes[group] > 1)[0]
    if len(active) == 0: break
    T = rng.choice([1, 2, 3, 4, 5])
    Q = [tuple(rng.randrange(n) for _ in range(n ** (t + 1))) for t in range(T)]
    m = mo.mask(Q, active); key = group[active] * (1 << n) + m
    _, newid = np.unique(key, return_inverse=True); before = group.max() + 1
    g2 = group.copy(); g2[active] = newid + before; _, group = np.unique(g2, return_inverse=True)
    stall = 0 if group.max() + 1 > before else stall + 1
    if stall > 3000: break
    if trial % 1000 == 0: print(f"  (a) 試行 {trial}: 類 {group.max()+1}/{len(reps)} ({time.time()-t0:.0f}s)", flush=True)
sizes = np.bincount(group); bad = [np.nonzero(group == g)[0] for g in np.nonzero(sizes > 1)[0]]
chk = und = 0
for b in bad:
    for i in range(len(b)):
        for j in range(i + 1, len(b)):
            chk += 1
            if dist_kill(fulls[b[i]], fulls[b[j]], n) is None:
                und += 1; print("(a) 区別できない:", fulls[b[i]], fulls[b[j]], flush=True)
print(f"(a) 満ちた {len(fulls)} 個: 分割で残った {chk} 組を厳密に判定、区別できない {und} ({time.time()-t0:.0f}s)", flush=True)
