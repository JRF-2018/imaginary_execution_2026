# 予想 2″ の完全な検証: |S|=nS、CS L 個以下(恒等写像を消した形すべて)。
# 記憶のある相手で分割を細かくし、残った組は厳密な判定(killchar.dist_kill)で決着させる。
import itertools, random, sys, time
import numpy as np
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import dist_kill
nS = int(sys.argv[1]); L = int(sys.argv[2]); budget = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
F = np.array(list(itertools.product(range(nS), repeat=nS)), dtype=np.uint8)
ident = [tuple(f) for f in F.tolist()].index(tuple(range(nS)))
nonid = np.array([i for i in range(len(F)) if i != ident], dtype=np.int32)
blocks = []
for k in range(L + 1):
    if k == 0:
        blocks.append(np.full((1, L), ident, dtype=np.int32)); continue
    grids = np.stack(np.meshgrid(*([nonid] * k), indexing="ij"), -1).reshape(-1, k)
    pad = np.full((len(grids), L - k), ident, dtype=np.int32)
    blocks.append(np.concatenate([grids, pad], 1))
P = np.concatenate(blocks)
nP = len(P); print("代表", nP, flush=True)
rows = np.arange(nP)
seg = {}
for i in range(L + 1):
    cur = np.tile(np.arange(nS, dtype=np.uint8), (nP, 1)); seg[(i, i)] = cur
    for j in range(i + 1, L + 1):
        cur = F[P[:, j - 1]][rows[:, None], cur.astype(np.int64)]
        seg[(i, j)] = cur
def mask(Q, idx):
    T = len(Q); m = np.zeros(len(idx), dtype=np.int16)
    for cuts in itertools.combinations_with_replacement(range(L + 1), T):
        x = seg[(0, cuts[0])][idx, 0].astype(np.int64); h = x.copy()
        for t in range(T):
            y = np.asarray(Q[t], dtype=np.int64)[h]
            nxt = cuts[t + 1] if t + 1 < T else L
            x = seg[(cuts[t], nxt)][idx, y].astype(np.int64)
            h = h * nS + x
        m |= (1 << x).astype(np.int16)
    return m
group = np.zeros(nP, dtype=np.int64); rng = random.Random(0); t0 = time.time()
def ctxs():
    for q in itertools.product(range(nS), repeat=nS): yield [q]
    while True:
        T = rng.choice([2, 3, 4, 5]); yield [tuple(rng.randrange(nS) for _ in range(nS ** (t + 1))) for t in range(T)]
stall = 0
for trial, Q in enumerate(ctxs()):
    if trial >= budget: break
    sizes = np.bincount(group); active = np.nonzero(sizes[group] > 1)[0]
    if len(active) == 0: break
    m = mask(Q, active); key = group[active] * 64 + m
    _, newid = np.unique(key, return_inverse=True)
    before = group.max() + 1
    g2 = group.copy(); g2[active] = newid + before
    _, group = np.unique(g2, return_inverse=True)
    after = group.max() + 1
    stall = 0 if after > before else stall + 1
    if trial % 200 == 0 or after > before and len(active) < 1000:
        print(f"試行 {trial}: 類 {after}/{nP}, 未分離 {len(active)} ({time.time()-t0:.0f}s)", flush=True)
    if stall > 3000: break
sizes = np.bincount(group); bad = [np.nonzero(group == g)[0] for g in np.nonzero(sizes > 1)[0]]
print("分割の後に残った類", len(bad), f"({time.time()-t0:.0f}s)", flush=True)
Ft = [tuple(int(v) for v in f) for f in F]
def proc(r): return tuple(Ft[i] for i in P[r] if i != ident)
und = 0; chk = 0
for b in bad:
    for a in range(len(b)):
        for c in range(a + 1, len(b)):
            chk += 1
            if dist_kill(proc(b[a]), proc(b[c]), nS) is None:
                und += 1; print("区別できない:", proc(b[a]), proc(b[c]), flush=True)
print(f"|S|={nS} CS {L} 個以下: 残った {chk} 組を厳密に判定、区別できない組 {und}  ({time.time()-t0:.0f}s)", flush=True)
