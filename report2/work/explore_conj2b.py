# 予想 2′ の |S|=3・CS 4 個の探索(ノートの外で回した計算、約 10 分)。分割を細かくし、残った組を distinguishable で厳密に判定する。
import itertools, random, time, sys
import numpy as np
sys.path.insert(0,'.')
from kj_comp import MemObs
def refine(nS, L, reps, budget, seed=0, label=""):
    mo = MemObs(nS, L, reps); group = np.zeros(len(reps), dtype=np.int64); rng = random.Random(seed); t0=time.time()
    for trial in range(budget):
        sizes = np.bincount(group); active = np.nonzero(sizes[group] > 1)[0]
        if len(active) == 0: break
        T = rng.choice([1,2,3,4,5,6])
        Q = [tuple(rng.randrange(nS) for _ in range(nS ** (t + 1))) for t in range(T)]
        m = mo.mask(Q, active); key = group[active] * (1 << nS) + m
        _, newid = np.unique(key, return_inverse=True); g2 = group.copy(); g2[active] = newid + group.max() + 1
        _, group = np.unique(g2, return_inverse=True)
        if trial % 5000 == 0: print(f"  {label} 試行 {trial}: {len(np.unique(group))}/{len(reps)} ({time.time()-t0:.0f}s)", flush=True)
    n=len(np.unique(group)); print(f"{label}: {n}/{len(reps)} ({time.time()-t0:.0f}s)", flush=True)
    sizes=np.bincount(group); bad=[np.nonzero(group==g)[0] for g in np.nonzero(sizes>1)[0]]
    return n==len(reps), [[reps[i] for i in b] for b in bad]
nS=3; F=list(itertools.product(range(nS),repeat=nS)); ident=F.index((0,1,2))
consts=[F.index((c,c,c)) for c in range(3)]
perms=[F.index(p) for p in itertools.permutations(range(3)) if p!=(0,1,2)]
fam=consts+perms
L=4
reps=[tuple(seq)+(ident,)*(L-len(seq)) for n in range(L+1) for seq in itertools.product(fam,repeat=n)]
ok,bad=refine(nS,L,reps,60000,label="|S|=3 L=4 定数と置換")
print("成り立つ:",ok); 
for b in bad[:5]: print("  ", [tuple(F[i] for i in r) for r in b])
nonid=[i for i in range(27) if i!=ident]; rng=random.Random(5)
reps2=list({tuple(rng.choice(nonid) for _ in range(n))+(ident,)*(L-n) for n in (3,4) for _ in range(20000)})
ok2,bad2=refine(nS,L,reps2,60000,label="|S|=3 L=4 無作為 4 万")
print("成り立つ:",ok2)
for b in bad2[:5]: print("  ", [tuple(F[i] for i in r) for r in b])

from kj_comp import distinguishable
def settle(bad, label):
    undec=0; checked=0
    for grp in bad:
        procs=[tuple(F[i] for i in r) for r in grp]
        for a in range(len(procs)):
            for b in range(a+1,len(procs)):
                checked+=1
                if not distinguishable(procs[a],procs[b],3): undec+=1; print("   区別できない:",procs[a],procs[b])
    print(f"{label}: 残った組 {checked} 組を厳密に判定 → 区別できないもの {undec}", flush=True)
settle(bad, "定数と置換")
settle(bad2, "無作為")
