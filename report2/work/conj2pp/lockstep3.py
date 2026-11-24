# 最後の手番を「P が終わった後に v を自由に書く」に限った一歩ずつの軌跡で足りるか
import itertools, random, sys, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import segs, killable, dist_kill
from lockstep2 import check_tau

def free_final_ok(A, B, nS, extra=1, init=0, first_read_before=True):
    for (P, Q) in [(A, B), (B, A)]:
        sQ = segs(Q, nS); LP, LQ = len(P), len(Q)
        for T in range(LP + 1, LP + extra + 1):
            for ones in itertools.combinations(range(T - 1), LP):
                steps = [1 if t in ones else 0 for t in range(T)]
                for ys in itertools.product(range(nS), repeat=T):
                    if check_tau(P, sQ, LQ, nS, steps, ys, init): return True
    return False

if __name__ == "__main__":
    rng = random.Random(12); t0 = time.time()
    for nS, Lmax, N, extra in [(2, 2, 2000, 1), (3, 3, 3000, 1), (4, 4, 1000, 1), (3, 3, 3000, 2), (4, 4, 1000, 2)]:
        F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
        stat = {"可": 0, "不可": 0, "区別できない": 0}; ex = []
        for _ in range(N):
            La = rng.randint(1, Lmax); A = [rng.choice(F) for _ in range(La)]; B = A[:]
            B[rng.randrange(La)] = rng.choice(F)
            if rng.random() < 0.3 and len(B) > 1: B.pop(rng.randrange(len(B)))
            if rng.random() < 0.2: B.insert(rng.randrange(len(B) + 1), rng.choice(F))
            B = B[:Lmax]
            if A == B: continue
            if dist_kill(tuple(A), tuple(B), nS) is None: stat["区別できない"] += 1; continue
            if free_final_ok(tuple(A), tuple(B), nS, extra): stat["可"] += 1
            else:
                stat["不可"] += 1
                if len(ex) < 3: ex.append((A, B))
        print(nS, Lmax, "extra", extra, stat, ex, f"({time.time()-t0:.0f}s)", flush=True)
