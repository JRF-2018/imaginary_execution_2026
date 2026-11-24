# 一般化した「一歩ずつの軌跡」: 最初の読みは P が動く前、各間隔の P の CS は 0 個か 1 個。
import itertools, random, sys, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import segs, killable, dist_kill
from lockstep import belief_step

def check_tau(P, sQ, LQ, nS, steps, ys, init=0):
    """steps[t] ∈ {0,1}: 手番 t+1 の書き込みの後に P が実行する CS の数。P の軌跡 τ が定理 J の条件を満たすか。"""
    pos = 0; xs = [init]
    for t in range(len(ys) - 1):
        x = ys[t]
        if steps[t]: x = P[pos][x]; pos += 1
        xs.append(x)
    z = ys[-1]
    if steps[-1]: z = P[pos][z]; pos += 1
    assert pos == len(P)
    v = z
    Bq = frozenset(j for j in range(LQ + 1) if sQ[(0, j)][init] == xs[0])
    for x in range(nS):
        if x != xs[0]:
            side = frozenset(j for j in range(LQ + 1) if sQ[(0, j)][init] == x)
            if side and not killable(sQ, LQ, side, v, nS): return False
    for t in range(1, len(ys)):
        y = ys[t - 1]
        for x in range(nS):
            if x != xs[t]:
                side = belief_step(sQ, LQ, Bq, y, x)
                if side and not killable(sQ, LQ, side, v, nS): return False
        Bq = belief_step(sQ, LQ, Bq, y, xs[t])
    return all(sQ[(j, LQ)][ys[-1]] != v for j in Bq)

def lockstep2_ok(A, B, nS, extra=2, init=0):
    for (P, Q) in [(A, B), (B, A)]:
        sQ = segs(Q, nS); LP, LQ = len(P), len(Q)
        for T in range(max(LP, 1), LP + extra + 1):
            for ones in itertools.combinations(range(T), LP):
                steps = [1 if t in ones else 0 for t in range(T)]
                for ys in itertools.product(range(nS), repeat=T):
                    if check_tau(P, sQ, LQ, nS, steps, ys, init): return True
    return False

if __name__ == "__main__":
    rng = random.Random(11); t0 = time.time()
    for nS, Lmax, N in [(2, 2, 2000), (3, 3, 4000), (4, 4, 1500), (3, 4, 3000)]:
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
            if lockstep2_ok(tuple(A), tuple(B), nS): stat["可"] += 1
            else:
                stat["不可"] += 1
                if len(ex) < 4: ex.append((A, B))
        print(nS, Lmax, stat, ex, f"({time.time()-t0:.0f}s)", flush=True)
