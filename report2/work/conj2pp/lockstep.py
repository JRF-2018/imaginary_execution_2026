# 「一歩ずつの軌跡」τ(最初の読みは P が動く前、相手の手番の間に P の CS がちょうど一つ)だけで
# 定理 J の条件を満たせるか。厳密な判定と比べる。
import itertools, random, sys, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import segs, killable, dist_kill

def belief_step(seg, L, B, y, x):
    return frozenset(j for i in B for j in range(i, L + 1) if seg[(i, j)][y] == x)

def lockstep_ok(A, B, nS, init=0):
    for (P, Q) in [(A, B), (B, A)]:
        sP, sQ = segs(P, nS), segs(Q, nS); LP, LQ = len(P), len(Q)
        for ys in itertools.product(range(nS), repeat=LP):
            # τ: x_1 = init(P は動いていない)、y_t を書き、P が CS t を一つ実行して読む…
            xs = [init]
            for t in range(LP - 1):
                xs.append(P[t][ys[t]])
            v = P[LP - 1][ys[LP - 1]] if LP else init
            ok = True
            Bq = frozenset(j for j in range(LQ + 1) if sQ[(0, j)][init] != None and sQ[(0, j)][init] == xs[0])
            # 1 回目の読みの横の信念
            for x in range(nS):
                if x != xs[0]:
                    side = frozenset(j for j in range(LQ + 1) if sQ[(0, j)][init] == x)
                    if side and not killable(sQ, LQ, side, v, nS): ok = False; break
            if not ok: continue
            for t in range(1, LP):
                y = ys[t - 1]
                for x in range(nS):
                    if x != xs[t]:
                        side = belief_step(sQ, LQ, Bq, y, x)
                        if side and not killable(sQ, LQ, side, v, nS): ok = False; break
                if not ok: break
                Bq = belief_step(sQ, LQ, Bq, y, xs[t])
            if not ok: continue
            if all(sQ[(j, LQ)][ys[-1]] != v for j in Bq):
                return True
    return False

if __name__ == "__main__":
    rng = random.Random(11); t0 = time.time()
    for nS, Lmax, N in [(2, 2, 2000), (3, 3, 4000), (4, 4, 1500)]:
        F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
        stat = {"区別でき一歩で可": 0, "区別できるが一歩では不可": 0, "区別できない": 0}; ex = []
        for _ in range(N):
            La = rng.randint(1, Lmax); A = [rng.choice(F) for _ in range(La)]; B = A[:]
            B[rng.randrange(La)] = rng.choice(F)
            if rng.random() < 0.3 and len(B) > 1: B.pop(rng.randrange(len(B)))
            if rng.random() < 0.2: B.insert(rng.randrange(len(B) + 1), rng.choice(F))
            B = B[:Lmax]
            if A == B: continue
            d = dist_kill(tuple(A), tuple(B), nS) is not None
            if not d: stat["区別できない"] += 1; continue
            if lockstep_ok(tuple(A), tuple(B), nS): stat["区別でき一歩で可"] += 1
            else:
                stat["区別できるが一歩では不可"] += 1
                if len(ex) < 4: ex.append((A, B))
        print(nS, Lmax, stat, ex[:4], f"({time.time()-t0:.0f}s)", flush=True)
