# 「避けさせられる ⇔ 一手で潰せる」に基づく判定(定理 J の形)を、distinguishable と突き合わせる
import itertools, random, sys, time
sys.path.insert(0, '.')
from kj_comp import distinguishable
from functools import lru_cache

def segs(P, nS):
    L = len(P); seg = {}
    for i in range(L + 1):
        cur = tuple(range(nS)); seg[(i, i)] = cur
        for j in range(i + 1, L + 1):
            cur = tuple(P[j - 1][c] for c in cur); seg[(i, j)] = cur
    return seg

def killable(sQ, LQ, bq, v, nS):
    return any(all(sQ[(j, LQ)][y] != v for j in bq) for y in range(nS))

def dist_kill(A, B, nS, init=0, extra=0):
    sa, sb = segs(A, nS), segs(B, nS); La, Lb = len(A), len(B)
    depth0 = max(La, Lb) + 1 + extra
    def advance(seg, L, belief, y):
        out = {}
        for i in belief:
            for j in range(i, L + 1):
                out.setdefault(seg[(i, j)][y], set()).add(j)
        return out
    for v in range(nS):
        for (sP, LP, sQ, LQ) in [(sa, La, sb, Lb), (sb, Lb, sa, La)]:
            @lru_cache(maxsize=None)
            def good(bp, bq, d):
                if not bp: return False
                for y in range(nS):
                    if any(sP[(i, LP)][y] == v for i in bp) and all(sQ[(j, LQ)][y] != v for j in bq):
                        return True
                    if d > 0:
                        cp, cq = advance(sP, LP, bp, y), advance(sQ, LQ, bq, y)
                        if all(killable(sQ, LQ, q, v, nS) for q in cq.values()) and \
                           any(good(frozenset(cp[x]), frozenset(cq.get(x, ())), d - 1) for x in cp):
                            return True
                return False
            if sP[(0, LP)][init] == v and sQ[(0, LQ)][init] != v:
                return (v, 0)
            cp, cq = advance(sP, LP, {0}, init), advance(sQ, LQ, {0}, init)
            if all(killable(sQ, LQ, q, v, nS) for q in cq.values()) and \
               any(good(frozenset(cp[x]), frozenset(cq.get(x, ())), depth0 - 1) for x in cp):
                return (v, 1)
    return None

if __name__ == "__main__":
    rng = random.Random(3); mism = 0; tot = 0; t0 = time.time()
    for nS, L, N in [(2, 3, 3000), (3, 3, 3000), (3, 4, 3000), (4, 4, 1500), (4, 6, 500)]:
        F = list(itertools.product(range(nS), repeat=nS))
        for _ in range(N):
            A = [rng.choice(F) for _ in range(L)]; B = A[:]
            k = rng.randrange(L); B[k] = rng.choice(F)
            if rng.random() < 0.3: B.pop(rng.randrange(L))
            d1 = distinguishable(tuple(A), tuple(B), nS) is not None
            d2 = dist_kill(tuple(A), tuple(B), nS) is not None
            tot += 1; mism += d1 != d2
    print("不一致", mism, "/", tot, f"({time.time()-t0:.0f}s)")
