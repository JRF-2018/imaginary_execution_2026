# 境界(避ける側が満ちていて CS = |S|)の組で、一歩ずつの相手のどんな選び方が効くかを調べる
import sys, itertools, random, pickle, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from kj_comp import suffix_maps, prefix_maps, is_full, killer
from lockstep import belief_step
from killchar import segs

def lock_ok(P, X, nS, ys, v, init=0):
    """一歩ずつの相手(最後に v を自由に書く)が、X の信念をすべて潰して区別できるか。"""
    sX = segs(X, nS); M = len(X); L = len(P)
    xs = [init] + [P[t][ys[t]] for t in range(L)]
    B = frozenset(j for j in range(M + 1) if sX[(0, j)][init] == init)
    for x in range(nS):
        if x != init:
            side = frozenset(j for j in range(M + 1) if sX[(0, j)][init] == x)
            if side and killer(X, nS, side, v) is None: return False
    for t in range(L):
        for x in range(nS):
            if x != xs[t + 1]:
                side = belief_step(sX, M, B, ys[t], x)
                if side and killer(X, nS, side, v) is None: return False
        B = belief_step(sX, M, B, ys[t], xs[t + 1])
    # 最後に v を書く: X が B のどこにいても v にならない
    return all(sX[(j, M)][v] != v for j in B)

def probes(P, X, nS):
    return [(t, b) for t in range(len(P)) for b in range(nS) if P[t][b] != X[t][b] and P[t][b] != b]

def study(P, X, nS):
    """戻り値: 効く (probe, ys, v) の例と、movers を何でもよいか等の統計"""
    L = len(P)
    movers = [[y for y in range(nS) if P[t][y] != y] for t in range(L)]
    res = []
    for (t0, b) in probes(P, X, nS):
        choices = [movers[t] if t != t0 else [b] for t in range(L)]
        for ys in itertools.product(*choices):
            for v in range(nS):
                if lock_ok(P, X, nS, ys, v):
                    res.append((t0, b, ys, v))
    return res

if __name__ == "__main__":
    n = int(sys.argv[1]); N = int(sys.argv[2])
    rng = random.Random(3)
    fulls = pickle.load(open(f"conj2pp/full_n{n}.pkl", "rb"))
    F = [f for f in itertools.product(range(n), repeat=n) if f != tuple(range(n))]
    fail = 0; tot = 0; t0 = time.time(); kinds = {}
    for _ in range(N):
        X = rng.choice(fulls); P = list(X)
        k = rng.randrange(n); P[k] = rng.choice(F)
        if rng.random() < 0.3: P = list(rng.choice(fulls))
        P = tuple(P)
        if P == X or not probes(P, X, n): continue
        tot += 1
        r = study(P, X, n)
        if not r:
            fail += 1
            if fail <= 5: print("一歩ずつ(探り固定)では駄目:", P, X, flush=True)
    print(f"n={n}: {tot} 組中、探り+動かす値+v の一歩ずつの相手で区別できないもの {fail} ({time.time()-t0:.0f}s)")
