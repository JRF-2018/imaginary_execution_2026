# 定理 K・K+ の相手を実際に作り、すべてのインタリーブを実行して確かめる(信念の計算に頼らない独立の確認)
import sys, itertools, random, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import segs
from nonfull import full, suffixes

def run_all(P, partner, T, init=0):
    """P(記憶のない CS の列)と、読んだ値の履歴から書く値を決める相手(T 手)の、すべてのインタリーブの最終状態。"""
    out = set()
    def rec(i, t, s, hist):
        if i == len(P) and t == T:
            out.add(s); return
        if i < len(P): rec(i + 1, t, P[i][s], hist)
        if t < T:
            h = hist + (s,)
            rec(i, t + 1, partner(h), h)
    rec(0, 0, init, ())
    return out

def make_partner(P, X, nS, ys, v, init=0):
    """P に一歩ずつ付いていく相手。予想外の値を読んだら、X の信念を潰す値を書き、あとは読んだ値を写す。"""
    sX = segs(X, nS); M = len(X); L = len(P)
    expected = [init]
    for t in range(L): expected.append(P[t][ys[t]])
    def belief(h):
        B = {j for j in range(M + 1) if sX[(0, j)][init] == h[0]}
        for t in range(1, len(h)):
            y = ys[t - 1]
            B = {j for i in B for j in range(i, M + 1) if sX[(i, j)][y] == h[t]}
        return B
    def killer(B):
        for w in range(nS):
            if all(sX[(j, M)][w] != v for j in B): return w
        return None
    def partner(h):
        t = len(h) - 1
        for k in range(len(h)):
            if h[k] != expected[k]:
                if k == t:
                    w = killer(belief(h))
                    return w if w is not None else 0   # 潰せない(定理の仮定の外)
                return h[-1]                            # 潰した後は写すだけ
        return ys[t] if t < L else v
    return partner

def thm_strategy(A, B, nS):
    """定理 K+ の証明どおりに相手と v を選ぶ。返り値: (P, X, ys, v)"""
    LA, LB = len(A), len(B)
    if LA > LB: P, X, probe = A, B, None
    elif LA < LB: P, X, probe = B, A, None
    else:
        t0 = next(t for t in range(LA) if A[t] != B[t]); b = next(b for b in range(nS) if A[t0][b] != B[t0][b])
        if A[t0][b] != b: P, X = A, B
        else: P, X = B, A
        probe = (t0, b)
    ys = []
    for t in range(len(P)):
        if probe and t == probe[0]: ys.append(probe[1])
        else: ys.append(next(y for y in range(nS) if P[t][y] != y))
    sf = suffixes(X, nS)
    if not full(X, nS):
        v = next(v for v in range(nS) if any(all(f[w] != v for f in sf) for w in range(nS)))
    else:
        v = sf[0][0]     # 満ちている(長さ n-1)なら、全体の写像の像の値
    return P, X, ys, v

if __name__ == "__main__":
    rng = random.Random(7); t0 = time.time()
    for nS, N in [(3, 3000), (4, 1500), (5, 300)]:
        F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
        perms = [f for f in F if len(set(f)) == nS]
        ok = bad = 0
        for _ in range(N):
            Lmax = nS - 1
            # 満ちた(ラテン方陣型の)プロセスを多めに混ぜる
            if rng.random() < 0.3:
                sig = rng.choice([p for p in perms if all(p[i] != i for i in range(nS))])
                A = [sig] * Lmax
            else:
                A = [rng.choice(F) for _ in range(rng.randint(1, Lmax))]
            B = A[:]
            B[rng.randrange(len(B))] = rng.choice(F)
            if rng.random() < 0.3 and len(B) > 1: B.pop(rng.randrange(len(B)))
            if A == B: continue
            A, B = tuple(A), tuple(B)
            P, X, ys, v = thm_strategy(A, B, nS)
            pt = make_partner(P, X, nS, ys, v)
            T = len(P) + 1
            if v in run_all(P, pt, T) and v not in run_all(X, pt, T): ok += 1
            else:
                bad += 1; print("失敗:", A, B, "full", full(A, nS), full(B, nS))
        print(f"|S|={nS} CS {nS-1} 個以下: 区別できた {ok}, 失敗 {bad} ({time.time()-t0:.0f}s)", flush=True)
