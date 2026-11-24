# 長さ n の「満ちた」プロセスを全部数える(後ろから作り、各 w の軌跡の値の数で枝刈り)
import sys, itertools, time, pickle
import numpy as np
n = int(sys.argv[1]); L = n
F = np.array([f for f in itertools.product(range(n), repeat=n) if f != tuple(range(n))], dtype=np.int64)
nF = len(F); t0 = time.time()
# 状態: (後ろから選んだ CS の列, 位置 k..L の接尾写像の列)。各 w について {s_j(w): j>=k} の値の集合をビットで持つ
ident = np.arange(n)
# 位置 L: s_L = id、集合 = {w}
cur = [((), ident, np.array([1 << w for w in range(n)]))]   # (列, s_k, bits)
for k in range(L - 1, -1, -1):
    need = n - k            # 位置 k..L の値だけで、各 w について少なくとも n-k 個の値が必要
    nxt = []
    for seq, s, bits in cur:
        # s_k = s_{k+1} ∘ g_{k+1}
        sk = s[F]                                 # (nF, n): sk[g][w] = s[g[w]]
        nb = bits[None, :] | (1 << sk)
        cnt = np.zeros(nb.shape, dtype=np.int64)
        for b in range(n): cnt += (nb >> b) & 1
        ok = np.all(cnt >= need, axis=1)
        for gi in np.nonzero(ok)[0]:
            nxt.append(((int(gi),) + seq, sk[gi], nb[gi]))
    cur = nxt
    print(f"位置 {k}: 候補 {len(cur)} ({time.time()-t0:.0f}s)", flush=True)
full = [tuple(tuple(int(v) for v in F[g]) for g in seq) for seq, s, bits in cur]
print("長さ", L, "の満ちたプロセス:", len(full))
pickle.dump(full, open(f"conj2pp/full_n{n}.pkl", "wb"))
