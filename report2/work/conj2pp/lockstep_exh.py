# 一歩ずつの相手(最後に自由な書き込み)が、区別できる組をすべて区別するかの全数確認
import sys, itertools, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import dist_kill
from lockstep3 import free_final_ok
for nS, Lmax in [(2, 4), (3, 2)]:
    t0 = time.time()
    F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
    forms = [tuple(s) for L in range(Lmax + 1) for s in itertools.product(F, repeat=L)]
    st = {"可": 0, "不可": 0, "不可分": 0}; ex = []
    for a in range(len(forms)):
        for b in range(a + 1, len(forms)):
            A, B = forms[a], forms[b]
            if dist_kill(A, B, nS) is None: st["不可分"] += 1; continue
            if free_final_ok(A, B, nS, 1): st["可"] += 1
            else:
                st["不可"] += 1; ex.append((A, B))
    print(f"|S|={nS} CS {Lmax} 個以下: 形 {len(forms)}", st, ex[:3], f"({time.time()-t0:.0f}s)", flush=True)
