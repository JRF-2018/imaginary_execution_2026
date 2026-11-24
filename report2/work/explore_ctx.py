"""探索: 文脈同値と候補の意味の比較(下書き)。"""
import itertools, sys
from collections import defaultdict

S = range(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
LP = int(sys.argv[2]) if len(sys.argv) > 2 else 2
LQ = int(sys.argv[3]) if len(sys.argv) > 3 else 2
FUNCS = list(itertools.product(S, repeat=len(S)))      # 関数 S→S を値の組で表す

def inter(a, b):
    if not a: yield b; return
    if not b: yield a; return
    for r in inter(a[1:], b): yield (a[0],) + r
    for r in inter(a, b[1:]): yield (b[0],) + r

def finals(P, Q, init=0):
    out = set()
    for seq in inter(P, Q):
        s = init
        for f in seq: s = f[s]
        out.add(s)
    return frozenset(out)

procs = list(itertools.product(FUNCS, repeat=LP))
ctxs = [q for L in range(1, LQ + 1) for q in itertools.product(FUNCS, repeat=L)]
ctx_sig = {P: tuple(finals(P, Q) for Q in ctxs) for P in procs}

def compose(fs):
    return tuple(_apply(fs, s) for s in S)
def _apply(fs, s):
    for f in fs: s = f[s]
    return s

cands = {
  "実だけ(全体の合成)": lambda P: compose(P),
  "接尾の合成": lambda P: tuple(compose(P[i:]) for i in range(len(P))),
  "全部(各 CS の関数)": lambda P: P,
}
def nclasses(key):
    return len({key(P) for P in procs})
print(f"|S|={len(S)} LP={LP} LQ<={LQ}: プロセス {len(procs)} 個, 文脈 {len(ctxs)} 個")
print("文脈同値の類の数:", len(set(ctx_sig.values())))
for name, k in cands.items():
    # 細かさの比較: k が同じ ⇒ 文脈同値?(健全)/ 文脈同値 ⇒ k が同じ?(完全)
    sound = all(ctx_sig[P] == ctx_sig[Q] for P in procs for Q in procs if k(P) == k(Q)) if len(procs) < 800 else None
    by = defaultdict(set)
    for P in procs: by[k(P)].add(ctx_sig[P])
    sound = all(len(v) == 1 for v in by.values())
    by2 = defaultdict(set)
    for P in procs: by2[ctx_sig[P]].add(k(P))
    complete = all(len(v) == 1 for v in by2.values())
    print(f"  {name:<14} 類 {nclasses(k):>5}  合成的(同じなら文脈同値) {sound}  完全抽象(文脈同値なら同じ) {complete}")
