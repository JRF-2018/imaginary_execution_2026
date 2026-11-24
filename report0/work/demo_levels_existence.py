# -*- coding: utf-8 -*-
"""階層の各レベルで「その rf の実行が存在するか・どう決まるか」を調べる補足(ノートには入れていない)。

ELDE のプロセスは replay(inputs) で動く: CS (q,m) の出力は、q の 0..m 番目の lock で受け取った
状態すべてに依存する(プロセスの局所変数がある)。したがって「出力の依存関係」は rf ∪ po になる。
"""
import itertools
from kj_core import Proc, LOCK, unlock, put, get, INIT

def nodes_of(Ls):
    return [(q, m) for q, L in enumerate(Ls) for m in range(L)]

def cands(Ls, v):
    q, m = v
    own = (q, m - 1) if m > 0 else INIT
    return [own] + [u for u in nodes_of(Ls) if u[0] != q]

def acyclic(edges, nodes):
    succ = {n: [] for n in nodes}
    for a, b in edges:
        succ[a].append(b)
    color = {}
    def dfs(u):
        color[u] = 1
        for w in succ[u]:
            if color.get(w) == 1 or (w not in color and not dfs(w)):
                return False
        color[u] = 2
        return True
    return all(dfs(n) for n in nodes if n not in color)

def level(rf, Ls):
    ns = nodes_of(Ls)
    rf_e = [(p, v) for v, p in rf.items() if p != INIT]
    po_e = [((q, m - 1), (q, m)) for (q, m) in ns if m > 0]
    if acyclic(rf_e + po_e, ns):
        return "I 以下(rf ∪ po 非巡回)"
    if acyclic(rf_e, ns):
        return "B(rf だけ非巡回)"
    return "L(rf が循環)"

def evaluate(procs, rf, Ls, domain, init=()):
    """rf の下で自己無撞着な実行(各 CS の入力状態の組)をすべて探す。

    未知数は各 CS の入力状態。候補を総当りし、replay で出力を計算して
    「(q,m) の入力 = rf(q,m) の出力」がすべて成り立つものを残す。"""
    ns = nodes_of(Ls)
    sols = []
    for assign in itertools.product(domain, repeat=len(ns)):
        inp = dict(zip(ns, assign))
        outs = {}
        for q, L in enumerate(Ls):
            st, us, out, _ = procs[q].replay(tuple(inp[(q, m)] for m in range(L)))
            for m in range(L):
                outs[(q, m)] = us[m]
        ok = all(inp[v] == (init if rf[v] == INIT else outs[rf[v]]) for v in ns)
        if ok:
            sols.append(inp)
    return sols

# 局所変数を持つプロセス: 1 回目の CS で v を読んで覚え、2 回目の CS で「覚えた値 + d」を書く
def twophase(d):
    def p(out):
        s = yield LOCK; t = get(s, "v", 0); yield unlock(s)
        s = yield LOCK; yield unlock(put(s, "v", (t + d) % 3))
    return Proc(p)

# 局所変数を持たないプロセス: どの CS も「読んだ v + d」を書く
def stateless(d):
    def p(out):
        for _ in range(2):
            s = yield LOCK; yield unlock(put(s, "v", (get(s, "v", 0) + d) % 3))
    return Proc(p)

Ls = (2, 2)
dom = [(("v", k),) for k in range(3)]
rfs = []
for choice in itertools.product(*[cands(Ls, v) for v in nodes_of(Ls)]):
    rfs.append(dict(zip(nodes_of(Ls), choice)))

for name, procs in [("局所変数あり(二段階)", [twophase(1), twophase(2)]),
                    ("局所変数なし", [stateless(1), stateless(2)])]:
    stat = {}
    for rf in rfs:
        lv = level(rf, Ls)
        n = len(evaluate(procs, rf, Ls, dom, init=(("v", 0),)))
        stat.setdefault(lv, {}).setdefault(n, 0)
        stat[lv][n] += 1
    print(f"== {name}: 自己無撞着な実行の個数ごとの rf の数")
    for lv in ["I 以下(rf ∪ po 非巡回)", "B(rf だけ非巡回)", "L(rf が循環)"]:
        print(f"   {lv:<20} {dict(sorted(stat.get(lv, {}).items()))}")
