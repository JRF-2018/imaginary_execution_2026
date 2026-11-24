# -*- coding: utf-8 -*-
"""§10.4 の時間ループを、kj_ext の is_consistent(ELDE の再生による自己無撞着性の検査)で確かめる補足。

consistent_executions は状態の候補を有限集合から総当りするので、x が実数(複素数)の
この例にはそのまま使えない。そこで、候補を自分で並べ(解析的に求めた ±i も含める)、
一つずつ is_consistent で確かめる。
"""
import math
from kj_core import Proc, LOCK, unlock, put, get, enumerate_real
from kj_ext import is_consistent, mobius_rot, mobius_compose, mobius_fixed_points


def rot(theta):
    t = math.tan(theta)
    def prog(out):
        s = yield LOCK
        x = get(s, "x", 0.0)
        yield unlock(put(s, "x", (x + t) / (1 - x * t)))   # 角度 θ の回転
    return Proc(prog)


th, ph = 0.7, 0.4
procs, Ls = [rot(th), rot(ph)], (1, 1)
print("実実行(初期 x = 0.3):",
      [round(get(r.finals[r.seq[-1][0]], "x"), 6) for r in enumerate_real(procs, init=(("x", 0.3),))])

rf = {(0, 0): (1, 0), (1, 0): (0, 0)}      # 互いに相手の出力を読む時間ループ(階層 L)
fps = mobius_fixed_points(mobius_compose(mobius_rot(ph), mobius_rot(th)))
print("一周の写像の不動点(解析的に求めたもの):", fps)
for x in [0.0, 0.3, 1.0, -2.0] + list(fps):
    s0 = (("x", x),)
    # P0 が s0 を読むなら、P1 は P0 の出力を読む。その組が整合するかを調べる
    u0 = procs[0].replay((s0,))[1][0]
    ok = is_consistent(procs, rf, Ls, {(0, 0): s0, (1, 0): u0},
                       eq=lambda a, b: abs(get(a, "x") - get(b, "x")) < 1e-9)
    print(f"  P0 が x = {complex(x):.3f} を読む → 自己無撞着: {ok}")
