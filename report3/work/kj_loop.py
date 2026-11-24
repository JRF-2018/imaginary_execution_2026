# -*- coding: utf-8 -*-
"""kj_loop.py -- 「時間ループと最適化」(report3)の計算コア。

* メビウス変換の反復と不動点の分類(乗数 = 不動点での微分)
* リング発振器(否定を輪にした回路) = 嘘つきの時間ループの物理的な実現
* 再実行による callCC の goto ループ(同じ過去に何度も戻る反復)
* コピーと破棄による探索(GA の選択・粒子フィルタのリサンプリング・ビームサーチの共通の形)
"""
from __future__ import annotations
import cmath
import math
import random


# ------------------------------------------------------------------
# メビウス変換
# ------------------------------------------------------------------
def mob(M, x):
    a, b, c, d = M
    den = c * x + d
    return math.inf if den == 0 else (a * x + b) / den


def fixed_points(M):
    """c z^2 + (d - a) z - b = 0 の解(c = 0 なら一つ)。"""
    a, b, c, d = M
    if c == 0:
        return [b / (d - a)] if d != a else []
    disc = cmath.sqrt((d - a) ** 2 + 4 * b * c)
    return [((a - d) + disc) / (2 * c), ((a - d) - disc) / (2 * c)]


def multiplier(M, z):
    """不動点 z での微分(乗数) f'(z) = (ad - bc)/(cz + d)^2。"""
    a, b, c, d = M
    return (a * d - b * c) / (c * z + d) ** 2


def classify(M):
    """行列式で正規化したトレースで分類する(実係数、行列式 > 0)。"""
    a, b, c, d = M
    det = a * d - b * c
    tr = (a + d) / math.sqrt(det)
    if abs(tr) < 2 - 1e-12:
        return "楕円型(回転)"
    if abs(abs(tr) - 2) <= 1e-12:
        return "放物型"
    return "双曲型(収束)"


def orbit(M, x0, n):
    xs = [x0]
    for _ in range(n):
        xs.append(mob(M, xs[-1]))
    return xs


# ------------------------------------------------------------------
# リング発振器: N 個の否定(インバータ)を輪につなぎ、各段は 1 時刻遅れて前段の否定を出す
# ------------------------------------------------------------------
def ring_oscillator(N, T, init=None):
    x = list(init) if init else [0] * N
    hist = [tuple(x)]
    for _ in range(T):
        x = [1 - x[k - 1] for k in range(N)]
        hist.append(tuple(x))
    return hist


def period_of(seq):
    """列が最後に繰り返す周期(過渡部分を除く)。"""
    last = {}
    for t, v in enumerate(seq):
        if v in last:
            return t - last[v]
        last[v] = t
    return None


# ------------------------------------------------------------------
# 再実行による callCC(report2 と同じ仕組み)
# ------------------------------------------------------------------
class _Jump(Exception):
    pass


def run_with_callcc(program, max_worlds=50):
    """プログラムを最初から再実行して、何度でも再開できる継続を実現する。

    yield ("callcc",) で ("right", k) を受け取り、yield ("throw", k, v) で callcc の時点へ
    値 v を持って戻る(その時点で ("left", v) を受け取ったかのように再実行する)。
    返り値: (世界の列 [(記録, 結果)], 打ち切ったか)
    """
    answers = {}
    worlds = []
    for _ in range(max_worlds):
        g = program()
        log, n_callcc = [], 0
        try:
            req = next(g)
            while True:
                if req[0] == "callcc":
                    k = n_callcc; n_callcc += 1
                    req = g.send(answers.get(k, ("right", k)))
                elif req[0] == "throw":
                    _, k, v = req
                    log.append(v)
                    answers = {kk: vv for kk, vv in answers.items() if kk < k}
                    answers[k] = ("left", v)
                    raise _Jump()
                elif req[0] == "log":
                    log.append(req[1]); req = next(g)
        except StopIteration as e:
            worlds.append((log, e.value))
            return worlds, False
        except _Jump:
            worlds.append((log, None))
    return worlds, True


# ------------------------------------------------------------------
# コピーと破棄による探索
#   NK 景観(Kauffman): N ビットの列、各ビットの寄与は自分と K 個の隣のビットで決まる乱数表。
#   世界(個体・粒子)を pop 個持ち、各時刻:
#     1. 各世界は 1 ビットを変えてみて、悪くならなければ受け入れる(各世界の中では実実行)。
#     2. 各世界は確率 x で、二つを選んで良い方の **コピー** に置き換わる(自分の系統は捨てられる)。
#   x = 0 は独立な山登り(コピーなし)、x = 1 は毎回全員が選択される強い選択。
# ------------------------------------------------------------------
class NK:
    def __init__(self, N, K, seed):
        rng = random.Random(seed)
        self.N, self.K = N, K
        self.nb = [[i] + rng.sample([j for j in range(N) if j != i], K) for i in range(N)]
        self.tab = [[rng.random() for _ in range(2 ** (K + 1))] for _ in range(N)]

    def fitness(self, s):
        tot = 0.0
        for i in range(self.N):
            idx = 0
            for j in self.nb[i]:
                idx = idx * 2 + s[j]
            tot += self.tab[i][idx]
        return tot / self.N


def copy_discard_search(land, pop, T, x, seed):
    """返り値: (最良の適応度, 世代ごとの系統(祖先の番号)の記録, コピーの回数)。

    x は数か、時刻 t(0..T-1)を受け取ってコピーの確率を返す関数(切り換えの予定表)。"""
    rng = random.Random(seed)
    N = land.N
    worlds = [[rng.randrange(2) for _ in range(N)] for _ in range(pop)]
    fit = [land.fitness(w) for w in worlds]
    parent_hist = []           # 各時刻、世界 i がどの世界のコピーか(コピーでなければ自分)
    copies = 0
    for t in range(T):
        for i in range(pop):
            j = rng.randrange(N)
            w = worlds[i][:]
            w[j] ^= 1
            f = land.fitness(w)
            if f >= fit[i]:
                worlds[i], fit[i] = w, f
        par = list(range(pop))
        new_w, new_f = worlds[:], fit[:]
        xt = x(t) if callable(x) else x
        for i in range(pop):
            if rng.random() < xt:
                a, b = rng.randrange(pop), rng.randrange(pop)
                src = a if fit[a] >= fit[b] else b
                if src != i:
                    new_w[i], new_f[i] = worlds[src][:], fit[src]
                    par[i] = src
                    copies += 1
        worlds, fit = new_w, new_f
        parent_hist.append(par)
    return max(fit), parent_hist, copies


def surviving_lineages(parent_hist, pop):
    """最後の世界たちの祖先をたどり、各時刻に生き残っている系統の数を返す。"""
    alive = set(range(pop))
    counts = [len(alive)]
    for par in reversed(parent_hist):
        alive = {par[i] for i in alive}
        counts.append(len(alive))
    return list(reversed(counts))


def climb_time(land, seed, Tmax=5000):
    """コピーなし(x = 0)の一つの世界が、どの 1 ビットの変更でも良くならない状態(局所的な山頂)に初めて着く時刻。"""
    rng = random.Random(seed)
    N = land.N
    w = [rng.randrange(2) for _ in range(N)]
    f = land.fitness(w)

    def local_opt(w, f):
        for j in range(N):
            w[j] ^= 1
            g = land.fitness(w)
            w[j] ^= 1
            if g > f:
                return False
        return True
    for t in range(Tmax):
        if t % 5 == 0 and local_opt(w, f):
            return t
        j = rng.randrange(N)
        w2 = w[:]
        w2[j] ^= 1
        g = land.fitness(w2)
        if g >= f:
            w, f = w2, g
    return Tmax


class Flat:
    """どこも同じ適応度の景観(選択の効かない中立な場合)。"""
    def __init__(self, N):
        self.N = N

    def fitness(self, s):
        return 0.0


def coalescent_lineages(K, x, t):
    """中立なコピー(確率 x、K 個の世界)で、t 時刻さかのぼったときに残る系統の数の近似(Kingman の合着)。
    二つの系統が一時刻で一つにまとまる確率は約 (2x − x²)/K。"""
    p = (2 * x - x * x) / K
    return 1.0 / (1.0 - (1.0 - 1.0 / K) * math.exp(-p * t / 2.0))
