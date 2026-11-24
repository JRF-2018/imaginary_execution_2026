# -*- coding: utf-8 -*-
"""kj_txn.py -- 「虚実行と合流」(report1)の計算コア。

トランザクション = スナップショット(状態のコピー)を読み、書き込みを残す CS。
確定(commit)のとき、書き込みを現在の状態へ「合流」させる。
report0 の言葉では、スナップショットを二つ以上のトランザクションが読むのが「コピー」(虚実行)、
確定のときに自分のスナップショット以後の確定を取り込むのが「合流」である。

    t = Txn("T1", R={"x"}, W={"x"}, f=lambda s: {"x": s["x"] + 1})

f はスナップショット(辞書)を受け取り、書き込む変数とその値の辞書を返す。f は R の値だけに依存すること。
"""
from __future__ import annotations
import itertools
from collections import Counter, defaultdict


class Txn:
    def __init__(self, name, R, W, f):
        self.name = name
        self.R = frozenset(R)
        self.W = frozenset(W)
        self.f = f

    def writes(self, snap):
        w = self.f(dict(snap))
        assert set(w) <= self.W, (self.name, w)
        return w

    def __repr__(self):
        return self.name


# ------------------------------------------------------------------
# 実行の並び: start_i / commit_i の事象列(start_i が commit_i より前)
# ------------------------------------------------------------------
def schedules(n):
    """n 個のトランザクションの事象列をすべて作る。事象は ("s", i) / ("c", i)。"""
    out = []

    def rec(seq, started, committed):
        if len(committed) == n:
            out.append(tuple(seq))
            return
        for i in range(n):
            if i not in started:
                rec(seq + [("s", i)], started | {i}, committed)
            elif i not in committed:
                rec(seq + [("c", i)], started, committed | {i})
    rec([], frozenset(), frozenset())
    return out


def is_serial_schedule(sched):
    """重なりのない(start の直後に同じトランザクションの commit が来る)並び = 実実行。"""
    return all(sched[k][0] == "s" and sched[k + 1] == ("c", sched[k][1]) for k in range(0, len(sched), 2))


# ------------------------------------------------------------------
# 実行: 確定規則ごとの合流
# ------------------------------------------------------------------
RULES = ("NOVAL", "SI", "SSI", "OCC")


class Run:
    """一つの実行の結果。"""

    def __init__(self):
        self.order = []          # 確定した順のトランザクション番号
        self.aborted = []        # 中止したトランザクション番号
        self.snap = {}           # i -> スナップショット(dict)
        self.snap_ver = {}       # i -> スナップショットの版(それまでに確定した数)
        self.commit_ver = {}     # i -> 確定したときの版番号(確定順で 1, 2, ...)
        self.reads = {}          # i -> R の値(読んだ値)
        self.final = None        # 最終状態
        self.history = []        # 版の列 [(書いたトランザクション, 状態)]、版 0 は初期状態

    def merges(self):
        """合流の数: 確定のとき、自分のスナップショット以後に別の確定があったもの。"""
        return sum(1 for i in self.order if self.commit_ver[i] - 1 != self.snap_ver[i])

    def copies(self):
        """コピーの数: 二つ以上のトランザクションに読まれた版について (読んだ数 - 1) の和。"""
        c = Counter(self.snap_ver[i] for i in self.order)
        return sum(k - 1 for k in c.values() if k > 1)


def run(txns, sched, rule, init):
    """事象列 sched を確定規則 rule で実行する。"""
    assert rule in RULES
    n = len(txns)
    st = dict(init)
    r = Run()
    r.history.append((None, dict(st)))
    start_ver = {}
    rw_in, rw_out = defaultdict(set), defaultdict(set)    # SSI 用: 並行するトランザクション間の rw 逆依存

    def committed_since(i):
        return [j for j in r.order if r.commit_ver[j] > start_ver[i]]

    for kind, i in sched:
        t = txns[i]
        if kind == "s":
            start_ver[i] = len(r.order)
            r.snap[i] = dict(st)
            r.snap_ver[i] = start_ver[i]
            continue
        since = committed_since(i)
        if rule in ("SI", "SSI") and any(txns[j].W & t.W for j in since):
            r.aborted.append(i); continue                 # first-committer-wins
        if rule == "OCC" and any(txns[j].W & t.R for j in since):
            r.aborted.append(i); continue                 # Kung–Robinson の後ろ向き検証
        if rule == "SSI":
            # i と、i の実行中に確定した j: i が読んだ変数を j が書いた → i -rw-> j
            new_out = {j for j in since if t.R & txns[j].W}
            # まだ確定していない i の書き込みを、i より前に始まり i の開始後に確定した j が読んでいた → j -rw-> i
            new_in = {j for j in since if txns[j].R & t.W}
            # 確定済みで i と時間が重なる(i の開始時にまだ確定していなかった)もの全体
            overlap = set(since)
            out_i = rw_out[i] | new_out
            in_i = rw_in[i] | new_in
            pivot = bool(out_i) and bool(in_i)
            for j in new_out:                             # j が新たに in を得て pivot になるか
                pivot |= bool(rw_out[j])
            for j in new_in:                              # j が新たに out を得て pivot になるか
                pivot |= bool(rw_in[j])
            if pivot:
                r.aborted.append(i); continue
            rw_out[i] |= new_out; rw_in[i] |= new_in
            for j in new_out:
                rw_in[j].add(i)
            for j in new_in:
                rw_out[j].add(i)
        w = t.writes(r.snap[i])
        st.update(w)                                      # 合流: 書き込んだ変数だけ上書き
        r.order.append(i)
        r.commit_ver[i] = len(r.order)
        r.reads[i] = {x: r.snap[i].get(x) for x in t.R}
        r.history.append((i, dict(st)))
    r.final = st
    return r


def serial_equivalents(txns, r, init):
    """確定したトランザクションを直列に実行して、読んだ値と最終状態が r と一致する順序をすべて返す。"""
    out = []
    for perm in itertools.permutations(r.order):
        st = dict(init)
        ok = True
        for i in perm:
            if {x: st.get(x) for x in txns[i].R} != r.reads[i]:
                ok = False; break
            st.update(txns[i].writes(st))
        if ok and st == r.final:
            out.append(perm)
    return out


def classify(txns, init, rules=RULES):
    """すべての事象列を各規則で実行し、(全確定, 中止あり, 直列化不能) などを数える。"""
    n = len(txns)
    scheds = schedules(n)
    table = {}
    for rule in rules:
        c = Counter()
        for sc in scheds:
            r = run(txns, sc, rule, init)
            c["schedules"] += 1
            if r.aborted:
                c["with_abort"] += 1
            ser = bool(serial_equivalents(txns, r, init))
            if not ser:
                c["non_serializable"] += 1
            if r.merges():
                c["with_merge"] += 1
                if ser:
                    c["merge_but_serializable"] += 1
        table[rule] = c
    return table


# ------------------------------------------------------------------
# 依存グラフ(Adya の DSG): wr / ww / rw の辺
# ------------------------------------------------------------------
def dsg(txns, r):
    """確定したトランザクションの依存グラフ。辺は (a, b, 種類)。

    版は確定順に並ぶ。変数 x の版を書いたトランザクションの列を確定順に取り、
      ww: x を続けて書いた a の次に b
      wr: b がスナップショットで読んだ x の版を書いたのが a
      rw: a が読んだ x の版の、次の版を書いたのが b(a は b の書き込みを見ていない)
    """
    edges = set()
    writers = defaultdict(list)            # x -> [確定順の書き手]
    for i in r.order:
        for x in txns[i].W:
            writers[x].append(i)
    for x, ws in writers.items():
        for a, b in zip(ws, ws[1:]):
            edges.add((a, b, "ww"))
    for b in r.order:
        for x in txns[b].R:
            # b のスナップショットに入っていた x の最後の書き手
            before = [a for a in writers.get(x, []) if r.commit_ver[a] <= r.snap_ver[b]]
            if before:
                edges.add((before[-1], b, "wr"))
            after = [c for c in writers.get(x, []) if r.commit_ver[c] > r.snap_ver[b] and c != b]
            if after:
                edges.add((b, after[0], "rw"))
    return edges


def dsg_cycles(edges, nodes):
    """単純な循環をすべて返す(小さなグラフ用)。各循環は [(a, b, kind), ...]。"""
    adj = defaultdict(list)
    for a, b, k in edges:
        adj[a].append((b, k))
    cycles = []
    nodes = sorted(nodes)

    def dfs(start, u, path, seen):
        for v, k in adj[u]:
            if v == start:
                cycles.append(path + [(u, v, k)])
            elif v not in seen and v > start:
                dfs(start, v, path + [(u, v, k)], seen | {v})
    for s in nodes:
        dfs(s, s, [], {s})
    return cycles


def has_consecutive_rw(cycle):
    ks = [k for _, _, k in cycle]
    return any(ks[i] == "rw" and ks[(i + 1) % len(ks)] == "rw" for i in range(len(ks)))


# ------------------------------------------------------------------
# ランダムなトランザクション(性質の総当り確認用)
# ------------------------------------------------------------------
def random_txns(rng, n, vars_=("x", "y", "z"), vals=3, p_read=0.5, p_write=0.4):
    """読み集合・書き集合と、読んだ値の組から書く値への表をランダムに作る。"""
    txns = []
    for k in range(n):
        R = sorted(v for v in vars_ if rng.random() < p_read)
        W = sorted(v for v in vars_ if rng.random() < p_write)
        if not W:
            W = [rng.choice(vars_)]
        table = {}
        for key in itertools.product(range(vals), repeat=len(R)):
            table[key] = {w: rng.randrange(vals) for w in W}

        def f(s, R=tuple(R), table=table):
            return dict(table[tuple(s[x] for x in R)])
        txns.append(Txn(f"T{k + 1}", R, W, f))
    return txns


# ------------------------------------------------------------------
# 読む側を待たせない(§5): 排他ロックと、版を複製する方式(MVCC・RCU)の比較
#   1 本の書き手が、長さ write_len の更新を休みなく繰り返す。
#   読み手は各時刻に確率 lam で到着し、長さ read_len だけ読む。
#   LOCK: 読み手と書き手は排他(書き手の更新中に来た読み手は待つ。読み手がいる間、書き手は始められない)。
#   COPY: 書き手は版を複製して更新し、終わったら新しい版を公開する。読み手は到着時の最新版を待たずに読む。
#         古い版は、それを読んでいる読み手がいなくなるまで残す(RCU の猶予期間)。
# ------------------------------------------------------------------
def sim_readers(policy, lam, write_len=5, read_len=2, T=20000, seed=0):
    import random
    rng = random.Random(seed)
    readers = []           # [残り時間, 読んでいる版]
    queue = 0              # LOCK で待っている読み手の数
    wait_total = 0
    n_reads = 0
    stale = 0              # 読み終わったとき、より新しい版がすでに公開されていた読み
    version = 0            # 公開済みの最新版
    writer_left = write_len
    writer_active = True   # LOCK で書き手が更新中か
    max_versions = 1
    updates = 0
    for t in range(T):
        if rng.random() < lam:
            queue += 1
        if policy == "COPY":
            while queue:
                readers.append([read_len, version]); queue -= 1; n_reads += 1
            writer_left -= 1
            if writer_left == 0:
                version += 1; updates += 1; writer_left = write_len
        else:  # LOCK
            if writer_active:
                writer_left -= 1
                if writer_left == 0:
                    version += 1; updates += 1; writer_active = False
            if not writer_active:
                while queue:
                    readers.append([read_len, version]); queue -= 1; n_reads += 1
            wait_total += queue
        done = [r for r in readers if r[0] <= 1]
        for r in done:
            if r[1] < version:
                stale += 1
        readers = [[r[0] - 1, r[1]] for r in readers if r[0] > 1]
        if policy == "LOCK" and not writer_active and not readers and not queue:
            writer_active = True; writer_left = write_len
        live = len({r[1] for r in readers} | {version})
        max_versions = max(max_versions, live + (1 if policy == "COPY" else 0))
    return dict(policy=policy, lam=lam, mean_wait=wait_total / max(n_reads, 1),
                stale_frac=stale / max(n_reads, 1), max_versions=max_versions,
                updates_per_1000=1000 * updates / T)
