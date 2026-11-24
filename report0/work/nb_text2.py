# -*- coding: utf-8 -*-
"""ノートブック本文 後半(§7〜参考文献)。"""

CELLS = []


def md(s):
    CELLS.append(("md", s.strip("\n")))


def code(s):
    CELLS.append(("code", s.strip("\n")))


md(r"""
## §7 虚実行の使い道 ―― 健全な過大近似とその精錬

### 7.1 JRF の観察

> 「虚実行」群の中に「実実行」というべきものがすべて入っているので、「虚実行」群全体でテストに合格したものは「実実行」においてもテストに合格すると言える

これは計算機科学では **健全な過大近似(sound over-approximation)** と呼ばれる考え方そのものである。抽象解釈(Cousot & Cousot 1977)は、プログラムの本当のふるまいの集合を、扱いやすいより大きな集合で置き換えて性質を証明する。大きい集合で「悪いことは起きない」と示せれば、本物でも起きない。そのかわり、大きい集合には本物にはない **偽の反例(false alarm)** が混じる。

並列プログラムの検証には、これとよく似た **スレッド・モジュラー** な抽象がある(Flanagan & Qadeer 2003、Owicki–Gries 1976 や Jones の rely-guarantee 1983 の流れ)。各スレッドは「他のスレッドが作りうる共有状態のどれか」を読むと考えて、スレッドごとに別々に調べる。虚実行の階層(§5.3)の上の方(I や B)は、まさにこの種の抽象の具体例になっている。

### 7.2 例: 加算が失われるか

二つのプロセスが共有変数 `v` に 1 を 2 回ずつ足す。

- **原子的な版**: 読みと書きを同じ CS の中で行う。
- **二段階の版**: ある CS で `v` を読んで手元に覚え、次の CS で「覚えた値 + 1」を書く(典型的なバグ。ロックは使っているのに加算が失われる)。

性質「最後に v = 4」を調べる。虚実行では世界がいくつかに分かれるので、「すべての世界の最終状態で v = 4」を調べることにする。
""")

code(r"""
def mk_atomic(n):
    def p(out):
        for _ in range(n):
            s = yield LOCK
            yield unlock(put(s, "v", get(s, "v", 0) + 1))
    return p

def mk_twophase(n):
    def p(out):
        for _ in range(n):
            s = yield LOCK; t = get(s, "v", 0); yield unlock(s)      # 読んで覚える
            s = yield LOCK; yield unlock(put(s, "v", t + 1))         # 覚えた値+1 を書く
    return p

for name, mk in [("原子的", mk_atomic), ("二段階", mk_twophase)]:
    ps = [Proc(mk(2)), Proc(mk(2))]
    R = enumerate_real(ps)
    E0 = [r for r in enumerate_imag(ps) if is_elde0(r.rf)]
    real_v = Counter(get(r.finals[r.seq[-1][0]], "v", 0) for r in R)
    bad_imag = [r for r in E0 if any(get(s, "v", 0) != 4 for s in world_finals(r))]
    bad_imag_real = [r for r in bad_imag if is_linear(r.rf)]
    print(f"[{name}] 実実行 {len(R)} 通り, 最終 v の分布 {dict(real_v)}")
    print(f"        ELDE0 の実行 {len(E0)} 通り, うち性質を破るもの {len(bad_imag)} 通り"
          f" → 線形(本物の反例) {len(bad_imag_real)} 通り / 偽の反例 {len(bad_imag) - len(bad_imag_real)} 通り")
""")

md(r"""
- 原子的な版では、実実行はすべて v = 4 で、性質は正しい。ところが虚実行では性質を破るものが多数ある。どれも線形でない、つまり **偽の反例** である。状態がコピーされると、増分が別々の世界に散らばって、どの世界にも 4 回分が揃わない。
- 二段階の版では、実実行にも v = 2, 3 が現れる(本物のバグ)。虚実行の中の反例のうち、線形なものが本物の反例である。

ここから次の手順が考えられる。これは反例に導かれた抽象の精錬(CEGAR, Clarke ら 2000)の、ごく素朴な形である。

1. まず虚実行の集合で性質を調べる。全部通れば、実実行でも正しい(健全)。
2. 反例が見つかったら、定理 1 で線形かどうかを調べる。線形なら本物のバグ。
3. 線形でなければ偽の反例なので、その分岐(コピー)を禁じて探索を絞る。

### 7.3 どんな性質なら虚実行で調べてよいか

上の例からわかるのは、**「v = 4」のような保存則は、虚実行で調べると必ず偽の反例が出る** ということである。保存則は「一つの状態を一度しか使わない」という線形性に依存しているからである。

逆に、**各 CS が局所的に保つ性質** は虚実行でも正しい。たとえば「どの CS も v を減らさない」「v は 0 以上」のような不変条件 $J$ は、「$J(s)$ なら $J(\mathrm{CS}(s))$」がすべての CS について成り立てば、どんな木の上でも、根から帰納法で成り立つ。木であっても一本道であっても、各頂点の状態は根からの道に沿って CS を順に施したものだからである。

つまり、

- **帰納的な不変条件**(各 CS が保つ局所的な性質)は、虚実行で調べても失うものがない。帰納的なら、虚実行でも実実行でも成り立つ。ただし、実実行では成り立つが帰納的でない性質(個数や「ちょうど何回」に関わるもの。§7.2 の「最後に v = 4」がその例)は、虚実行では破れることがある。
- **保存則・個数・「ちょうど一度」**(大域的な性質)は、虚実行で調べると偽の反例が出る。

JRF の「「虚実行」を含めたテスト…という考え方がもしかすると有用かもしれない」は、前者についてはそのとおりである。虚実行の集合は大きいが、不変条件の検査は CS ごとの局所的な検査に分解できる(状態の集合を固定点まで広げればよい)。そうすれば、総当りの数の爆発そのものを避けられる。これがスレッド・モジュラー検証の発想である。report2 §6 で、状態の数が指数から多項式に下がること、局所的な不変条件は正しく判定でき個数の性質は偽の警報になることを実測した。
""")

md(r"""
## §8 線形性 ―― コピーと移動、保存則、デッドロック

ここまでの結果を一言でまとめると、**実実行は状態を移動させる実行で、虚実行は状態をコピーしてしまう実行** である。

### 8.1 ロックは「一つしかない物」を受け渡す仕組み

ロックの本質は、共有状態という **一つしかない物** を、プロセスの間で手渡すことにある。手渡した側の手元には何も残らない。ELDE その1 の規則「受け渡しがなければ自分の手元の状態で続ける」は、手渡した後も手元にコピーが残ることを許していた。これが虚実行を生んだ。

この「一度しか使えない」という性質は、論理学では **線形論理**(Girard 1987)が扱う。普通の論理では仮定を何度でも使える(縮約規則)し、使わなくてもよい(弱化規則)。線形論理ではこの二つを制限し、仮定を資源として「ちょうど一度」使う。線形論理には、資源をコピー可能にする様相 $!A$ があり、

- 実実行 = 状態を線形な資源として扱った実行、
- 虚実行 = 状態に $!$ をつけて、コピー(縮約)と破棄(弱化。誰にも読まれない葉)を許した実行、

と言える。

物理では、量子状態は複製できない(複製不可能定理、Wootters & Zurek 1982)。古典的な情報はいくらでもコピーできる。逆向きの対応になるのは面白いが、**本物の実行は複製できない資源の受け渡しとしてしか起きない**、という点は共通している。

### 8.2 ラムダ式との関係(JRF 2011 の直観)

JRF は 2011 年に「lock と(高階論理で使われる)ラムダ式の関係みたいなのが私には見えはじめてる」と書いた。木の見方をとると、これに具体的な形を与えられる。CS $c$ は状態から状態への関数 $f_c$ で、実実行は

$$ f_{v_N}(\cdots f_{v_2}(f_{v_1}(\bot))\cdots) $$

という一本の合成になる。中間の値はどれもちょうど一度使われる(**線形ラムダ項**)。虚実行は、ある中間の値を二度使う項、たとえば

$$ \mathrm{let}\ s = f_{(0,0)}(\bot)\ \mathrm{in}\ \big(\, f_{(0,1)}(s),\ f_{(1,0)}(s) \,\big) $$

で、結果は二つの値の組(二つの世界)になる。$\mathrm{let}$ による **共有** が縮約にあたる。ELDE その1 が数えていたのは、CS を部品とする「共有ありの項」全体、その3 が数えていたのは「線形な項」全体だと言える。

### 8.3 デッドロックは線形性から生まれる

虚実行の世界では **デッドロックが起きない**。ELDE その1 の規則では、lock は決して待たない(誰からも受け渡しがなければ、自分の手元のコピーで続ける)からである。デッドロックは、「一つしかない物」を二人が一つずつ持ったまま、相手の持っている物を待つときに起きる。物がコピーできるなら、待つ必要はない。

つまりデッドロックは、線形な資源に特有の現象である。§9.2 で、2 ロックのデッドロックを進行グラフの上で見る。そこでは、虚実行(禁止領域のすり抜け)を許せばデッドロック領域から抜け出せる。
""")

md(r"""
## §9 ELDE の拡張 ―― 複数ロック・wait_and_lock・確率

### 9.1 拡張の方針

ここまでの考察から、ELDE を拡張するときの方針は次のようになる。

1. **データ構造の中心を lock 仕様から読み出し関係(木)に移す。** 実/虚の判定(定理 1)も、虚の度合い(葉の数 $-1$)もこれで扱える。
2. **lock_limit をなくす。** 同じ大域状態を二度展開しないようにすれば、有限状態のプログラムなら探索は止まる。ELDE その3 の「中途のコンテクストが同じものは二度と実行されないようにプログラムを効率化している」をそのまま一般化したものである。(ただし、ここでの実装はプロセスの局所状態を入力の履歴で代用しているので、ループが無限に続くプログラムでは止まらない。局所状態を明示的に持つ書き方にすれば止まる。)
3. **複数ロック**: ロックごとに共有状態を持たせ、lock 事象だけを分岐点にして総当りする。JRF の「lock のときにのみ調べればよい」は、互いに独立な操作の順序は入れ替えても結果が変わらない、という **トレース**(Mazurkiewicz 1977)の考え方そのもので、Lipton(1975)のリダクションや DRF 保証(Adve & Hill 1990)と同じ前提に立つ(§1.3)。現代の **半順序簡約**(Godefroid 1996、動的半順序簡約 Flanagan & Godefroid 2005)や **ステートレス・モデル検査**(VeriSoft、Godefroid 1997。CHESS、Musuvathi ら 2008)に通じる。
4. **確率**: スケジューラに確率を入れ、実実行に重みをつける(§9.4)。虚実行には「葉の数」で重みをつける(§10.2)。

### 9.2 複数ロックとデッドロック(問 D)

`model_check` は、プロセスを `yield lock("A")` / `yield unlock(s, "A")` のように書き、ロック A, B それぞれに共有状態を持たせて、lock 事象ごとに分岐しながら全実行を調べる。古典的なデッドロックの例として、プロセス 0 は A → B の順に、プロセス 1 は B → A の順にロックを取る。
""")

code(r"""
def pa(out):
    a = yield lock("A")
    b = yield lock("B")
    yield unlock(put(b, "x", get(b, "x", 0) + 1), "B")      # x += 1
    yield unlock(a, "A")

def pb(out):
    b = yield lock("B")
    a = yield lock("A")
    yield unlock(a, "A")
    yield unlock(put(b, "x", get(b, "x", 0) * 10 + 5), "B")  # x = 10x + 5

finals, deadlocks, nstates = model_check([MProc(pa), MProc(pb)], ["A", "B"])
print("調べた大域状態の数:", nstates)
for (ls, outs), trace in finals.items():
    print("正常終了: x =", get(dict(ls)["B"], "x"), "  ロックを取った順:", trace)
for (ls, outs), trace in deadlocks.items():
    print("デッドロック: ロックを取った順:", trace)
""")

code(r"""
def held_after(ev, k):
    h = set()
    for e in ev[:k]:
        if e[0] == "L": h.add(e[1])
        else: h.discard(e[1])
    return h

def deadlock_geometry(ev0, ev1):
    n0, n1 = len(ev0), len(ev1)
    forb = {(x, y) for x in range(n0 + 1) for y in range(n1 + 1)
            if held_after(ev0, x) & held_after(ev1, y)}
    ok = lambda x, y: 0 <= x <= n0 and 0 <= y <= n1 and (x, y) not in forb
    reach = set(); st = [(0, 0)]
    while st:
        p = st.pop()
        if p in reach: continue
        reach.add(p)
        for d in [(1, 0), (0, 1)]:
            q = (p[0] + d[0], p[1] + d[1])
            if ok(*q): st.append(q)
    coreach = set(); st = [(n0, n1)]
    while st:
        p = st.pop()
        if p in coreach: continue
        coreach.add(p)
        for d in [(-1, 0), (0, -1)]:
            q = (p[0] + d[0], p[1] + d[1])
            if ok(*q): st.append(q)
    return n0, n1, forb, reach, coreach

ev0, ev1 = progress_events(pa), progress_events(pb)
n0, n1, forb, reach, coreach = deadlock_geometry(ev0, ev1)
fig, ax = plt.subplots(figsize=(5.5, 5.5))
for x in range(n0 + 1):
    for y in range(n1 + 1):
        if (x, y) in forb:
            ax.add_patch(plt.Rectangle((x - .5, y - .5), 1, 1, color="0.7"))
        elif (x, y) in reach and (x, y) not in coreach:
            ax.add_patch(plt.Rectangle((x - .5, y - .5), 1, 1, color="#f4a6a6"))
        elif (x, y) not in reach:
            ax.add_patch(plt.Rectangle((x - .5, y - .5), 1, 1, color="#a6c8f4"))
lab0 = ["", "L A", "L B", "U B", "U A"]; lab1 = ["", "L B", "L A", "U A", "U B"]
ax.set_xticks(range(n0 + 1)); ax.set_xticklabels(lab0)
ax.set_yticks(range(n1 + 1)); ax.set_yticklabels(lab1)
ax.set_xlim(-.5, n0 + .5); ax.set_ylim(-.5, n1 + .5); ax.set_aspect("equal"); ax.grid(alpha=.3)
ax.set_xlabel("プロセス 0 (A→B)"); ax.set_ylabel("プロセス 1 (B→A)")
ax.set_title("2 ロックの進行グラフ\n灰: 禁止領域  赤: デッドロックに落ちる領域  青: 到達不能", fontsize=10)
plt.show()
""")

md(r"""
灰色の禁止領域は「十字」の形をしている(A を両方が持つ帯と、B を両方が持つ帯の和)。左下の角の赤い点 (1, 1) は「プロセス 0 が A を持って B を待ち、プロセス 1 が B を持って A を待つ」状態で、右にも上にも進めない。ここに入った実実行は終われない。これがデッドロックの幾何学的な姿である。右上の青い点は、どの実行も到達できない領域である。

問 C の「デッドロックの連続・不連続」に一つの答え方をすると、こうなる。実行の道を連続的に変形していくと、ある道は禁止領域の左上側を、ある道は右下側を通る。その間を連続的に移ろうとすると、必ずデッドロック領域を通るか、禁止領域を横切らなければならない。**デッドロック領域は、実行の空間の二つの成分(正常終了の二つの結果 x = 6 と x = 15)の「境目」にあたる。** 有向代数的位相幾何は、この直観を、道の空間の位相として精密にする。

そして §8.3 で見たように、虚実行(禁止領域のすり抜け)を許せば赤い点からも右上へ抜けられる。虚の世界にはデッドロックがない。

### 9.3 wait_and_lock(ELDE その2)の再現

`WLOCK` は ELDE その2 の `wait_and_lock` で、「自分の直前の unlock(最初の lock なら開始)の後に、他のプロセスの CS が一つ以上あるまで待ってからロックを取る」。JRF の例を、実実行だけの探索で再現する。
""")

code(r"""
def w0(out):
    s = yield LOCK
    out.append(get(s, "a")); s = put(s, "a", 1)
    yield unlock(s)
    s = yield WLOCK
    out.append(get(s, "a")); s = put(s, "a", 3)
    yield unlock(s)

def w1(out):
    s = yield WLOCK
    out.append(get(s, "a")); s = put(s, "a", 2)
    yield unlock(s)

for r in enumerate_real([Proc(w0), Proc(w1)]):
    print(spec_str(r.seq), r.status, " 出力:", r.outputs)

def d0(out):
    s = yield WLOCK; yield unlock(s)
def d1(out):
    s = yield WLOCK; yield unlock(s)
print()
print("両方が最初から wait_and_lock する場合:")
for r in enumerate_real([Proc(d0), Proc(d1)]):
    print("  ", spec_str(r.seq) or "(何も実行されない)", r.status)
""")

md(r"""
JRF のその2 の結論「π0υ0→π1λ0,π1υ0→π0λ1 という lock 仕様のときのみ、正常に終了する」と一致する(その3 の記法では P0L0,P1L0,P0L1)。実実行だけを探索すると、待ちで止まった実行は `deadlock` としてそのまま区別できる。その2 は虚実行を含む枠組みだったので、「wait を含むが、その子の仕様に正常終了したものがない場合」という回りくどい判定が必要だった。

### 9.4 確率(問 E)

その2 の「今後の課題」で JRF はこう書いた。

> 二つのプロセスがあって、一方では lock 後ある変数に 1 を足し他方では 1 を引くとする。例えば、それをそれぞれ２度繰り返したあと一方が答えを表示する。(...)「現実」は、lock が一度もブロックされないことが圧倒的に多いとなるだろう。(...) しかし、ここにそれぞれ wait_and_lock を挟むとどうなるか。とたんに中間的な値が「現実」味を帯びてくる。

これを確かめる。スケジューラは「直前に走ったプロセスが続けて走れるなら確率 $1-\varepsilon$ で続け、$\varepsilon$ で他のプロセスに切り換える」とする。$\varepsilon$ が小さいほど、横取り(preemption)の少ない、「現実」に近いスケジュールになる。
""")

code(r"""
def mk_incdec(wait):
    def inc(out):
        for k in range(2):
            s = yield (WLOCK if (wait and k > 0) else LOCK)
            yield unlock(put(s, "v", get(s, "v", 0) + 1))
        s = yield LOCK
        out.append(get(s, "v", 0))             # 表示
        yield unlock(s)
    def dec(out):
        for k in range(2):
            s = yield (WLOCK if (wait and k > 0) else LOCK)
            yield unlock(put(s, "v", get(s, "v", 0) - 1))
    return [Proc(inc), Proc(dec)]

epss = np.logspace(-3, np.log10(0.5), 30)
fig, axes = plt.subplots(1, 2, figsize=(12, 4), sharey=True)
for ax, wait in zip(axes, [False, True]):
    ps = mk_incdec(wait)
    vals = sorted({r.outputs[0][0] for r in enumerate_real(ps) if r.outputs[0]})
    curves = {v: [] for v in vals}
    for eps in epss:
        d = scheduled_distribution(ps, eps, lambda o, s: o[0][0])
        for v in vals:
            curves[v].append(d.get(v, 0.0))
    for v in vals:
        ax.semilogx(epss, curves[v], label=f"表示 = {v}", lw=2)
    ax.set_xlabel("切り換え確率 ε"); ax.grid(alpha=.3); ax.legend()
    ax.set_title("wait_and_lock あり" if wait else "wait_and_lock なし(普通の lock)")
    print(("あり" if wait else "なし"), "実実行:", [(spec_str(r.seq), r.outputs[0]) for r in enumerate_real(ps)][:4], "...")
axes[0].set_ylabel("確率")
plt.tight_layout(); plt.show()
""")

md(r"""
- 普通の lock では、$\varepsilon\to 0$ で表示は 2(足す方が全部先)か 0(引く方が先、または表示の前に全部終わる)にほぼ限られ、中間の 1 は消えていく。場合の数としては 1 もあるのに、「現実」の確率はほとんどない。JRF の「「現実」にはまともな「確率」が存在しない」はこのことだろう。
- wait_and_lock を挟むと、両端の値(2)は場合の数から消え、中間の 1 が $\varepsilon\to0$ でも半分近い確率を持つ。**wait_and_lock は場合の数を減らす(枝刈り)と同時に、確率の重みを大きく動かす。** JRF の「その場合の数以上にとても大きな「現実」も枝刈りしたとできるのかもしれない」の数値的な裏づけになる。

この問題は、その後の並列プログラムのテスト研究で中心的な主題になった。

- **文脈切り換えの回数を制限した探索**(Musuvathi & Qadeer 2007): 実際のバグの多くは横取りが 2 回程度以下のスケジュールで現れる。$\varepsilon$ が小さい「現実」の確率の重みと同じ発想である。
- **PCT**(Burckhardt ら 2010): 少数の「優先度変更点」を乱数で入れるスケジューラで、深さ $d$ のバグを見つける確率に下界を与える。JRF がその1 で書いた「sleep とはエラーの確率に干渉する操作ではないか」は、ちょうど PCT の優先度変更点(わざと遅らせる点)の役割にあたる。
""")

md(r"""
## §10 虚数との関係

ここからが問 F、「虚実行」を「虚数」とどう関係づけられるか、である。言葉が似ているだけでなく、構造の上でも対応がつくことを、三つの方向から示す。

### 10.1 「虚」を経由して「実」に戻る

JRF は『宗教学雑考集』(2025)の「虚数と超ひも理論」の節でこう書いている。

> 虚数とは単に「2乗するとマイナスになる数」だが、それは現実には存在しないバーチャルな量である。しかし、それを物理学の理論に組み込むことで、説明が容易になることが多かった。バーチャルな「虚」の理論を経由して計算しても、結果、「虚」が外れた現実に解が戻ってくれば、それが正しい現実の解になるのだ。
>
> 虚数に限らず、ある理論を「仮設」して、それを経由して現実を説明するようなそのような理論を「虚」の理論と私は呼ぶ。

歴史的にも、虚数はまさにこの形で現れた。16 世紀、ボンベリ(Bombelli 1572)は 3 次方程式 $x^3 = 15x + 4$ にカルダノの公式を当てはめ、

$$ x = \sqrt[3]{2+\sqrt{-121}} + \sqrt[3]{2-\sqrt{-121}} $$

を得た。実数の答え $x=4$ があるのに、途中で負の数の平方根を通らないと公式が使えない。ボンベリは $(2+\sqrt{-1})^3 = 2+\sqrt{-121}$ に気づき、$x = (2+\sqrt{-1}) + (2-\sqrt{-1}) = 4$ と「実」に戻った。
""")

code(r"""
z = (2 + 1j) ** 3
print("(2+i)^3 =", z)
x = (2 + 1j) + (2 - 1j)
print("x =", x, "  検算 x^3 - 15x - 4 =", x**3 - 15*x - 4)
""")

md(r"""
ELDE にもこれと同じ形の出来事があった。JRF はその3 で、虚実行を含む「失敗作」の `elde_0.pl` を、実実行だけを数える `elde_2.pl` の検算に使った(`elde_0_and_2.pl`)。「怪我の功名」と JRF は書いたが、これは「虚の理論を経由して実を確かめる」ことの小さな実例である。

以下では、虚実行を経由して実実行を取り出す計算を、文字どおり虚数を使って行う。

### 10.2 枝分かれの母関数と単位円上の積分

定理 1 により、虚実行 $E$ の **葉の数** $\ell(E)$ は「世界の数」で、$\ell(E)=1$ が実実行である。そこで、虚実行の集合(ここでは ELDE その1 の全体 E0)の上で母関数

$$ G(x) = \sum_{E\in \mathrm{E0}} x^{\ell(E)-1} $$

を考える。$x$ は「余分な世界一つあたりの重み」である。

- $x = 1$: $G(1) = |\mathrm{E0}|$。ELDE その1 が数えていたもの。
- $x = 0$: $G(0) = $ 実実行の数。ELDE その3 が数えていたもの。
- $0<x<1$: 虚実行を「虚の度合い」に応じて割り引いて数える。その1 とその3 を連続的につなぐ。

$G$ は多項式なので、定数項 $G(0)$ は単位円上の平均で取り出せる(コーシーの積分公式):

$$ G(0) = \frac{1}{2\pi}\int_0^{2\pi} G(e^{i\theta})\, d\theta = \frac{1}{K}\sum_{k=0}^{K-1} G(\omega^k),\quad \omega = e^{2\pi i/K},\ K > \deg G . $$

右辺の各項 $G(\omega^k)$ は複素数で、虚実行の寄与 $\omega^{k(\ell-1)}$ は単位円上をぐるりと回る。平均をとると虚実行の寄与は互いに打ち消し合い、実実行だけが残る。**虚実行の和に複素数の位相をつけて足し合わせると、干渉によって実実行だけが残る。** 物理学の経路積分で、古典的でない経路の寄与が位相の打ち消し合いで消えていくのと同じ形である(ただし物理では打ち消し合いは近似的で、ここでは厳密)。

JRF の最初の例では、E0 は 6 通りで、実が 3 通り、葉が 2 の虚が 3 通りだから $G(x) = 3 + 3x$、$K=2$ で $\{G(1) + G(-1)\}/2 = (6 + 0)/2 = 3$ である。$x=-1$ では、虚実行がちょうど $-1$ の重みを持って実実行を打ち消す。表示される値ごとに分けると次のようになる。
""")

code(r"""
E0_ex = [r for r in enumerate_imag(procs) if is_elde0(r.rf)]
by_out = defaultdict(list)
for r in E0_ex:
    by_out[r.outputs[1][0]].append(r)
print("表示ごとの母関数 G_o(x) = Σ x^(ℓ-1):")
for o, rs in by_out.items():
    poly = leaf_poly(rs)
    val, vals = circle_filter(poly, K=2)
    print(f"  表示 {o!s:>5}: 係数 {dict(sorted(poly.items()))}   G_o(1) = {poly_eval(poly, 1)}, "
          f"G_o(-1) = {poly_eval(poly, -1)},  平均 = {val.real:.0f}  (実実行の数)")
""")

md(r"""
表示 undef の行では $G(-1) = -1$ になる。$x=-1$ を「重み」と見ると、虚実行に **負の確率** を割り当てて実実行を取り出したことになる。ファインマンの「負の確率」(Feynman 1987)や量子力学の Wigner 関数の負の値と同じ種類のものである。

もう少し大きな例(二段階の加算、E0 が 1107 通り)で、$G(e^{i\theta})$ が複素平面上に描く曲線と、その平均を見る。
""")

code(r"""
ps = [Proc(mk_twophase(2)), Proc(mk_twophase(2))]
E0_big = [r for r in enumerate_imag(ps) if is_elde0(r.rf)]
poly = leaf_poly(E0_big)
print("葉の数 -1 の分布:", dict(sorted(poly.items())))
print("G(1) =", poly_eval(poly, 1), " (ELDE0 の総数)")
K = max(poly) + 1
val, vals = circle_filter(poly, K)
print(f"K = {K} 点の単位円平均 = {val.real:.6f} {val.imag:+.1e}i   実実行の数 = {len(enumerate_real(ps))}")

th = np.linspace(0, 2 * np.pi, 400)
curve = np.array([poly_eval(poly, np.exp(1j * t)) for t in th])
fig, axes = plt.subplots(1, 2, figsize=(12, 4.8))
ax = axes[0]
ax.plot(curve.real, curve.imag, lw=1.5)
pts = np.array(vals)
ax.plot(pts.real, pts.imag, "o", color="crimson", label=f"G(ω^k), k=0..{K-1}")
ax.plot([val.real], [val.imag], "*", ms=16, color="k", label="平均 = 実実行の数")
ax.axhline(0, color="0.5", lw=.5); ax.axvline(0, color="0.5", lw=.5)
ax.set_aspect("equal"); ax.legend(fontsize=8); ax.set_title(r"$G(e^{i\theta})$ の描く曲線(二段階加算の E0)")
ax = axes[1]
xs = np.linspace(0, 1, 101)
outs = defaultdict(list)
for r in E0_big:
    outs[tuple(sorted(get(s, "v", 0) for s in world_finals(r)))].append(r)
# 実実行の最終 v ごとに、x で割り引いた重み
for v in [2, 3, 4]:
    sel = [r for r in E0_big if any(get(s, "v", 0) == v for s in world_finals(r))]
    num = [sum(x ** (len(leaves(r.rf)) - 1) for r in sel) for x in xs]
    den = [poly_eval(poly, x) for x in xs]
    ax.plot(xs, np.array(num) / np.array(den), label=f"ある世界で v = {v}")
ax.set_xlabel("x(余分な世界一つあたりの重み)"); ax.set_ylabel("割合")
ax.set_title("x = 1 が ELDE その1、x = 0 が ELDE その3"); ax.grid(alpha=.3); ax.legend(fontsize=8)
plt.tight_layout(); plt.show()
""")

md(r"""
右の図は、$x$ を 1 から 0 へ動かすと、虚実行の世界観(その1)から実実行の世界観(その3)へ連続的に移ることを示す。$x$ は統計力学の **活量**(fugacity)のような働きをする。$x$ を確率の重みと見れば、「虚実行を少しだけ許すテスト」が定義できる。

**注意(実数でも足りるか).** 定数項の取り出しは、実数の点 $x_1,\dots,x_K$ での値からラグランジュ補間でも計算できる(係数には負の数が出る)。だから「虚数でなければできない」わけではない。2021 年に、量子力学は実数だけでは書けないことが実験で示された(Renou ら 2021。JRF も『宗教学雑考集』でこの記事を引いている)。ここでの虚数は、そういう意味での不可欠さではなく、「位相を回して平均する」という計算の自然さの点で現れている。

### 10.3 トンネル効果 ―― 禁止領域の中の虚数

定理 3 によれば、虚実行は進行グラフの禁止領域をすり抜ける道である。量子力学では、粒子が古典的に入れない領域(ポテンシャルの壁 $V > E$)に染み込み、通り抜けることがある(トンネル効果)。そこでは波数

$$ k = \frac{\sqrt{2m(E - V)}}{\hbar} $$

が **虚数** になり、波は振動せずに指数関数的に減衰する。トンネルの確率は壁の厚さに対して指数関数的に小さい。さらに、トンネルする経路は **虚時間** $t = -i\tau$ の中での古典的な運動(インスタントン、Coleman 1977)として計算できる。

ELDE に当てはめると、「禁止領域の中を進む実行は、実時間の実行ではない」。§10.2 の重み $x$ を「禁止領域の中を一歩進むごとの減衰」と読みかえれば、トンネルの深さに応じて指数関数的に小さくなる重みを虚実行につけることになる。これはまだ類比の段階だが、**「実行の可能性の空間で、本物の実行が通れない領域」に虚数が現れる** という対応は、物理と ELDE で同じ形をしている。

### 10.4 時間ループと虚数単位 ―― 嘘つきの値は $i$

虚実行の階層(§5.3)の一番上は「時間ループ」L であった。CS が、自分より後に書かれる状態、さらには **自分自身の出力** を入力として読む。こういう実行が意味を持つのは、ループに沿った状態が **自己無撞着**(一周して元に戻る)ときだけである。CS $c_1,\dots,c_n$ のループなら、状態 $s$ は

$$ s = f_{c_n}\circ\cdots\circ f_{c_1}(s) $$

を満たさなければならない。不動点がなければ、その時間ループは起こりえない(「親殺しのパラドックス」)。不動点が無数にあれば、何でも起こりうる(「ブートストラップのパラドックス」)。時間旅行の物理でいう **ノヴィコフの自己無撞着原理**(Friedman ら 1990)や、Deutsch(1991)の閉じた時間的曲線のモデルは、この不動点の条件を課すものである。

ここで、状態が実数 $x$ で、CS が **タンジェントの加法定理** で $x$ を更新する例を考える。

$$ f_\theta(x) = \frac{x + \tan\theta}{1 - x\tan\theta} \qquad (x = \tan\alpha \text{ なら } f_\theta(x) = \tan(\alpha+\theta)) $$

これは角度を $\theta$ だけ回す操作である。実実行ではループ $s_{k+1} = f_\theta(s_k)$ を何度も回し、$x$ は $\tan(\alpha + k\theta)$ と実数の範囲でぐるぐる回る。ところが「CS が自分の出力を読む」時間ループにすると、$x = f_\theta(x)$ から

$$ x(1 - x\tan\theta) = x + \tan\theta \iff x^2 = -1 \iff x = \pm i $$

で、**$\theta$ によらず、自己無撞着な状態は虚数単位 $\pm i$ しかない。** 実実行ではいつまでも回り続けるものを、時間を止めて(一つの状態で)表そうとすると、虚数が出てくる。

さらに見通しをよくするために、$w = (x - i)/(x + i)$(ケイリー変換)で実数直線を単位円に写す。$x = \tan\alpha$ は $w = -e^{2i\alpha}$ に写り、$f_\theta$ は単位円の **回転** $w\mapsto e^{2i\theta}w$ になる。実実行は円周上を回り、$x=i$ は円の **中心** $w=0$ に写る。虚数単位は、回り続ける実実行の「回転の中心」である。

**虚の不動点での微分が、実実行の回転の速さを与える.** $t=\tan\theta$ とおくと $f_\theta'(x) = (1+t^2)/(1-tx)^2$ で、不動点 $x=i$ では

$$ f_\theta'(i) = \frac{1+t^2}{(1-it)^2} = \frac{(1-it)(1+it)}{(1-it)^2} = \frac{1+it}{1-it} = \frac{\cos\theta + i\sin\theta}{\cos\theta - i\sin\theta} = e^{2i\theta} $$

となる。絶対値が 1 なので、$i$ は引き寄せも突き放しもしない「中立」な不動点で、その偏角 $2\theta$ が、実実行がケイリー変換後の円の上を一回の CS で回る角度にちょうど等しい(上の回転 $w\mapsto e^{2i\theta}w$ の倍率そのもの)。したがって、実実行が何回の CS で元に戻るか(周期)は $e^{2in\theta}=1$ となる最小の $n$ で、**時間ループの虚の解だけを見て、実実行の振動の周期が読める**。線形の力学系で、複素固有値の偏角が振動の周期を決めるのと同じ形である。この話は report3(時間ループと最適化)§1・§2 で一般のメビウス変換や発振条件に広げ、実実行が元に戻るのは乗数が 1 の冪根のときに限ることを示した(report3 の定理 F′)。
""")

code(r"""
theta = 0.7
M = mobius_rot(theta)
print("θ = 0.7 の回転 f の自己無撞着解(長さ 1 のループ):", mobius_fixed_points(M))
h = 1e-6
fprime = (mobius_apply(M, 1j + h) - mobius_apply(M, 1j - h)) / (2 * h)   # 数値微分
print(f"f'(i) = {fprime:.6f},  e^(2iθ) = {cmath.exp(2j * theta):.6f}")
for n in [2, 3, 5]:
    th = math.pi / n
    for L in sorted({1, n - 1, n}):
        fp = mobius_fixed_points(mobius_power(mobius_rot(th), L))
        desc = "すべての x(ブートストラップ)" if fp == "all" else ", ".join(f"{z:.3f}" for z in fp)
        print(f"  θ = π/{n}, ループの長さ {L}: {desc}")

cay = lambda x: (x - 1j) / (x + 1j)
fig, axes = plt.subplots(1, 2, figsize=(11, 5))
ax = axes[0]
x = 0.3; ks = range(12); xs_ = []
for k in ks:
    xs_.append(x); x = mobius_apply(M, x)
ax.plot(list(ks), xs_, "o-"); ax.set_ylim(-8, 8); ax.grid(alpha=.3)
ax.set_xlabel("CS の回数 k"); ax.set_ylabel("x_k"); ax.set_title(r"実実行: $x_{k+1} = f(x_k)$ は実数の中で回り続ける")
ax = axes[1]
t = np.linspace(0, 2 * np.pi, 300)
ax.plot(np.cos(t), np.sin(t), color="0.6")
ws = [cay(v) for v in xs_]
ax.plot([w.real for w in ws], [w.imag for w in ws], "o-", label="実実行の軌道(ケイリー変換後)")
ax.plot([0], [0], "*", ms=18, color="crimson", label="x = i(時間ループの解)= 中心")
ax.set_aspect("equal"); ax.legend(fontsize=8, loc="lower left"); ax.set_title("w = (x - i)/(x + i): 回転の中心が i")
plt.tight_layout(); plt.show()
""")

md(r"""
**ELDE の言葉で確かめる.** この時間ループは、ELDE の部品でそのまま書ける。2 プロセスがそれぞれ CS を一つ持ち、P0 は x を角度 $\theta$ だけ、P1 は $\varphi$ だけ回すとする。普通の実実行は CS を順に走らせるだけだが、rf を $\mathrm{rf}(0,0)=(1,0)$, $\mathrm{rf}(1,0)=(0,0)$(互いに相手の出力を読む、§5.3 の L)にすると、どちらから走らせても入力が決まらない。ELDE の再生でできるのは、候補の状態を仮定して、一周して戻るかを確かめることだけである。§5.5 の `consistent_executions` は候補を有限集合から総当りするので、$x$ が実数(や複素数)のこの例にはそのまま使えない。そこで、その中の検査だけを取り出した `is_consistent` を使い、候補(上で解いた一周の写像の不動点 $\pm i$ も含める)を一つずつ確かめる。
""")

code(r"""
def rot_proc(theta):
    t = math.tan(theta)
    def p(out):
        s = yield LOCK
        x = get(s, "x", 0.0)
        yield unlock(put(s, "x", (x + t) / (1 - x * t)))
    return Proc(p)

P0, P1 = rot_proc(0.7), rot_proc(0.4)
print("実実行(初期 x = 0.3):", [round(get(r.finals[r.seq[-1][0]], "x"), 4)
                             for r in enumerate_real([P0, P1], init=(("x", 0.3),))])
rf_loop = {(0, 0): (1, 0), (1, 0): (0, 0)}      # 互いに相手の出力を読む(階層 L)
fps = mobius_fixed_points(mobius_compose(mobius_rot(0.4), mobius_rot(0.7)))
print("一周の写像の不動点(解析的に求めたもの):", [f"{z:.3f}" for z in fps])
close = lambda a, b: abs(get(a, "x") - get(b, "x")) < 1e-9
for x in [0.0, 0.3, 1.0, -2.0] + list(fps):
    s0 = (("x", x),)
    u0 = P0.replay((s0,))[1][0]          # P0 が s0 を読んで置く状態 = P1 が読む状態
    ok = is_consistent([P0, P1], rf_loop, (1, 1), {(0, 0): s0, (1, 0): u0}, eq=close)
    print(f"   P0 が x = {complex(x):.3f} を読む → 自己無撞着: {ok}")
""")

md(r"""
実数の候補はどれも戻らず、整合するのは $x=\pm i$ だけである(θ+φ が π の倍数でない限り、実数の解はない)。§5.5 で見たとおり、**時間ループの実行は「走らせて決まる」のではなく「整合するものだけが存在する」**。この例では、整合する状態が実数の中になく、虚数単位として現れる。

$x=\tan\alpha$ は $\alpha$ について周期 $\pi$ なので、$\theta = \pi/n$ の回転を $n$ 回施すと元に戻る(ケイリー変換後の円をちょうど一周する)。このように、ループの長さがちょうど一周分のときだけ、すべての実数が自己無撞着になる(ブートストラップ型)。それ以外の長さでは解は $\pm i$ だけである(親殺し型。実数の解はない)。

**嘘つきのパラドックス.** 特に $\theta = \pi/2$(4 分の 1 回転)なら $f(x) = -1/x$ で、$x=0$ を「真」、$x=\infty$ を「偽」とすると、$f$ は真と偽を入れ替える **否定** になる($f(0)=\infty$, $f(\infty)=0$)。「この文は偽である」という嘘つきの文は、否定が自分自身を読む時間ループ $x = -1/x$ であり、真にも偽にも定まらない。実実行(時間に展開した評価)では真・偽・真・偽…と振動する。そしてこのループの自己無撞着な値は $x^2=-1$、つまり **$i$** である。一方「この文は真である」(否定を二度通る長さ 2 のループ $f\circ f = \mathrm{id}$)は、どの値でも自己無撞着になる(真と言っても偽と言ってもよい)。嘘つきと正直者の違いが、親殺し型とブートストラップ型の違いとして現れる。

自己言及のパラドックスと虚数を結びつける考えは古くからある。スペンサー=ブラウン『形式の法則』(1969)は、自己を再参照する式の値を「虚の値」と呼び、時間の中の振動として解釈した。カウフマン(Kauffman 1987)は、振動 $[+1,-1,+1,\dots]$ とその半周期ずらしを使って、論理の上で $i^2=-1$ を満たす「虚の値」を作った。ここでの見方は、それを ELDE の言葉で言い直したものである。**嘘つきの文の値 $i$ は、実実行では振動として時間の中に展開されるものを、時間ループ(虚実行の極限)で一つの状態に押し込めたときの値である。** この振動を実際に作る回路が、否定を奇数個輪につないだリング発振器で、report3 §2.3(定理 R)で扱った。

### 10.5 まとめ: 虚実行と虚数の対応表

| | 数 | 実行 |
|---|---|---|
| 実のもの | 実数 | 実実行(状態の移動、一本道) |
| 拡張 | 複素数 | 虚実行(状態のコピー、木) |
| 捨てた制約 | 「2 乗は 0 以上」 | 「一つの状態は一度だけ使う」(線形性) |
| 保たれる局所規則 | 四則演算の法則 | 各 CS は実在する過去の状態を読む |
| 「虚」を経由して「実」に戻る | ボンベリの 3 次方程式 | その1 でその3 を検算、葉の母関数の円周積分 |
| 禁止された領域 | トンネル効果の虚の波数 | 進行グラフの禁止領域のすり抜け |
| 自己無撞着 | $x^2=-1$ の解 $i$ | 時間ループ $x = -1/x$ の状態 |
| 回転 | $e^{i\theta}$ | 回り続ける実実行の、回転の中心 |
""")

md(r"""
## §11 まとめと今後の課題

### 11.1 JRF の問いへの答え

- **問 A(判定)**: 実実行 ⇔ 読み出し関係の木で、どの状態も高々一度しか読まれない ⇔ 葉が一つ(定理 1)。判定は線形時間でできる。
- **問 B(意味)**: 虚実行は、局所的な制約(実在する過去の状態を読む)はすべて満たし、大域的な線形性(一つの状態は一度だけ)だけを破る実行である。存在しない出来事を参照するほかの cut とは、はっきり区別できる(§5.4)。帰納的な不変条件の検査には健全で、保存則の検査では偽の反例を生む(§7)。
- **問 C(連続性)**: 2 プロセスでは、虚実行は進行グラフの禁止領域をすり抜ける道である(定理 3)。道が禁止領域を通れば必ず虚になることは、プロセスがいくつでも成り立つ。デッドロック領域は、実行の空間の成分の境目にある(§9.2)。有向代数的位相幾何がこれを精密にする。
- **問 D(複数ロック)**: lock 事象だけを分岐点にしたモデル検査器で、デッドロックの検出と、その幾何学的な姿を示した(§9.2)。虚の世界にはデッドロックがない(§8.3)。
- **問 E(確率)**: 横取りの少ないスケジューラでは中間的な結果の確率が消え、wait_and_lock を挟むと中間的な結果が現実味を帯びる、という JRF の直観を数値で確かめた(§9.4)。
- **階層の上**: まだ書かれていない状態まで読んでよいとすると(時間逆行・時間ループ)、実行は前から計算できず、一周して整合するものだけが存在する(定理 4、§5.5)。時間ループの整合する状態が虚数単位になる例が §10.4 である。
- **問 F(拡張概念)**: 虚実行と虚数の間に、捨てた大域制約・保たれる局所規則・「虚」を経由した計算・禁止領域・自己無撞着・回転、の各点で対応がつく(§10.5)。

### 11.2 今後の課題

0.1.0 で最初に挙げた「定理 2 と定理 3(i) の完全な証明」は、Lean による形式的証明として済ませた。定理 4 も 0.4.0 で Lean で証明した。0.3 で挙げた課題のうち、後続のレポートで扱ったものには、その行き先を書く。

1. **2 プロセスの仕様数 $f(2a,2b)$ の閉じた式と漸近挙動**。→ 0.4.0・0.4.2 で解いた(§5.2)。$f(2a,2b)$ は三項係数 $[x^{2b}](1+x+x^2)^{a+b}$(OEIS A027907)で、対角線は中心三項係数(A002426、A082758)、$f(2a,2a) \sim \sqrt{3/(8\pi a)}\,9^a$。既知の数である。3 プロセス以上の数え上げは残る。
2. **合流(マージ)のある虚実行**。虚実行は「枝分かれはするが合流しない」歴史である。二つの世界の状態を合流させる操作を許すと、楽観的並行制御やスナップショット分離(write skew などの異常)、分散システムの結果整合性や CRDT(Shapiro ら 2011)の理論につながる。git の履歴(分岐と合流)や、コピーの上で並列に作業する AI エージェントも同じ形をしている。→ report1(虚実行と合流): 合流が直列実行と区別できない条件(定理 A)と、スナップショット分離の危険構造(定理 B)を Lean で証明した。
3. **部品に意味を与える**。並列プログラムをプロセスごとに理解するには、プロセス単体の意味を「相手がどんな状態を渡してきても」で定める必要があり、そこには実際の相手が渡さない虚の入力が含まれる(Brookes の完全抽象意味論、rely-guarantee)。実実行だけでは並列合成について閉じないこと、閉じるために足りる最小の虚は何か(E0 か)を調べる。§7.3 のスレッド・モジュラー検査による計算量の削減もここに入る。→ report2: 実実行だけでは閉じず(定理 C)、スケジュールを選べる検査者には各 lock に一つずつの虚の入力が必要十分(定理 H、E0 の形)、記憶のある相手は「外れたときに潰せる」虚の入力の列を見分ける(定理 J・K)。
4. **複数ロックの虚実行**。ロックごとに別々の木を持つ虚実行と、デッドロック領域のすり抜けの関係。
5. **重み $x$ と最適化**。JRF は 2025 年に「最適化にそれをどうつなげればいいのかはまだぜんぜんわからない」と書いた。一つの道筋は整数計画法の **緩和**(LP 緩和)で、虚実行は実行の空間の「線形性の緩和」、§10.2 の $x$ はその緩和の強さを連続的に調整するパラメータになっている。遺伝的アルゴリズムの選択、粒子フィルタのリサンプリング、ビームサーチは、どれも状態を「コピーし、捨てる」探索で、虚実行の木を育てて最後に一本の実の道を選ぶ過程と見られる。§10.4 の時間ループの周期もここで一般化する。→ report3: 時間ループの周期と乗数(定理 F・F′・F″・G)、コピーと破棄の探索で最適な $x$ が地平で切り換わること。
6. **継続(call/cc)との関係**。このノートの実装はプロセスを Python のジェネレータで書いた。ジェネレータは「一度しか再開できない継続」なので、虚実行を作るたびにプロセスを最初から再実行している。一度しか使えない継続が実実行に、何度でも再開できる継続(call/cc)が虚実行に対応している、と見られる。JRF は 2011 年に Haskell の callCC で goto や「排中律」を書いており(《Haskell の callCC で goto を作る》《時間泥棒の夕べ》)、そこで捨てられる「死んだ夢の世界」は虚実行の葉にあたる。→ report2 §8: 再実行は何度でも再開できる継続を作る方法と同じで、世界の数 = 1 + 継続を余分に再開した回数(定理 E)。線形な継続 = 実実行、継続のコピー = 虚実行 = 古典論理(状態が継続の中にしかない場合)。ただし、複数のプロセスが状態を受け渡す ELDE の設定では、一つの虚実行を作るのに継続のコピーは要らず、状態の値のコピーで rf ∪ po が循環しないもの(I 以下)がすべて作れる。ELDE の再実行が要ったのは、たくさんの世界を途中まで共有して総当りするためだった(report2 定理 E′)。

### 11.3 教材として

`kj_core.py` は、Python のジェネレータ(`yield`)を使って数百行で書いた小さなモデル検査器である。並列処理の総当り、実行の数え方、「実」と「虚」の区別、デッドロックの幾何、スケジューラの確率までを、手元で動かしながら確かめられる。並列処理を学ぶ人の教材としても使えるだろう。
""")

md(r"""
## 参考文献

### JRF の文献(本稿の出発点)

- JRF《Exhaustive Lock Dependency Emulator その１ 並列処理の総当り》JRF のソフトウェア Tips, 2011-06-20(追記 2018-04-06)。 http://jrf.cocolog-nifty.com/software/2011/06/post-1.html
- JRF《Exhaustive Lock Dependency Emulator その２ wait_and_lock》同, 2011-07-01。 http://jrf.cocolog-nifty.com/software/2011/07/post.html
- JRF《Exhaustive Lock Dependency Emulator その３ 修正とチェック》同, 2018-04-13。 http://jrf.cocolog-nifty.com/software/2018/04/post-1.html (配布物 elde.zip: `elde_0.pl`, `elde_0wl.pl`, `elde_2.pl`, `elde_0_and_2.pl`)
- JRF《組み合わせと順列の数え上げのアルゴリズム》同, 2018-04-11。 http://jrf.cocolog-nifty.com/software/2018/04/post.html
- JRF《Haskell の callCC で goto を作る》同, 2011-01-20。 http://jrf.cocolog-nifty.com/software/2011/01/post-2.html
- JRF《時間泥棒の夕べ − 排中律と call/cc》JRF の私見：雑記, 2011-01-20。 http://jrf.cocolog-nifty.com/column/2011/01/post-1.html
- JRF「ひとこと」[cocolog:69727785] 2011-09-08(lock とラムダ式)、[cocolog:89156596] 2018-04-06(《ショック。ELDE に大きなミスを発見。実際にはありえない「虚実行」を数え上げてた。》 http://jrf.cocolog-nifty.com/statuses/2018/04/post-683a.html )、[cocolog:89194943] 2018-04-13、[cocolog:93692583] 2022-08-24(『GEB』の超自然数と拡張概念)、[cocolog:95231673] 2025-01-12(最適化の拡張)。
- JRF『宗教学雑考集 易理・始源論・神義論』第 1.0 版, 2025-03-11(「虚数と超ひも理論」の節)。
- JRF & Claude Opus 5.5『虚実行と合流』(report1)、『虚実行があるからこそ解ける問題 ―― 部品の意味と計算量』(report2)、『時間ループと最適化』(report3)。本稿の後続のレポート。

### 並列処理・検証

- E. W. Dijkstra, "Cooperating sequential processes", EWD123, 1965/1968.
- E. G. Coffman, M. J. Elphick, A. Shoshani, "System deadlocks", *ACM Computing Surveys* 3(2), 67–78, 1971.
- L. Fajstrup, E. Goubault, E. Haucourt, S. Mimram, M. Raussen, *Directed Algebraic Topology and Concurrency*, Springer, 2016.
- L. Lamport, "How to make a multiprocessor computer that correctly executes multiprocess programs", *IEEE Trans. Computers* C-28(9), 1979(逐次一貫性)。
- M. Herlihy, J. Wing, "Linearizability: a correctness condition for concurrent objects", *ACM TOPLAS* 12(3), 1990.
- P. B. Gibbons, E. Korach, "Testing shared memories", *SIAM J. Computing* 26(4), 1208–1244, 1997(観測から逐次一貫性を判定する問題は一般に NP 完全。本稿の定理 1 が簡単なのは、読み出し関係がわかっているから)。
- D. Mazières, D. Shasha, "Building secure file systems out of Byzantine storage", *PODC* 2002, 108–117(fork 一貫性)。
- A. Mazurkiewicz, "Concurrent program schemes and their interpretations", DAIMI PB-78, Aarhus University, 1977(トレース)。
- P. Godefroid, *Partial-Order Methods for the Verification of Concurrent Systems*, LNCS 1032, Springer, 1996.
- C. Flanagan, P. Godefroid, "Dynamic partial-order reduction for model checking software", *POPL* 2005.
- R. J. Lipton, "Reduction: a method of proving properties of parallel programs", *Communications of the ACM* 18(12), 717–721, 1975.
- S. V. Adve, M. D. Hill, "Weak ordering — a new definition", *Proc. 17th ISCA*, 2–14, 1990(DRF 保証)。
- P. Godefroid, "Model checking for programming languages using VeriSoft", *POPL* 1997, 174–186(ステートレス・モデル検査)。
- M. Musuvathi, S. Qadeer, T. Ball, G. Basler, P. A. Nainar, I. Neamtiu, "Finding and reproducing Heisenbugs in concurrent programs", *OSDI* 2008, 267–280(CHESS)。
- M. Chalupa, K. Chatterjee, A. Pavlogiannis, N. Sinha, K. Vaidya, "Data-centric dynamic partial order reduction", *Proc. ACM Program. Lang.* 2(POPL), Article 31, 2018(読み出し関係にもとづく探索)。
- P. A. Abdulla, M. F. Atig, B. Jonsson, M. Lång, T. P. Ngo, K. Sagonas, "Optimal stateless model checking for reads-from equivalence under sequential consistency", *Proc. ACM Program. Lang.* 3(OOPSLA), Article 150, 2019.
- J. Alglave, L. Maranget, M. Tautschnig, "Herding cats: modelling, simulation, testing, and data mining for weak memory", *ACM TOPLAS* 36(2), Article 7, 2014(候補実行と一貫性の公理)。
- H.-J. Boehm, B. Demsky, "Outlawing ghosts: avoiding out-of-thin-air results", *MSPC* 2014(out-of-thin-air 問題)。
- M. Batty, K. Memarian, K. Nienhuis, J. Pichon-Pharabod, P. Sewell, "The problem of programming language concurrency semantics", *ESOP* 2015, LNCS 9032, 283–307.
- M. Musuvathi, S. Qadeer, "Iterative context bounding for systematic testing of multithreaded programs", *PLDI* 2007.
- S. Burckhardt, P. Kothari, M. Musuvathi, S. Nagarakatte, "A randomized scheduler with probabilistic guarantees of finding bugs", *ASPLOS* 2010(PCT)。
- P. Cousot, R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", *POPL* 1977.
- E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, "Counterexample-guided abstraction refinement", *CAV* 2000.
- C. Flanagan, S. Qadeer, "Thread-modular model checking", *SPIN* 2003, LNCS 2648, doi:10.1007/3-540-44829-2_14.
- S. Owicki, D. Gries, "An axiomatic proof technique for parallel programs I", *Acta Informatica* 6, 1976.
- C. B. Jones, "Tentative steps toward a development method for interfering programs", *ACM TOPLAS* 5(4), 1983(rely-guarantee)。
- M. Shapiro, N. Preguiça, C. Baquero, M. Zawirski, "Conflict-free replicated data types", *SSS* 2011.
- R. Milner, *Communicating and Mobile Systems: the π-Calculus*, Cambridge University Press, 1999.

### 論理・数学・物理

- J.-Y. Girard, "Linear logic", *Theoretical Computer Science* 50, 1987.
- L. de Moura, S. Ullrich, "The Lean 4 theorem prover and programming language", *CADE-28*, LNCS 12699, 2021. / The mathlib Community, "The Lean mathematical library", *CPP* 2020(付録の証明に使用)。
- W. K. Wootters, W. H. Zurek, "A single quantum cannot be cloned", *Nature* 299, 1982.
- R. Bombelli, *L'Algebra*, 1572.
- G. Spencer-Brown, *Laws of Form*, Allen & Unwin, 1969.
- L. H. Kauffman, "Imaginary values in mathematical logic", *Proc. 17th International Symposium on Multiple-Valued Logic*, 282–289, 1987.
- D. R. ホフスタッター『ゲーデル，エッシャー，バッハ ―― あるいは不思議の環』野崎昭弘・はやしはじめ・柳瀬尚紀 訳, 白揚社, 1985(原著 1979)。
- R. P. Feynman, "Negative probability", in B. J. Hiley, F. D. Peat (eds.), *Quantum Implications*, Routledge, 1987.
- M.-O. Renou ら, "Quantum theory based on real numbers can be experimentally falsified", *Nature* 600, 2021.
- S. Coleman, "Fate of the false vacuum: semiclassical theory", *Physical Review D* 15, 1977(インスタントン)。
- J. Friedman, M. S. Morris, I. D. Novikov, F. Echeverria, G. Klinkhammer, K. S. Thorne, U. Yurtsever, "Cauchy problem in spacetimes with closed timelike curves", *Physical Review D* 42(6), 1915–1930, 1990(自己無撞着原理)。
- D. Deutsch, "Quantum mechanics near closed timelike lines", *Physical Review D* 44, 1991.
- The On-Line Encyclopedia of Integer Sequences, A027907(三項係数の三角形)、A002426(中心三項係数)、A082758(三項係数の二乗和)。 https://oeis.org/
- M. J. Wainwright, M. I. Jordan, "Graphical models, exponential families, and variational inference", *Foundations and Trends in Machine Learning* 1, 2008(局所整合ポリトープ)。

### 謝辞と注意

本稿の理論(定理 1〜4、階層、母関数、時間ループの対応)は、Claude Opus 5.5 が JRF の記事と配布プログラムを読んで組み立てたものである。定理 1〜4 は Lean 4 + Mathlib で形式的に証明した(各定理の直後のセルと付録)。$f(2a,2b)$ の閉じた式と母関数は文章で導き、漸化式と計算機で照合した(漸近式は鞍点の評価と数値による)。それが既知の三項係数であることは OEIS で確かめた。ただし Lean の定理は本文の定理を抽象化した形で述べており、ELDE のプログラムが実際に生成する仕様と一致することは、本文の総当りで確かめている(たとえば「CS の中で状態を読み書きするプロセス」が lock 仕様どおりに状態を受け渡すことは、Lean では仮定せず、rf の組合せ的な性質として扱った)。§10 の物理との対応(トンネル効果・インスタントン・時間旅行)は類比であって、物理の主張ではない。文献は 0.2.0 で照合し、0.4.0 で残っていた二件(Friedman ら 1990 の著者と頁、Flanagan & Qadeer 2003 の DOI)を確かめた(照合の記録は refs/BIBLIO.md)。
""")
