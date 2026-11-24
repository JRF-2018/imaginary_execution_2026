# Lean 形式化(report0〜3 の定理)

このディレクトリは Lean 4(v4.34.1)+ Mathlib(v4.34.1)の Lake のパッケージで、各レポートの定理のファイルを一つずつのモジュールとして持ちます。

```bash
cd lean
lake exe cache get   # Mathlib のビルド済みファイルを取ってくる
lake build           # すべてのファイルを検査する(#print axioms の結果も表示される)
```

| ファイル | レポート | 主な定理 |
|---|---|---|
| `Thm1.lean` | report0 | 定理 1(実実行 ⇔ 線形 ⇔ 葉が一つ) |
| `Thm23.lean` | report0 | 定理 2(ELDE その1 の特徴づけ)、定理 3(進行グラフ) |
| `Thm4.lean` | report0 | 定理 4(rf ∪ po が循環しなければ実行はちょうど一つ、循環すれば 0 個・2 個以上がありうる) |
| `R1Merge.lean` | report1 | 定理 A(楽観的並行制御)、write skew、定理 B(スナップショット分離の危険構造)と SSI |
| `R2Parts.lean` | report2 | 定理 C(実実行だけでは閉じない)、定理 E(世界の数)、定理 E′(スケジューラで作れる rf) |
| `R2Abstract.lean` | report2 | 定理 H・H (3)・H′・I、`sep_single` |
| `R2Mem.lean` | report2 | 補題 S、定理 J、定理 K(予想 2″ の CS ≦ |S|−1 の部分) |
| `R3Loop.lean` | report3 | 定理 F・F′・F″・G(メビウス変換の乗数と周期)、定理 R(リング発振器) |

`sorry` はなく、使う公理は標準の `propext`・`Classical.choice`・`Quot.sound` だけです。各ノートブックは、これらのファイルを `%%writefile test.lean` のセルに分けて書き出し、最後にまとめて検査します。以下は作業中に書いた詳しいメモです(「プロジェクト直下で `lake env lean lean/…`」とあるのは作業用の配置での手順で、このリポジトリでは上の手順を使ってください)。

----

# Lean 形式化: report0 の定理 2・3

`Thm23.lean`(Lean 4 v4.34.1 + Mathlib v4.34.1)。プロジェクト直下で

```
lake env lean lean/Thm23.lean
```

でチェックできる(数秒)。`sorry` なし。使う公理は標準の `propext`, `Classical.choice`, `Quot.sound` だけ(ファイル末尾の `#print axioms`)。

## モデル

- プロセス `Fin P`、プロセス `q` は `L q` 回 CS を実行。CS `(q,m)` の lock は局所時刻 `2m`、unlock は `2m+1`。
- 読み出し元 `Src P = Option (Fin P × ℕ)`(`none` = 初期状態 ⊥)。
- lock 仕様の項 `Item`(`P{p}U{n}->P{q}L{m}`)。`Before e e'` = 共有するどのプロセスでも局所時刻が狭義に増える。`before_iff` で、JRF の `_make_lock_spec_tree` の四つの不等式と同値であることを示した。
- `Valid L l`: ELDE その1 が生成する lock 仕様(`Before` について pairwise、範囲内)。`srcE l`: 仕様から作る rf。
- 道(進行グラフ上の単調な道)= lock/unlock 事象の大域時刻 `τ`(各プロセス内で単調、全体で単射)。`TReads`: lock はその時点で最も新しい unlock 状態を読む(トンネル意味論)。`Avoids`: 二つのプロセスが同時にロックを持つ点を通らない。
- 実実行 `IsReal`: CS の全順序 `σ` で各 CS が直前の CS を読む。

## 結果

| Lean の名前 | 内容 |
|---|---|
| `valid_cond`, `cond_valid` | **定理 2(a)**: 受け渡しの集合が lock 仕様として並べられる ⇔ 衝突なし・局所時刻の先後グラフが非巡回(位相的整列)。任意の P。 |
| `srcE_eq_iff` | **定理 2(b)**: 仕様 → rf は受け渡しの集合だけで決まり、集合が違えば rf も違う。任意の P。 |
| `valid_unique` | **定理 2(c)**: P ≤ 3 では、同じ集合の仕様は列として一つ。よって仕様と rf は一対一。 |
| `not_unique_four` | **訂正**: P = 4 では一対一でない(共通のプロセスを持たない二項はどちらの順にも並ぶ)。Python でも (1,1,1,1) で仕様 85 件・rf 73 種類、(2,1,1,1) で 352 件・292 種類を確認。report0 は 3 プロセスまでしか確かめていなかった。 |
| `thm3_ii` | **定理 3(ii)**: rf が実 ⇔ その rf を与える道で禁止点を通らないものがある。**任意の P** で成立(report0 は 2 プロセスとして述べた)。 |
| `thm3_ii_strong` | さらに強く、rf を与える **どの** 道についても「rf が実 ⇔ その道が禁止点を通らない」。証明の要は `cross_double_read`(最初に禁止領域に入る瞬間の二つの lock は同じ状態を読む)と `real_linear`(実実行では状態は高々一度しか読まれない)。 |
| `thm3_i` | **定理 3(i)**(2 プロセス): トンネル意味論の rf の全体 = ELDE その1 の rf の全体 E0。 |
| `tunnel_not_e0_three` | 3 プロセスでは E0 ⊊ T(一つの unlock を二つの他プロセスが読む例)。 |

### 定理 3(i) の証明の筋

- T ⊆ E0 (`tunnel_to_e0`): 道から他プロセスからの読み出しを集め、各項に「lock の大域時刻」を割り当てると先後グラフの辺に沿って真に増える(非巡回)、同じ局所時刻の衝突も起きない。定理 2(a) で並べれば lock 仕様になる。
- E0 ⊆ T (`e0_to_tunnel`): unlock 事象を「その unlock 以前に局所時刻を持つ項の数 `cnt`」で並べ(同数なら受け渡しに使われる unlock を先に、さらにプロセス・番号で決める)、各 lock をその読み出し元の unlock の直後に置く(`tau`)。2 プロセスではどの項も両方のプロセスに局所時刻を持つので、`cnt` が項の列での位置そのものになることが効く。

# R2Mem.lean: report2 §4.5・§4.6(記憶のある相手、補題 S・定理 K)

`lake env lean lean/R2Mem.lean` でチェックできる(数秒、`sorry` なし、標準の公理だけ)。

- モデル: 記憶のないプロセス `X : List (S → S)` と、読んだ値の履歴から書く値を決める相手 `Q : List S → S`(`T` 手)。実行は到達関係 `Reach`(`X` の CS を一つ進める/相手が読んで書く)、観測 `obs` は最終状態の集合。`seg X j X.length` が接尾写像 `s_j`。
- `lemmaS`・`lemmaS_conv`: **補題 S**。位置の可能性 `B` のどこから続けても `v` に着かないなら、`B` を潰す値 `w` がある(証明は `reach_freeze`: 相手が打ち切るまで `X` が止まっているスケジュール)。逆に、潰す値を書いて写すだけなら `v` に着かない。
- `Arr`(初期状態から来られる場面)、`thmJ_nec`・`thmJ_last`・`thmJ_suff`・`thmJ`: **定理 J**(区別の正確な条件)の両向き。信念 = `{c | Arr X Q T init c h x}`。十分の向きは、履歴 `H` に従い、外れたら潰して写すだけの相手を作る。
- `partner`・`produce`・`avoid`・`core`: 一歩ずつ付いていく相手。`P` は `v` に着き、`X` は着かない。
- `thmK`: **定理 K**。恒等写像の CS を含まない `P ≠ X` が、それぞれ `NotFull`(満ちていない)か `Distinct`(軌跡がすべて異なる)なら、記憶のある相手で観測が違う。
- `thmK_long`: 短い方の CS が `|S| − 1` 個以下なら、長い方がどれほど長くても区別できる。
- `thmK_card`: CS がどちらも `|S| − 1` 個以下なら区別できる(予想 2″ の CS ≦ |S| − 1 の部分)。`notFull_or_distinct` は鳩の巣論法。

# R2Abstract.lean の追加: 定理 H (3)

- `thmH3`: どの lock `i` についても、`i` 番目の CS の前で割り込まない検査では一致するが、そこで割り込めば違う二つのプロセスがある(`runI_append`・`runI_ids` を使う)。

# R3Loop.lean の追加(report3 0.2.0)

- `conj_fixed`・`conj_ne`・`real_to_circle`・`elliptic_unit`・`elliptic_return`: **定理 F′**。実係数で実数でない不動点 `z` を持つメビウス変換では、乗数の絶対値は 1、座標 `R(x) = (x − z)/(x − conj z)` は実数直線を単位円に移し、実の繰り返しが `n` 回で戻る ⇔ 乗数の `n` 乗が 1。
- `converge`: **定理 F″**。乗数の絶対値が 1 より小さければ、もう一つの不動点を通らない繰り返しは不動点に収束する(`Filter.Tendsto`)。
- `ringStep`・`ring_N`・`ring_2N`・`ring_no_fixed`: **定理 R**。±1 で書いたリング発振器(段数 `N` 奇数)は `N` 時刻で全体の否定、`2N` 時刻で元に戻り、止まらない。

# R1Merge.lean の追加(report1 0.2.0): 定理 B

- `SIRun`: SI の実行(開始 `s`・確定 `c` の時刻、読み書きの集合、first-committer-wins)。`Edge`: 依存グラフの ww・wr・rw の辺(Adya の辺が満たす条件として書く)。
- `nonrw_time`・`rw_time`: rw 以外の辺 `a → b` では `c a < s b`、rw の辺では `s a < c b`。
- `thmB`: **定理 B**(Fekete ら 2005、Cahill ら 2008 の形)。依存グラフの循環には、循環の中で最初に確定したトランザクションに入る二本の rw 辺があり、どちらの両端も時間が重なる。
- `ssi_safe`: 並行な相手との rw が入って出ていくトランザクションを許さなければ、循環はない。

# Thm4.lean(report0 0.4.0): 定理 4(実行の決まり方)

- `Frame`(rf・po・初期状態)、`Proc`(各 CS の出力。自分と同じプロセスの前の CS の入力だけで決まる)、`IsExec`(各 CS の入力 = rf の出力)。
- `thm4_1`: rf ∪ po が循環しなければ、実行はちょうど一つ(入力の依存 `D` の整礎な再帰と帰納法)。
- `thm4_2`: rf ∪ po が循環すれば(po は狭義の順序)、整数の状態で、実行のないプロセスと二つ以上あるプロセスがある。循環を含む強連結な部分 `Comp` の中で「入力 + 1」を出力させ、最小値で矛盾させる。

# R2Parts.lean の追加: 定理 E′

- `EdgeRP`・`sched_iff`: 各 CS を一度ずつ実行するスケジューラの実行順(単射な時刻 `τ`)で rf ∪ po の辺が時刻を増やすものがある ⇔ rf ∪ po が循環しない。
