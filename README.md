# imaginary_execution_2026

虚実行論 2026 ―― 並列処理の総当りから「虚」の理論へ

<!-- Time-stamp: "2026-11-25" -->

私(JRF)は 2011 年に、並列プロセスのロック依存を総当りで調べる Perl のプログラム ELDE(Exhaustive Lock Dependency Emulator、[elde](https://github.com/JRF-2018/elde))を書きました。2018 年になって、それが「実際にはありえない実行」まで数えていたことに気づき、それを **虚実行** と名付けました(本物は **実実行**)。そのとき「今のままでは「虚実行」そのものに意味を見出すのは難しい」と書いたのですが、それを Claude Opus 5.5 さんと一緒に考え直したのが、この四つのレポート(IPYNB)です。

虚実行とは、状態を **コピー** してしまった実行で、実実行は状態を **移動** させた実行です。虚実行は局所的な規則はすべて守り、大域的な線形性(一つの状態は一度しか使わない)だけを破ります。その意味で、虚数や負の数と同じ型の「拡張概念」として扱えないか、というのがもとの問いでした。レポート群は、その問いを、トランザクション(合流)、並列プログラムの部品の意味、継続(callCC)、時間ループと最適化へと広げています。

## ページ

* ノートの HTML 版: https://jrf-2018.github.io/imaginary_execution_2026/ (この README の下のリンク)。

## レポート

読む順に並べます。どれも Claude Opus 5.5 さんによるレポートで、私(JRF)の記事・日記・プログラムと、私との質疑をもとにしています。

| | レポート | 中身 |
|---|---|---|
| report0 | [虚実行論 ―― 並列処理の総当りから「虚」の理論へ](report0/imaginary_execution.ipynb) ([HTML](https://jrf-2018.github.io/imaginary_execution_2026/imaginary_execution.html)) | 実行を「各 CS がどの状態を読んだか」の木として見る。実実行 ⇔ どの状態も高々一度しか読まれない ⇔ 葉が一つ(定理 1)。ELDE その1 の lock 仕様の特徴づけ(定理 2)、進行グラフで禁止領域をすり抜ける道(定理 3)。虚実行の階層と、未来を読む段では実行が自己無撞着性で決まること(定理 4)。仕様数の母関数と漸近式。枝分かれの母関数の単位円上の積分、時間ループの解としての虚数単位(嘘つきの値は $i$) |
| report1 | [虚実行と合流 ―― 楽観的並行制御・スナップショット分離・AI エージェント](report1/imaginary_execution_merge.ipynb) ([HTML](https://jrf-2018.github.io/imaginary_execution_2026/imaginary_execution_merge.html)) | コピーした世界を合流させる仕組み(トランザクション、MVCC・RCU、git の merge、callCC)。合流が直列実行と見分けられない条件(定理 A、楽観的並行制御)。write skew と read-only anomaly。スナップショット分離の危険構造(定理 B、Fekete ら 2005 の形)。並列 AI エージェントの「衝突のない壊れ方」 |
| report2 | [虚実行があるからこそ解ける問題 ―― 部品の意味と計算量](report2/imaginary_execution_parts.ipynb) ([HTML](https://jrf-2018.github.io/imaginary_execution_2026/imaginary_execution_parts.html)) | 実実行だけでは並列合成について閉じない(定理 C)。スケジュールを選べる検査者には各 lock に一つずつの虚の入力が必要十分(定理 H)。記憶のある相手が見分けるのは「外れたときに一手で潰せる」虚の入力の列(定理 J)で、CS が状態の数 − 1 個以下なら恒等写像の CS を消して一致することが文脈同値(定理 K)。スレッド・モジュラー検査で計算量が指数から多項式に。継続と世界の数(定理 E・E′) |
| report3 | [時間ループと最適化 ―― 虚の固定点・反復・コピーと破棄](report3/imaginary_execution_loop.ipynb) ([HTML](https://jrf-2018.github.io/imaginary_execution_2026/imaginary_execution_loop.html)) | 「戻らないことがある種の定常状態になる」の正確な形: 楕円型の不動点での乗数、実の繰り返しが戻るのは乗数が 1 の冪根のときに限る(定理 F・F′・F″・G)。リング発振器(定理 R)。callCC の goto ループ。コピーと破棄による探索(GA・粒子フィルタ・ビームサーチ)で、最適なコピーの量が地平で切り換わること |

各レポートの冒頭に版の変更履歴、末尾に「今後の課題」と「謝辞と注意」(何が Lean の証明で、何が文章の証明・計算機による確認・解釈なのか)を書いています。

## 動かし方

どのノートも、上から順に実行すれば全部動きます(Python 3、numpy、matplotlib)。各ノートは、使う Python のモジュール(`kj_core.py` など)を最初のほうのセルで書き出してから使います。report2 は数分、report3 は 3 分ほどかかります。

各ノートの Lean のセルは、定理の直後に置いた `%%writefile test.lean` のセルで書き出し、最後の付録でまとめて確かめます。その前の準備のセルが、ノートと同じディレクトリか親のディレクトリに Mathlib の入った Lake のプロジェクトがあればそれを使い、なければ elan と Mathlib を入れてプロジェクト `imagexec_lean/` を作ります。Google Colab でもそのまま通ります(初めは数分〜10 分ほどかかります)。

## 中身

* `report0/`〜`report3/` … 各レポートの IPYNB(実行済みの出力つき)、ノートが使う Python のモジュール、文献の照合の記録(`refs/BIBLIO.md`、`refs_BIBLIO.md`)。
  * `work/` … ノートを組み立てる台本(`nb_text*.py` が本文、`build_nb.py` が組み立て、`rebuild.sh` が組み立てと実行)と、ノートの外で回した計算(report2 の `work/conj2pp/`、report3 の `work/exp_*.py` など)。
* `lean/` … 定理の Lean のファイル(Lean 4 v4.34.1 と Mathlib)。詳しくは [lean/README.md](https://github.com/JRF-2018/imaginary_execution_2026/blob/master/lean/README.md)。CI は `.github/workflows/lean.yml`。
* `callcc/` … 2011 年の記事《Haskell の callCC で goto を作る》のプログラムを GHC 9.10.3 で動かした記録と、callCC と虚実行の関係のメモ。`refs_callcc/` は、その調査のメモと、私が 2011 年に配布したソース(`momo_hs/`)。

```bash
cd lean && lake exe cache get && lake build
```

### Lean による定理

| ファイル | レポート | 中身 |
|---|---|---|
| `Thm1.lean` | report0 | 定理 1: 実実行 ⇔ どの状態も高々一度しか読まれない ⇔ 葉が一つ |
| `Thm23.lean` | report0 | 定理 2: ELDE その1 の lock 仕様の特徴づけ(4 プロセスでは一対一でない反例も)。定理 3: 進行グラフの禁止点を通る道は虚 |
| `Thm4.lean` | report0 | 定理 4: rf ∪ po が循環しなければ実行はちょうど一つ。循環すれば、実行のないプロセスも二つ以上あるプロセスもある |
| `R1Merge.lean` | report1 | 定理 A(合流の直列等価性)、write skew、定理 B(SI の依存グラフの循環は、最初に確定したものに入る二本の rw 辺を持つ)、SSI の安全性 |
| `R2Parts.lean` | report2 | 定理 C、定理 E(世界の数 = 1 + 余分な再開)、定理 E′(スケジューラで作れる rf ⇔ rf ∪ po が循環しない) |
| `R2Abstract.lean` | report2 | 定理 H(完全抽象・十分・必要)、定理 H′、定理 I(stuttering) |
| `R2Mem.lean` | report2 | 記憶のある相手との実行、補題 S、定理 J(区別の正確な条件)、定理 K |
| `R3Loop.lean` | report3 | 定理 F・F′・F″・G(メビウス変換の乗数・周期・収束)、定理 R(リング発振器) |

`sorry` はありません。

## 関連

* [elde](https://github.com/JRF-2018/elde) … 元の Perl のプログラム(2011〜2018)。
* 元の記事(ブログ『JRF のソフトウェア Tips』): 《[Exhaustive Lock Dependency Emulator その１ 並列処理の総当り](http://jrf.cocolog-nifty.com/software/2011/06/post-1.html)》(2011年6月)、《[その２ wait_and_lock](http://jrf.cocolog-nifty.com/software/2011/07/post.html)》(2011年7月)、《[その３ 修正とチェック](http://jrf.cocolog-nifty.com/software/2018/04/post-1.html)》(2018年4月)、《[Haskell の callCC で goto を作る](http://jrf.cocolog-nifty.com/software/2011/01/post-2.html)》(2011年1月)、《[時間泥棒の夕べ − 排中律と call/cc](http://jrf.cocolog-nifty.com/column/2011/01/post-1.html)》(2011年1月)。

## Author (文責)

JRF ( http://jrf.cocolog-nifty.com/statuses , Twitter (X): @jion_rockford )

元のプログラム・「虚実行」の着想・問いは JRF のもの(AI 以前のもの)です。レポートの理論の組み立て・プログラム・計算・証明は Claude Opus 5.5 (Anthropic) によるものです。

## License

基本的に「学習用に特に Public Domain になることを望んでいるが、それが気になる場合は MIT License で。」です。

----
(This document is mainly written in Japanese/UTF8.)
