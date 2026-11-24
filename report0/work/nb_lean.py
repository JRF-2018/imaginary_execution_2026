# -*- coding: utf-8 -*-
"""Lean のセル(本文中の各定理の直後と、末尾の一括検証)。build_nb.py から読む。

Lean の正本は ../../lean/Thm1.lean・Thm23.lean・Thm4.lean。ここではそれを `test.lean` へ書き出すセルに分ける。
"""
import os
from nbformat.v4 import new_markdown_cell, new_code_cell

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_DIR = os.path.join(HERE, "..", "..", "lean")

LEAN_MD = {
    "thm1": r"""#### Lean: 定理 1(`lean/Thm1.lean`)

定理 1 の Lean 4 + Mathlib(v4.34.1)による証明。Lean のセルはどれも `test.lean` に書き出すだけで、検査はノートの最後(付録)でまとめて行う。最初のセルはファイルの頭(`import Mathlib`)も書く。

CS の集合を有限型 `V`、読み出し関係を `par : V → Option V`(`none` が ⊥)、プログラム順序を `po` で表す。`Causal` が「循環しない」、`IsReal` が実実行、`leaves` が葉の集合で、`thm1` が定理 1 である。""",
    "thm2": r"""#### Lean: 定理 2(`lean/Thm23.lean` の前半)

プロセスを `Fin P`、プロセス `q` の CS の数を `L q` とする。lock 仕様の項 `Item`(`P{p}U{n}->P{q}L{m}`)は、プロセス `p` の局所時刻 `2n+1` と `q` の局所時刻 `2m` を占める(`time`)。`Before e e'` は「共有するどのプロセスでも局所時刻が増える」で、`before_iff` がそれと JRF の四つの不等式との同値を示す。`Valid L l` が ELDE その1 の生成する仕様、`Cond S` が定理 2 (1) の条件(衝突なし・非巡回)、`srcE l` が仕様から作る rf である。

- `valid_cond`・`cond_valid`: 定理 2 (1)
- `srcE_eq_iff`: 定理 2 (2)
- `valid_unique`(3 プロセス以下)・`not_unique_four`(4 プロセスの反例): 定理 2 (3)""",
    "thm4": r"""#### Lean: 定理 4(`lean/Thm4.lean`)

CS の集合を有限型 `V`、`Frame` を読み出し関係 `rf`・プログラム順序 `po`・初期状態の組、`Proc` を各 CS の出力 `out`(自分と同じプロセスの前の CS の入力だけで決まる、`loc`)とする。`IsExec` が「各 CS の入力 = `rf` の出力」を満たす入力の組(自己無撞着な実行)、`E` が rf ∪ po の辺、`D` が入力の依存である。

- `thm4_1`: 定理 4 (1)。rf ∪ po が循環しなければ、実行はちょうど一つ(依存 `D` が整礎なので、それに沿って前から計算でき、一意性も同じ帰納法で出る)。
- `thm4_2`: 定理 4 (2)。rf ∪ po が循環すれば(po は狭義の順序)、状態を整数として、実行が一つもないプロセスと二つ以上あるプロセスがある。本文の証明(最短の循環と {0,1})とは作り方を変え、循環を含む強連結な部分 `Comp` を使い、「その中の入力 + 1」を出力させて最小値で矛盾させる(`path_split`・`D_cycle`・`comp_pred`)。""",
    "thm3": r"""#### Lean: 定理 3(`lean/Thm23.lean` の後半)

道は、各事象 `(r, t)`(プロセス `r` の局所時刻 `t`)に大域時刻を与える単射 `τ` で、各プロセスの中では局所時刻の順に並ぶもの(`Arr`)。lock は「その時点で最も新しい unlock 状態」を読む(`TReads`)。`Avoids` は禁止点を通らないこと、`IsReal` は CS の全順序 `σ` で各 CS が直前の CS を読む実実行である。

- `thm3_ii`・`thm3_ii_strong`: 定理 3 (ii)(任意のプロセス数)。要は `cross_double_read`(初めて禁止領域に入る瞬間の二つの lock は同じ状態を読む)と `real_linear`(実実行ではどの状態も高々一度しか読まれない)。
- `thm3_i`: 定理 3 (i)(2 プロセス)。`tunnel_to_e0` と、lock 仕様から道 `tau` を作る `e0_to_tunnel`。
- `tunnel_not_e0_three`: 3 プロセスでは E0 ⊊ トンネル。""",
}

APPENDIX_MD = r"""## 付録: Lean による一括検証

ここまでの `%%writefile` セルで `test.lean` が出来上がっている。最後に、使った公理を表示する行を足し、Lean 4(v4.34.1)+ Mathlib(v4.34.1)をそろえてまとめて検証する。

* **Colab**: elan をインストールし、`imagexec_lean/` に Mathlib を依存に持つ Lake プロジェクトを作る。`lake exe cache get` でビルド済みの .olean を取得する(初回は数分)。
* **ローカル**: カレントディレクトリかその親に、すでに Mathlib 入りの `lakefile.lean` があれば、それをそのまま使う。

エラーがなく、`#print axioms` が標準の公理(`propext`, `Classical.choice`, `Quot.sound`)だけを挙げれば、証明は通っている。"""

SETUP = r"""%%bash
set -e
export PATH="$HOME/.elan/bin:$PATH"
if [ -f lakefile.lean ] && grep -q mathlib lakefile.lean; then
  echo "using the existing Lake project in the current directory"
  echo "." > .leandir
elif [ -f ../lakefile.lean ] && grep -q mathlib ../lakefile.lean; then
  echo "using the existing Lake project in the parent directory"
  echo ".." > .leandir
else
  if ! command -v lake >/dev/null 2>&1; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
  fi
  mkdir -p imagexec_lean && cd imagexec_lean
  echo 'leanprover/lean4:v4.34.1' > lean-toolchain
  cat > lakefile.lean <<'EOF'
import Lake
open Lake DSL

package imagexec_lean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"
EOF
  lake update 2>&1 | tail -3
  lake exe cache get 2>&1 | tail -3
  cd ..
  echo "imagexec_lean" > .leandir
fi"""

CHECK = r"""%%bash
export PATH="$HOME/.elan/bin:$PATH"
LEANDIR=$(cat .leandir)
FILE=$(pwd)/test.lean
cd "$LEANDIR"
time lake env lean "$FILE" && echo "=== test.lean: all theorems checked ==="
"""

HEADER = "import Mathlib\n\nset_option autoImplicit false\nset_option linter.deprecated false\n"


def _split(fname):
    src = open(os.path.join(LEAN_DIR, fname), encoding="utf-8").read()
    body = src[src.index("namespace "):]
    lines = body.split("\n")
    prints = [l for l in lines if l.startswith("#print axioms")]
    body = "\n".join(l for l in lines if not l.startswith("#print axioms")).rstrip() + "\n"
    return body, prints


def _cell(text, first=False):
    head = "%%writefile test.lean\n" + HEADER if first else "%%writefile -a test.lean"
    return new_code_cell(head + "\n" + text.strip("\n") + "\n")


def lean_cells(key):
    cells = [new_markdown_cell(LEAN_MD[key])]
    if key == "thm1":
        body, _ = _split("Thm1.lean")
        parts = body.split("\n/-! ### ")
        chunks = [parts[0]] + ["/-! ### " + p for p in parts[1:]]
        cells.append(_cell(chunks[0], first=True))
        cells += [_cell(c) for c in chunks[1:]]
        return cells
    if key == "thm4":
        # Thm23.lean の名前空間 ImagExec の途中に入るので、いったん閉じて開き直す
        body, _ = _split("Thm4.lean")
        cells.append(_cell("end ImagExec\n\n" + body + "\nnamespace ImagExec\n\nopen Item\n"))
        return cells
    body, _ = _split("Thm23.lean")
    parts = body.split("\n/-! ## ")
    chunks = ["/-! ## " + p for p in parts[1:]]
    chunks[0] = parts[0].rstrip("\n") + "\n\n" + chunks[0]   # `namespace ImagExec` を最初の節に付ける
    want = ("0.", "1.", "2.") if key == "thm2" else ("3.", "4.")
    for c in chunks:
        head = c[c.index("/-! ## ") + len("/-! ## "):]
        if head.startswith(want):
            cells.append(_cell(c))
    return cells


def appendix_cells():
    prints = _split("Thm1.lean")[1] + _split("Thm23.lean")[1] + _split("Thm4.lean")[1]
    return [new_markdown_cell(APPENDIX_MD), _cell("\n".join(prints)),
            new_code_cell(SETUP), new_code_cell(CHECK)]
