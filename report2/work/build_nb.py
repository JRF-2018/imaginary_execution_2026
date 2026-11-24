# -*- coding: utf-8 -*-
"""report1 の ipynb を生成する(ノートブックは直接編集しない)。"""
import os
import sys
import nbformat
from nbformat.v4 import new_notebook, new_markdown_cell, new_code_cell

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import nb_text, nb_lean2 as nb_lean1

SEP = "# ------------------------------------------------------------------\n"


def module_cells(fname, intro):
    src = open(os.path.join(HERE, fname), encoding="utf-8").read()
    parts = src.split(SEP)
    chunks = [parts[0]] + [SEP + p for p in parts[1:]]
    cells = [new_markdown_cell(intro)]
    for i, ch in enumerate(chunks):
        head = f"%%writefile {fname}" if i == 0 else f"%%writefile -a {fname}"
        cells.append(new_code_cell(head + "\n" + ch.rstrip("\n") + "\n"))
    cells.append(new_code_cell(f"from {fname[:-3]} import *\nprint('ok')"))
    return cells


def main(out):
    nb = new_notebook()
    nb.metadata["kernelspec"] = {"name": "python3", "display_name": "Python 3", "language": "python"}
    nb.metadata["language_info"] = {"name": "python"}
    for kind, s in nb_text.CELLS:
        if kind == "md":
            nb.cells.append(new_markdown_cell(s))
        elif kind == "code":
            nb.cells.append(new_code_cell(s))
        elif kind == "lean":
            nb.cells += nb_lean1.lean_cells(s)
        elif kind == "modules":
            nb.cells += module_cells("kj_comp.py",
                "#### `kj_comp.py`\n\nインタリーブの観測 `finals`、文脈同値 `context_classes`・`refines`、記憶のある相手で区別できるかの厳密な判定 `distinguishable`、定理 K の相手 `separating_partner`(`killer`・`is_full`・`run_with_partner`)、全状態探索 `explore_global` とスレッド・モジュラー検査 `explore_modular`、再実行による callCC `run_with_callcc`。")
    nb.cells += nb_lean1.appendix_cells()
    nbformat.write(nb, out)
    print("wrote", out, len(nb.cells), "cells")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "imaginary_execution_parts.ipynb"))
