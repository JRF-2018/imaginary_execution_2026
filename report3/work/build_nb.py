# -*- coding: utf-8 -*-
"""report1 の ipynb を生成する(ノートブックは直接編集しない)。"""
import os
import sys
import nbformat
from nbformat.v4 import new_notebook, new_markdown_cell, new_code_cell

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import nb_text, nb_lean3 as nb_lean1

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
            nb.cells += module_cells("kj_loop.py",
                "#### `kj_loop.py`\n\nメビウス変換 `mob`・`fixed_points`・`multiplier`・`classify`、リング発振器 `ring_oscillator`、再実行による callCC `run_with_callcc`、NK 景観 `NK` とコピーと破棄の探索 `copy_discard_search`。")
    nb.cells += nb_lean1.appendix_cells()
    nbformat.write(nb, out)
    print("wrote", out, len(nb.cells), "cells")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "imaginary_execution_loop.ipynb"))
