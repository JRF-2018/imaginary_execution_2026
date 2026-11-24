# -*- coding: utf-8 -*-
"""imaginary_execution.ipynb を生成する(ノートブックは直接編集しない)。"""
import os, re, sys
import nbformat
from nbformat.v4 import new_notebook, new_markdown_cell, new_code_cell

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import nb_text1, nb_text2, nb_lean

SEP = "# ------------------------------------------------------------------\n"


def module_cells(fname, intro):
    src = open(os.path.join(HERE, fname), encoding="utf-8").read()
    parts = src.split(SEP)
    chunks = [parts[0]]
    for p in parts[1:]:
        chunks.append(SEP + p)
    cells = [new_markdown_cell(intro)]
    for i, ch in enumerate(chunks):
        head = f"%%writefile {fname}" if i == 0 else f"%%writefile -a {fname}"
        cells.append(new_code_cell(head + "\n" + ch.rstrip("\n") + "\n"))
    return cells


def main(out):
    nb = new_notebook()
    nb.metadata["kernelspec"] = {"name": "python3", "display_name": "Python 3", "language": "python"}
    nb.metadata["language_info"] = {"name": "python"}
    for kind, s in nb_text1.CELLS + nb_text2.CELLS:
        if kind == "md":
            nb.cells.append(new_markdown_cell(s))
        elif kind == "code":
            nb.cells.append(new_code_cell(s))
        elif kind == "lean":
            nb.cells += nb_lean.lean_cells(s)
        elif kind == "modules":
            nb.cells += module_cells("kj_core.py",
                "### 2.1 `kj_core.py` ―― 再実装の中心\n\n状態の表し方、プロセスの再生、実実行と虚実行の総当り、ELDE その1 の忠実な移植、判定関数。")
            nb.cells += module_cells("kj_ext.py",
                "### 2.2 `kj_ext.py` ―― 拡張\n\n数え上げの漸化式、トンネル意味論、葉の母関数、複数ロックのモデル検査器、確率的スケジューラ、メビウス変換(時間ループ)、自己無撞着な実行の探索(§5.5)。")
    nb.cells += nb_lean.appendix_cells()
    nbformat.write(nb, out)
    print("wrote", out, len(nb.cells), "cells")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "imaginary_execution.ipynb"))
