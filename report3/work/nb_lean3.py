# -*- coding: utf-8 -*-
"""report3 の Lean のセル。正本は ../../lean/R3Loop.lean。"""
import os
import sys
from nbformat.v4 import new_markdown_cell, new_code_cell

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "report0", "work"))
import nb_lean as base

HEADER = "import Mathlib\n\nset_option autoImplicit false\n"


def _cell(text, first=False):
    head = "%%writefile test.lean\n" + HEADER if first else "%%writefile -a test.lean"
    return new_code_cell(head + "\n" + text.strip("\n") + "\n")


def lean_cells(key):
    body, _ = base._split("R3Loop.lean")
    parts = body.split("\n/-! ## ")
    chunks = [parts[0].rstrip("\n") + "\n\n/-! ## " + parts[1]] + ["/-! ## " + p for p in parts[2:]]
    sel = {"F": chunks[0:3], "F2": chunks[3:5], "R": chunks[5:]}[key]
    if key == "F":
        return [_cell(sel[0], first=True)] + [_cell(c) for c in sel[1:]]
    # 名前空間 ImagExec.R3 は最初のセルで開いたまま、最後のセルで閉じる
    return [_cell(c) for c in sel]


def appendix_cells():
    prints = base._split("R3Loop.lean")[1]
    return [new_markdown_cell(base.APPENDIX_MD), _cell("\n".join(prints)),
            new_code_cell(base.SETUP), new_code_cell(base.CHECK)]
