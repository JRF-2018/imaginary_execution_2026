# -*- coding: utf-8 -*-
"""report1 の Lean のセル。正本は ../../lean/R1Merge.lean。report0 の nb_lean.py と同じ作り。"""
import os
import sys
from nbformat.v4 import new_markdown_cell, new_code_cell

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "report0", "work"))
import nb_lean as base   # SETUP, CHECK, _split を流用

HEADER = "import Mathlib\n\nset_option autoImplicit false\nset_option linter.deprecated false\n"

APPENDIX_MD = base.APPENDIX_MD.replace("imagexec_lean", "imagexec_lean")


def _cell(text, first=False):
    head = "%%writefile test.lean\n" + HEADER if first else "%%writefile -a test.lean"
    return new_code_cell(head + "\n" + text.strip("\n") + "\n")


def lean_cells(key):
    body, _ = base._split("R1Merge.lean")
    parts = body.split("\n/-! ## ")
    chunks = [parts[0].rstrip("\n") + "\n\n/-! ## " + parts[1]] + ["/-! ## " + p for p in parts[2:]]
    if key == "B":
        # 定理 B(4 番目の節)。名前空間 ImagExec.R1 は開き直す
        return [_cell("namespace ImagExec.R1\n\n" + chunks[3])]
    # 定理 A と write skew(最初の三つの節)。ここで名前空間をいったん閉じる
    return [_cell(chunks[0], first=True)] + [_cell(c) for c in chunks[1:2]] + \
        [_cell(chunks[2] + "\nend ImagExec.R1\n")]


def appendix_cells():
    prints = base._split("R1Merge.lean")[1]
    return [new_markdown_cell(APPENDIX_MD), _cell("\n".join(prints)),
            new_code_cell(base.SETUP), new_code_cell(base.CHECK)]
