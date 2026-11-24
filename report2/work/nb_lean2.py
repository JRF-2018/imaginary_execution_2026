# -*- coding: utf-8 -*-
"""report2 の Lean のセル。正本は ../../lean/R2Parts.lean・R2Abstract.lean・R2Mem.lean。"""
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


def _chunks():
    body, _ = base._split("R2Parts.lean")
    parts = body.split("\n/-! ## ")
    return parts[0].rstrip("\n") + "\n\n/-! ## " + parts[1], "/-! ## " + parts[2]


def _chunks_h():
    body, _ = base._split("R2Abstract.lean")
    parts = body.split("\n/-! ## ")
    return [parts[0].rstrip("\n") + "\n\n/-! ## " + parts[1]] + ["/-! ## " + p for p in parts[2:]]


def _chunks_m():
    body, _ = base._split("R2Mem.lean")
    parts = body.split("\n/-! ## ")
    return [parts[0].rstrip("\n") + "\n\n/-! ## " + parts[1]] + ["/-! ## " + p for p in parts[2:]]


def lean_cells(key):
    head = "end ImagExec.R2\n\nnamespace ImagExec.R2M\n\nopen Classical\n\nvariable {S : Type}\n\n"
    tail = "\nend ImagExec.R2M\n\nnamespace ImagExec.R2\n"
    if key == "S":
        cs = _chunks_m()
        return [_cell("end ImagExec.R2\n\n" + cs[0]), _cell(cs[1] + tail)]
    if key == "J":
        cs = _chunks_m()
        return [_cell(head + cs[2] + tail)]
    if key == "K":
        cs = _chunks_m()
        return [_cell(head + cs[3]), _cell(cs[4] + "\nnamespace ImagExec.R2\n")]
    if key == "H":
        cs = _chunks_h()
        # 定理 C のセルで開いたままの名前空間をいったん閉じ、定理 H の後で開き直す
        cs[0] = "end ImagExec.R2\n\n" + cs[0]
        cs[-1] = cs[-1] + "\nnamespace ImagExec.R2\n"
        return [_cell(c) for c in cs]
    if key == "E2":
        body, _ = base._split("R2Parts.lean")
        return [_cell("/-! ## " + body.split("\n/-! ## ")[3])]
    c1, c2 = _chunks()
    return [_cell(c1, first=True)] if key == "C" else [_cell(c2)]


def appendix_cells():
    prints = base._split("R2Parts.lean")[1] + base._split("R2Abstract.lean")[1] + base._split("R2Mem.lean")[1]
    return [new_markdown_cell(base.APPENDIX_MD), _cell("\n".join(prints)),
            new_code_cell(base.SETUP), new_code_cell(base.CHECK)]
