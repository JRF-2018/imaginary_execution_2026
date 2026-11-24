#!/bin/bash
# 生成 → 実行(無ければ作る)
set -e
cd "$(dirname "$0")"
# Python と Jupyter: 環境変数 PY と JUPYTER で変えられる(既定は PATH 上のもの)
PY=${PY:-python3}
JUPYTER=${JUPYTER:-jupyter}
[ -x $PY ] || { python3 -m venv $V; $V/bin/pip install -q numpy matplotlib nbformat nbconvert ipykernel; }
$PY build_nb.py ../imaginary_execution.ipynb
cd ..
$JUPYTER nbconvert --to notebook --execute --inplace --ExecutePreprocessor.timeout=1800 imaginary_execution.ipynb
echo executed
