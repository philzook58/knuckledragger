#!/usr/bin/env bash
# Build a JupyterLite site bundling the local knuckledragger wheel and its pinned runtime wheels.
# Needs `pip install -r lite/requirements.txt`. Output: lite/_output, or the directory given as $1.
set -euo pipefail
cd "$(dirname "$0")"
# Pinned wheels the site installs with `%pip install --no-deps` (sympy is skipped).
WHEELS=(
  z/z3-solver/z3_solver-5.3.3.0-py3-none-pyemscripten_2026_0_wasm32.whl
  l/lark/lark-1.3.1-py3-none-any.whl
  g/graphviz/graphviz-0.21-py3-none-any.whl
)
mkdir -p pypi
rm -f pypi/knuckledragger-*.whl
uv build --wheel --out-dir pypi ..
for w in "${WHEELS[@]}"; do
  [ -f "pypi/${w##*/}" ] || curl -sSfL -o "pypi/${w##*/}" "https://files.pythonhosted.org/packages/py3/$w"
done
jupyter lite build ${1:+--output-dir "$1"}
