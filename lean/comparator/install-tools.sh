#!/usr/bin/env bash
set -euo pipefail
CALABI_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to a fresh directory}"
test "$(uname -s)" = Linux
mkdir -p "$COMPARATOR_TOOLS/bin"
export PATH="$HOME/.elan/bin:$PATH"
read -r CALABI_CMP CALABI_EXPORT CALABI_LANDRUN < <(python3 - "$CALABI_ROOT/lean/comparator/pins.json" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]));print(p['comparator_commit'],p['lean4export_commit'],p['landrun_commit'])
PY
)
git clone --quiet https://github.com/zouuup/landrun.git "$COMPARATOR_TOOLS/landrun"
git -C "$COMPARATOR_TOOLS/landrun" checkout --quiet --detach "$CALABI_LANDRUN"
(cd "$COMPARATOR_TOOLS/landrun" && go build -trimpath -o "$COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun)
git clone --quiet https://github.com/leanprover/comparator.git "$COMPARATOR_TOOLS/comparator"
git -C "$COMPARATOR_TOOLS/comparator" checkout --quiet --detach "$CALABI_CMP"
git clone --quiet https://github.com/leanprover/lean4export.git "$COMPARATOR_TOOLS/lean4export"
git -C "$COMPARATOR_TOOLS/lean4export" checkout --quiet --detach "$CALABI_EXPORT"
python3 - "$COMPARATOR_TOOLS" <<'PY'
from pathlib import Path
import sys
root=Path(sys.argv[1])
for tool in ['comparator','lean4export']:
    p=root/tool/'lean-toolchain'
    if p.read_text().strip()!='leanprover/lean4:v4.34.0': raise SystemExit('Unexpected upstream toolchain')
    p.write_text('leanprover/lean4:v4.34.1\n')
PY
(cd "$COMPARATOR_TOOLS/comparator" && lake build comparator)
test "$(git -C "$COMPARATOR_TOOLS/comparator/.lake/packages/lean4export" rev-parse HEAD)" = "$CALABI_EXPORT"
(cd "$COMPARATOR_TOOLS/lean4export" && lake build lean4export)
