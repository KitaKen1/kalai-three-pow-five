#!/usr/bin/env bash
set -euo pipefail
KALAI_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to a new tool directory}"
test "$(uname -s)" = Linux
test ! -e "$COMPARATOR_TOOLS"
mkdir -p "$COMPARATOR_TOOLS/bin"
export PATH="$HOME/.elan/bin:$PATH"
read -r KALAI_COMPARATOR KALAI_EXPORT KALAI_LANDRUN < <(python3 - "$KALAI_ROOT/lean/comparator/pins.json" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]))
print(p['comparator_commit'],p['lean4export_commit'],p['landrun_commit'])
PY
)
git clone --quiet --filter=blob:none --no-checkout https://github.com/zouuup/landrun.git "$COMPARATOR_TOOLS/landrun"
git -C "$COMPARATOR_TOOLS/landrun" checkout --quiet --detach "$KALAI_LANDRUN"
(cd "$COMPARATOR_TOOLS/landrun" && go build -trimpath -o "$COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun)
git clone --quiet --filter=blob:none --no-checkout https://github.com/leanprover/comparator.git "$COMPARATOR_TOOLS/comparator"
git -C "$COMPARATOR_TOOLS/comparator" checkout --quiet --detach "$KALAI_COMPARATOR"
git clone --quiet --filter=blob:none --no-checkout https://github.com/leanprover/lean4export.git "$COMPARATOR_TOOLS/lean4export"
git -C "$COMPARATOR_TOOLS/lean4export" checkout --quiet --detach "$KALAI_EXPORT"
python3 - "$KALAI_ROOT/lean/comparator/pins.json" "$COMPARATOR_TOOLS" <<'PY'
from pathlib import Path
import json,sys
pins=json.load(open(sys.argv[1])); root=Path(sys.argv[2])
for name in ['comparator','lean4export']:
    toolchain=root/name/'lean-toolchain'
    if toolchain.read_text().strip()!=pins['toolchain_patches'][name]['upstream']:
        raise SystemExit('Unexpected upstream toolchain: '+name)
    toolchain.write_text(pins['lean_toolchain']+'\n')
PY
cmp "$KALAI_ROOT/lean/lean-toolchain" "$COMPARATOR_TOOLS/comparator/lean-toolchain"
cmp "$KALAI_ROOT/lean/lean-toolchain" "$COMPARATOR_TOOLS/lean4export/lean-toolchain"
python3 - "$COMPARATOR_TOOLS/comparator/lake-manifest.json" "$KALAI_EXPORT" <<'PY'
import json,sys
packages=json.load(open(sys.argv[1]))['packages']
if next(p['rev'] for p in packages if p['name']=='lean4export')!=sys.argv[2]:
    raise SystemExit('Unexpected pinned exporter dependency')
PY
(cd "$COMPARATOR_TOOLS/comparator" && lake build comparator)
test "$(git -C "$COMPARATOR_TOOLS/comparator/.lake/packages/lean4export" rev-parse HEAD)" = "$KALAI_EXPORT"
(cd "$COMPARATOR_TOOLS/lean4export" && lake build lean4export)
python3 "$KALAI_ROOT/lean/comparator/check-environment.py" "$COMPARATOR_TOOLS" "$COMPARATOR_TOOLS/checker-environment.json"
test -x "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator"
test -x "$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export"
