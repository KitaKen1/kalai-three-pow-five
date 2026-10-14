#!/usr/bin/env bash
set -euo pipefail
KALAI_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
KALAI_RECEIPT="$KALAI_ROOT/build-receipt"
mkdir -p "$KALAI_RECEIPT"
printf 'NOT_RUN\n' > "$KALAI_RECEIPT/status.txt"
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > "$KALAI_RECEIPT/status.txt"; fi' EXIT
python3 "$KALAI_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$KALAI_RECEIPT"
python3 "$KALAI_ROOT/lean/comparator/check-archive.py" source --output "$KALAI_RECEIPT/archive-input.json"
cd "$KALAI_ROOT/lean"
lake env lean --version | tee "$KALAI_RECEIPT/compiler.txt"
grep -q 'version 4.33.1,' "$KALAI_RECEIPT/compiler.txt"
python3 comparator/check-private-names.py --receipt-dir "$KALAI_RECEIPT"
# FCSolution imports the FC archive. The archive's elaborator forces ordinary
# kernel checking for every decoded declaration; the original search is absent.
/usr/bin/time -v -o "$KALAI_RECEIPT/build-time.log" \
  timeout --kill-after=120 300m lake build FCSolution 2>&1 | tee "$KALAI_RECEIPT/build.log"
python3 comparator/check-archive.py audit "$KALAI_RECEIPT/build.log" --output "$KALAI_RECEIPT/archive-replay.json"
lake env lean -Ddebug.skipKernelTC=false -DElab.async=false FCAudit.lean 2>&1 | tee "$KALAI_RECEIPT/axioms.log"
python3 comparator/audit.py axioms "$KALAI_RECEIPT/axioms.log" --output "$KALAI_RECEIPT/axioms.json"
python3 - "$KALAI_RECEIPT" <<'PY'
from pathlib import Path
import json, sys
p=Path(sys.argv[1]); inputs=json.loads((p/'input-check.json').read_text())
replay=json.loads((p/'archive-replay.json').read_text())
(p/'source-build.json').write_text(json.dumps({
    'status':'PASS', 'complete_target_build':True, 'target':'FCSolution',
    'lean_toolchain':inputs['pins']['lean_toolchain'],
    'proof_source_map_sha256':inputs['proof_source_map_sha256'],
    'method':'explicit proof declarations, ordinary kernel replay',
    'archive_sha256':replay['archive_sha256'],
    'archive_declarations':replay['declarations'],
    'native_decide':False},indent=2)+'\n')
PY
printf 'PASS\n' > "$KALAI_RECEIPT/status.txt"
if [[ -n "${GITHUB_OUTPUT:-}" ]]; then printf 'ready=true\n' >> "$GITHUB_OUTPUT"; fi
