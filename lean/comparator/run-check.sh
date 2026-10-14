#!/usr/bin/env bash
set -euo pipefail
KALAI_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
test "$(uname -s)" = Linux
test "$(id -u)" -ne 0
KALAI_RECEIPT="$KALAI_ROOT/comparator-receipt"
mkdir -p "$KALAI_RECEIPT"
printf 'NOT_RUN\n' > "$KALAI_RECEIPT/status.txt"
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > "$KALAI_RECEIPT/status.txt"; fi' EXIT
python3 "$KALAI_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$KALAI_RECEIPT"
python3 "$KALAI_ROOT/lean/comparator/check-environment.py" "$COMPARATOR_TOOLS" "$KALAI_RECEIPT/checker-environment.json"
{
  printf 'repository=%s\nrun=%s\nattempt=%s\n' "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}" "${GITHUB_RUN_ATTEMPT:-local}"
  printf 'tested_commit=%s\n' "$(git -C "$KALAI_ROOT" rev-parse HEAD)"
  date -u +started_utc=%FT%TZ
  printf 'sandbox: unprivileged uid/gid, RestrictAddressFamilies=~AF_UNIX, NoNewPrivileges=yes\n'
  uname -a
} > "$KALAI_RECEIPT/environment.txt"
cd "$KALAI_ROOT/lean"
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=240min --working-directory="$KALAI_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" comparator.json \
  2>&1 | tee "$KALAI_RECEIPT/comparator.log"
grep -Fxq 'Lean default kernel accepts the solution' "$KALAI_RECEIPT/comparator.log"
grep -Fxq 'Your solution is okay!' "$KALAI_RECEIPT/comparator.log"
python3 comparator/check-inputs.py --receipt-dir "$KALAI_RECEIPT/after"
lake env lean -Ddebug.skipKernelTC=false -DElab.async=false FCAudit.lean 2>&1 | tee "$KALAI_RECEIPT/axioms.log"
python3 comparator/audit.py axioms "$KALAI_RECEIPT/axioms.log" --output "$KALAI_RECEIPT/axioms.json"
printf 'PASS\n' > "$KALAI_RECEIPT/status.txt"
