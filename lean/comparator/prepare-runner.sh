#!/usr/bin/env bash
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
test "${RUNNER_ENVIRONMENT:-}" = github-hosted
test "${RUNNER_OS:-}" = Linux
# This cleanup is confined to the disposable GitHub-hosted Linux runner.
sudo rm -rf -- /usr/share/dotnet /usr/local/lib/android /opt/ghc /usr/local/.ghcup \
  /usr/share/swift /usr/local/share/powershell /usr/lib/jvm /usr/local/share/boost
sudo apt-get update -qq
sudo apt-get install -y -q time > /dev/null
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$RUNNER_TEMP/kalai-elan-init.sh"
sh "$RUNNER_TEMP/kalai-elan-init.sh" -y --default-toolchain none > /dev/null
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
{ nproc; free -h; df -h .; } | tee "$RUNNER_TEMP/kalai-runner.txt"
available_bytes=$(df -B1 --output=avail . | tail -n 1)
if (( available_bytes < 35 * 1024 * 1024 * 1024 )); then
  echo "::error::Less than 35 GiB free for verification."
  exit 1
fi
