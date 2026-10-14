#!/usr/bin/env bash
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
test "${RUNNER_ENVIRONMENT:-}" = github-hosted
test "${RUNNER_OS:-}" = Linux
want=${1:-8}
keep=${2:-20}
free_gb() { df --output=avail -BG "$1" | tail -n 1 | tr -dc '0-9'; }
directory=/
if mountpoint -q /mnt && (( $(free_gb /mnt) > $(free_gb /) )); then directory=/mnt; fi
amount=$(( $(free_gb "$directory") - keep ))
(( amount > want )) && amount=$want
if (( amount < 1 )); then echo 'No room for additional swap.'; exit 0; fi
swap_file="${directory%/}/kalai-swap-$RANDOM"
sudo fallocate -l "${amount}G" "$swap_file"
sudo chmod 600 "$swap_file"
sudo mkswap "$swap_file" > /dev/null
sudo swapon "$swap_file"
{ free -h; swapon --show; } | tee -a "$RUNNER_TEMP/kalai-runner.txt"
