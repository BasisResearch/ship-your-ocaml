#!/usr/bin/env bash
# A Sol worker already inherits the launcher's 12 GB systemd scope.
set -euo pipefail
[[ $# -gt 0 ]] || { echo 'usage: lean-capped.sh COMMAND [ARGS...]' >&2; exit 2; }
AVAILABLE=$(free -g | awk '/^Mem:/{print $7}')
[[ "$AVAILABLE" -ge 25 ]] || { echo "Only $AVAILABLE GB available; wait for 25 GB" >&2; exit 1; }
if [[ ${SYO_LEAN_CAPPED:-0} == 1 ]]; then
  exec env LEAN_NUM_THREADS=2 "$@"
else
  exec systemd-run --user --scope -q -p MemoryMax=12G env LEAN_NUM_THREADS=2 "$@"
fi
