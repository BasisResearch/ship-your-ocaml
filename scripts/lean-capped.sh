#!/usr/bin/env bash
# A Sol worker already inherits the launcher's 12 GB systemd scope.
set -euo pipefail
[[ $# -gt 0 ]] || { echo 'usage: lean-capped.sh COMMAND [ARGS...]' >&2; exit 2; }
AVAILABLE=$(free -g | awk '/^Mem:/{print $7}')
[[ "$AVAILABLE" -ge 25 ]] || { echo "Only $AVAILABLE GB available; wait for 25 GB" >&2; exit 1; }
# Keep the lock in flock's parent, not in the child: OS trace validation
# expects inherited file descriptors to be closed.
BUILD_ROOT=$(git rev-parse --show-toplevel)
mkdir -p "$BUILD_ROOT/.lake"
if [[ ${SYO_BUILD_LOCK_ROOT:-} == "$BUILD_ROOT" ]]; then
  exec env LEAN_NUM_THREADS=2 "$@"
fi
if [[ ${SYO_LEAN_CAPPED:-0} == 1 ]]; then
  exec flock --close "$BUILD_ROOT/.lake/syo-build.lock" \
    env LEAN_NUM_THREADS=2 SYO_BUILD_LOCK_ROOT="$BUILD_ROOT" "$@"
else
  exec flock --close "$BUILD_ROOT/.lake/syo-build.lock" \
    systemd-run --user --scope -q -p MemoryMax=12G \
    env LEAN_NUM_THREADS=2 SYO_LEAN_CAPPED=1 SYO_BUILD_LOCK_ROOT="$BUILD_ROOT" "$@"
fi
