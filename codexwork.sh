#!/usr/bin/env bash
# Run one Sol task in an existing lane worktree; at most two per project.
# Usage: ./codexwork.sh a0-boot-next tasks/sol-startup.md > /tmp/syo-startup.log 2>&1 & wait
main() {
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd -P)
SLOT=${1:?usage: codexwork.sh SLOT TASKFILE}
[[ "$SLOT" =~ ^[a-z0-9-]+$ ]] || { echo 'Invalid slot'; exit 2; }
TASK=$(realpath "${2:?task file required}")
WORKTREE=$(realpath "$ROOT/../syo-wt/$SLOT")
CODEX=${CODEX:-$HOME/.local/share/codex-0.162.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex}
mkdir -p "$ROOT/logs"
LOG="$ROOT/logs/sol-$SLOT-$(date -u +%Y%m%d-%H%M%S)-$$.log"
exec > >(tee -a "$LOG") 2>&1
echo "Task: $TASK; worktree: $WORKTREE; start: $(date -u --iso-8601=seconds)"
stuck() { echo "RESULT: stuck $*"; exit 1; }
[[ -f "$TASK" && -x "$CODEX" ]] || stuck 'missing task or Codex binary'
[[ $(wc -l < "$TASK") -lt 40 ]] || stuck 'task must be under 40 lines'
exec 8>"$ROOT/logs/slot-$SLOT.lock"
flock -n 8 || stuck "worker already active in $SLOT"
exec 9>"$ROOT/logs/worker-1.lock"
if ! flock -n 9; then
  exec 9>"$ROOT/logs/worker-2.lock"
  flock -n 9 || stuck 'two project workers already running'
fi
free -g
AVAILABLE=$(free -g | awk '/^Mem:/{print $7}')
[[ "$AVAILABLE" -ge 25 ]] || stuck "only $AVAILABLE GB available; need 25"
cd "$WORKTREE"
[[ -z $(git status --porcelain) ]] || stuck 'preserve and commit lane WIP before launch'
git fetch origin main || stuck 'fetch origin/main failed'
git merge-base --is-ancestor origin/main main || stuck 'manager must fast-forward main before launch'
git rebase main || stuck 'rebase conflict; work preserved for manager'
START=$(git rev-parse HEAD)
echo "Worker: gpt-6.1-sol, high reasoning; initial commit: $START"
set +e
systemd-run --user --scope -q -p MemoryMax=12G \
  env LEAN_NUM_THREADS=2 SYO_LEAN_CAPPED=1 \
  "$CODEX" exec -m gpt-6.1-sol -c 'model_reasoning_effort="high"' \
  -s workspace-write --add-dir "$ROOT" -C "$WORKTREE" \
  "$(cat "$TASK")" 8>&- 9>&-
RC=$?
set -e
echo "Worker exit: $RC; end: $(date -u --iso-8601=seconds)"
if [[ "$RC" -ne 0 ]]; then
  echo "RESULT: stuck worker exit $RC; inspect $LOG"
elif [[ -z $(git status --porcelain) ]] && [[ $(git rev-parse HEAD) != "$START" ]] &&
     git fetch -q origin main && git merge-base --is-ancestor HEAD origin/main; then
  echo "RESULT: landed $(git rev-parse HEAD)"
else
  echo "RESULT: stuck task not landed; inspect worker result in $LOG"
fi
}
main "$@"; exit "$?"
