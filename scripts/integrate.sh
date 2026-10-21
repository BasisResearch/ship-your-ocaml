#!/usr/bin/env bash
# Land the current lane branch on origin/main: rebase, gate, fast-forward push.
#
#     scripts/integrate.sh
#
# Run from a lane worktree with a clean tree. Rebases onto origin/main, runs
# scripts/check_all.sh (it builds under a cgroup cap), and pushes to main only
# as a fast-forward; on a push race it re-fetches and retries. On a rebase
# conflict or a failing gate it stops and leaves the branch as it is.
#
# Landings from all lanes are serialized by a machine-wide lock. While waiting,
# each run registers its branch head in ~/.syo-queue. The run that holds the
# lock lands a TRAIN: its own commits plus every queued branch that
# cherry-picks cleanly, gated once (one rebuild for the whole queue). A queued
# branch that conflicts is left out and lands on its own turn. If the train's
# gate fails, the holder falls back to gating its own branch alone. A run whose
# commits already reached main on someone else's train finds nothing left to
# land and exits at once.
main() {
set -euo pipefail
QUEUE="${SYO_INTEGRATE_QUEUE:-$HOME/.syo-queue}"
mkdir -p "$QUEUE"
cd "$(git rev-parse --show-toplevel)"
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "integrate: commit or stash first"; exit 1; }
BRANCH=$(git branch --show-current)
ENTRY="$QUEUE/$$"
echo "$(git rev-parse HEAD) $BRANCH $(pwd)" > "$ENTRY"
cleanup() {
  rm -f "$ENTRY"
  if git rev-parse --verify -q "train-$$" >/dev/null; then
    git checkout -q "$BRANCH" 2>/dev/null || true
    git branch -q -D "train-$$" 2>/dev/null || true
  fi
  return 0
}
trap cleanup EXIT

exec 9>"${SYO_INTEGRATE_LOCK:-$HOME/.syo-integrate.lock}"
echo "integrate: waiting for the landing lock (another lane may be landing)"
flock 9
echo "integrate: lock held"
rm -f "$ENTRY"

wait_mem() {
  while :; do
    avail=$(free -g | awk '/^Mem:/{print $7}')
    [ "$avail" -ge 25 ] && return
    echo "integrate: ${avail} GB available (< 25), waiting"; sleep 60
  done
}
# 9>&-: the gate must not inherit the lock descriptor (the OS-spec
# validation traces expect fd 9 to be closed, EBADF).
gate() { wait_mem; bash scripts/check_all.sh > .integrate.log 2>&1 9>&-; }

for attempt in 1 2 3 4 5; do
  git fetch -q origin main
  git rebase -q origin/main || { echo "integrate: rebase conflict — resolve, then rerun"; exit 1; }
  if [ "$(git rev-parse HEAD)" = "$(git rev-parse origin/main)" ]; then
    echo "integrate: nothing left to land (already on main, e.g. via another lane's train)"; exit 0
  fi
  # Build the train: own commits, then each queued branch that applies cleanly.
  git checkout -q -B "train-$$"
  riders=()
  for e in "$QUEUE"/*; do
    [ -f "$e" ] || continue
    read -r sha br wt < "$e" || continue
    git merge-base --is-ancestor "$sha" origin/main 2>/dev/null && continue
    # Lanes often share unlanded foreman commits, or copies of those commits
    # rebased onto different heads. Pick only patches missing from this train.
    commits=()
    mapfile -t commits < <(git rev-list --reverse --topo-order --cherry-pick --right-only "HEAD...$sha")
    [ ${#commits[@]} -gt 0 ] || continue
    if git cherry-pick "${commits[@]}" >/dev/null 2>&1; then
      riders+=("$br")
    else
      git cherry-pick --abort 2>/dev/null || true
      echo "integrate: $br does not apply cleanly on the train; it lands on its own turn"
    fi
  done
  if [ ${#riders[@]} -gt 0 ]; then
    echo "integrate: train = $BRANCH + ${riders[*]}"
    if gate; then
      if git push -q origin HEAD:main; then
        echo "integrate: landed train $(git rev-parse --short HEAD) on main ($BRANCH + ${riders[*]})"
        git checkout -q "$BRANCH"; git fetch -q origin main; git rebase -q origin/main || true
        exit 0
      fi
      echo "integrate: push race on the train, retrying ($attempt)"
      git checkout -q "$BRANCH"; git branch -q -D "train-$$"; continue
    fi
    echo "integrate: train gate failed (.integrate.log); falling back to $BRANCH alone"
    cp .integrate.log .integrate-train.log
    git checkout -q "$BRANCH"; git branch -q -D "train-$$"
  else
    git checkout -q "$BRANCH"; git branch -q -D "train-$$"
  fi
  gate || { tail -20 .integrate.log; echo "integrate: gate failed (.integrate.log)"; exit 1; }
  if git push -q origin HEAD:main; then echo "integrate: landed $(git rev-parse --short HEAD) on main"; exit 0; fi
  echo "integrate: push race, retrying ($attempt)"
done
echo "integrate: gave up after 5 push races"; exit 1
}
main "$@"
