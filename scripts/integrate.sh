#!/usr/bin/env bash
# Land the current lane branch on origin/main: rebase, gate, fast-forward push.
#
#     scripts/integrate.sh
#
# Run from a lane worktree with a clean tree. Rebases onto origin/main, runs
# scripts/check_all.sh (it builds under a 30 GB cgroup cap), and pushes HEAD to
# main only as a fast-forward; on a push race it re-fetches and retries. On a
# rebase conflict or a failing gate it stops and leaves the branch as it is.
# Landings from all lanes are serialized by a machine-wide lock, so they
# queue instead of racing (a race costs a second full rebuild).
set -euo pipefail
exec 9>"${SYO_INTEGRATE_LOCK:-$HOME/.syo-integrate.lock}"
echo "integrate: waiting for the landing lock (another lane may be landing)"
flock 9
echo "integrate: lock held"
cd "$(git rev-parse --show-toplevel)"
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "integrate: commit or stash first"; exit 1; }
wait_mem() {
  while :; do
    avail=$(free -g | awk '/^Mem:/{print $7}')
    [ "$avail" -ge 25 ] && return
    echo "integrate: ${avail} GB available (< 25), waiting"; sleep 120
  done
}
for attempt in 1 2 3 4 5; do
  git fetch -q origin main
  git rebase -q origin/main || { echo "integrate: rebase conflict — resolve, then rerun"; exit 1; }
  wait_mem
  bash scripts/check_all.sh > .integrate.log 2>&1 || { tail -20 .integrate.log; echo "integrate: gate failed (.integrate.log)"; exit 1; }
  if git push -q origin HEAD:main; then echo "integrate: landed $(git rev-parse --short HEAD) on main"; exit 0; fi
  echo "integrate: push race, retrying ($attempt)"
done
echo "integrate: gave up after 5 push races"; exit 1
