# F1 foreman

The lead plans, assigns, reviews and lands. Proof workers are separate
`codex exec` processes using `gpt-6.1-sol` with high reasoning, never built-in
subagents. At most two run for this project. Reuse `../syo-wt/*` lane worktrees.

Launch from the main checkout:

```
./codexwork.sh a0-boot-next tasks/sol-startup.md > /tmp/syo-startup-launch.log 2>&1 & wait
```

The runner checks free memory, locks a project worker slot and the worktree,
requires preserved WIP to be committed, fetches and rebases on current `main`,
then logs to `logs/sol-<slot>-<time>-<pid>.log`. Keep the shell waiting when
using an exec tool so its process cleanup does not kill the background job.
Each task starts with
`tasks/RULES.txt` verbatim, followed by one target, files and a completion
criterion; fewer than 40 lines in total. The launcher puts the entire worker
inside a 12 GB systemd scope, so sandboxed child builds inherit the limit.
Use `scripts/lean-capped.sh` for builds; outside a worker it creates the scope.

Review actual changes, theorem premises, audit results and gate output before
counting a landing. Workers leave checked edits and report results. The foreman commits and runs
`scripts/integrate.sh` outside the worker sandbox after review, because
`workspace-write` denies Git metadata, the user systemd bus and home landing queue.
Append the final `RESULT: landed <commit>` to the worker log after landing.
Do not re-send routes recorded in `docs/lanes/DEAD-ENDS.md`. Keep `STATUS.md`
current, reserving `## Needs user` for decisions only the user can make.

When warming an idle worktree, keep the dependency build caches consistent
with the project cache. Copying only `.lake/build` can trigger a broad rebuild:
the October 27 formatter gate found different `Sail.Sail` artifact hashes in
the two worktrees despite identical source and compiler inputs, invalidating
the transitive import hashes. Compare dependency artifacts before choosing a
cache donor; let Lake validate all copied artifacts. Never alter trace hashes
or copy into a worktree with an active build.

For a failing or memory-heavy proof, use `python3 scripts/lean-guarded.py
--log /tmp/task-build.log -- scripts/lean-capped.sh lake ...`. Inside the worker
scope it stops that build's process group on a reported error or at 10 GiB,
leaving headroom below the 12 GiB cap for the worker. For diagnosis, use
`lake env lean -M 6000 -j 1 --profile` on a small temporary file before
retrying the whole module. The guard also cleans up the build's descendants
when interrupted; canceling Lake alone can leave a compiler running.

F1 remains the priority; G2 continues as a slot becomes available. Preserve
the older Bprime C4 draft and a2-sem uncaught-path WIP until their turn.
