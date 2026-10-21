# F1 foreman

The lead plans, assigns, reviews and lands. Proof workers are separate
`codex exec` processes using `gpt-6.1-sol` with high reasoning, never built-in
subagents. At most two run for this project. Reuse `../syo-wt/*` lane worktrees.

Launch from the main checkout:

```
nohup ./codexwork.sh a0-boot-next tasks/sol-startup.md >/dev/null 2>&1 &
```

The runner checks free memory, locks a project worker slot and the worktree,
requires preserved WIP to be committed, fetches and rebases on current `main`,
then logs to `logs/sol-<slot>-<time>-<pid>.log`. Each task starts with
`tasks/RULES.txt` verbatim, followed by one target, files and a completion
criterion; fewer than 40 lines in total. Every Lean run uses a 12 GB cgroup.

Review actual changes, theorem premises, audit results and gate output before
counting a landing. Workers land through `scripts/integrate.sh`; the foreman
also uses that train for reviewed recovered work and coordination updates.
Do not re-send routes recorded in `docs/lanes/DEAD-ENDS.md`. Keep `STATUS.md`
current, reserving `## Needs user` for decisions only the user can make.

F1 remains the priority; G2 continues as a slot becomes available. Preserve
the older Bprime C4 draft and a2-sem uncaught-path WIP until their turn.
