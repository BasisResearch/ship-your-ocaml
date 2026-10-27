# Foreman status

Updated 2026-10-27. Active target: Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently.

## Standing decisions

- `BarrierGrowthFull` remains a named premise until G2 supplies collection.
- `CustomMemCall` remains a named premise.
- C4 abstraction-discovery round 2 waits until F1 closes; its draft is preserved.
- All Lean runs are capped at 12 GB. Landings use `scripts/integrate.sh`,
  including its checks and serialized fast-forward push to `origin/main`.

## Active work

| Lane | Current work | Worktree |
| --- | --- | --- |
| a0-boot / a0-lib | Reset-through-atom milestone landed (`9c443c79`, audited at `bb55a4e5`); reset-to-cut and `libHeap` remain open | `syo-wt/a0-boot-next` |
| a1-prims / bprime | Named-value representation and primitive returns, then `caml_format_int`; retain existing WIP | `syo-wt/a1-prims-next`, `syo-wt/bprime` |
| a6-gc | G2 pick/pop landed as `6d002aa5`; refcount transport landed as `1960311a` | `syo-wt/a6-gc`, `syo-wt/a6-gc-next2` |
| foreman / a1-arms / a2-sem | C_CALL arity landed; shared invariants, table assembly, integration | `syo-wt/a1-arms`; main |

The lead now uses separate `codex exec` workers (`gpt-6.1-sol`, high reasoning),
at most two at a time, launched through `codexwork.sh`. Built-in proof agents
have stopped. The current Sol tasks finish physical named-node ownership/separation and
generalize the formatter caller layout. Startup, G2 pick/pop, refcount transport, all-byte C-string/strcmp, and foreman
tooling landed. The current proof work remains in the two Sol worktrees. Workers inherit a 12 GB systemd scope; the lead handles
Git and landings outside their workspace-write sandbox. Known failed routes are in `docs/lanes/DEAD-ENDS.md`.

All F1 opcode rows and interpreter entry/halt composition are present. The
headline `ocamlrun_refinement_F1_open` still consumes primitive and growth
premises. The captured `WhileMin.loaded_fillZero` proves the captured state
is loaded; it does not prove execution from reset. F1 is not yet closed. The exact-arity C_CALL assembly landed as `c5c0fff4`
after the full gate; bytecode audit/measurement caps landed as `a80d71cc`.
The remaining general C_CALL fields are `openOutRuntime`, `outListRuntime`,
`register_named_value_c_call2`, and `format_int_c_call2`.

The a2-sem uncaught-exception WIP is preserved in `syo-wt/a2-sem-next`;
`GoodF1` excludes that path, so it is behind current F1 work in priority.

The named worker checked the full-byte lookup bridge and 43 focused axiom
reports, preserved at `7c6bc6c1`. Its full consumer build remains incomplete.
The named worker is resuming physical ownership/separation WIP after a usage-limit stop. This is an invariant
design task, not a user-only blocker. The next task supplies physical ownership
and separation, then migrates payload consumers. The formatter WIP is preserved
in `bprime` from `2c0a97a9`; its active worker is porting generated edits into templates.

The independent all-byte C-string/strcmp extraction passed generation checks
and its sole full-gate regression in `Uncaught.FatalNames` is repaired and
focused-audited, then landed as `c5a18e5a` after the full gate. The formatter Sol worker
is now active in `bprime`.
The previous workers stopped on the October 21 usage limit; its logged October
27 reset time has passed, so the lead is restarting separate Sol processes.

G2 validation: the landing gate built 6029 jobs and audited 8325 declarations
before pushing `6d002aa5`. The refcount/library train passed all stages and
audited 8338 declarations before pushing `c5a18e5a`. G2 still has
search/pick/pop as separate summaries; split,
remnant-call composition, allocator readiness and full collection remain open.
