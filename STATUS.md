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
have stopped. The current Sol tasks reconstruct complete channel-count return evidence
for the actual C_CALL execution, and prove the first empty-skiplist insertion needed by startup. Startup, G2 pick/pop, refcount transport, all-byte C-string/strcmp, and foreman
tooling landed. The current proof work remains in the two Sol worktrees. Workers inherit a 12 GB systemd scope; the lead handles
Git and landings outside their workspace-write sandbox. Known failed routes are in `docs/lanes/DEAD-ENDS.md`.

All F1 opcode rows and interpreter entry/halt composition are present. The
headline `ocamlrun_refinement_F1_open` still consumes primitive and growth
premises. The captured `WhileMin.loaded_fillZero` proves the captured state
is loaded; it does not prove execution from reset. F1 is not yet closed. The exact-arity C_CALL assembly landed as `c5c0fff4`
after the full gate; bytecode audit/measurement caps landed as `a80d71cc`.
On the landing candidate, the remaining general C_CALL fields are `openOutRuntime`, `outListRuntime`,
`register_named_value_c_call2`, and `format_int_c_call2`.

The a2-sem uncaught-exception WIP is preserved in `syo-wt/a2-sem-next`;
`GoodF1` excludes that path, so it is behind current F1 work in priority.

The physical named-table migration passed the complete `OCaml` build (4,151
jobs) and all 71 focused axiom reports. Its checked commit is `97e03f8d`;
the rebased integration candidate is in `syo-wt/a6-gc-next2` (`3322dc6c` before
status updates), alongside the formatter checkpoint. The first gate was stopped after a downstream build exposed a missing
named-binding equality in `LoopGeometry.of_above`. That explicit frame premise
is repaired; its focused build passes (1,539 jobs) and both axiom reports
use only the permitted standard axioms. The full gate is running again at
`3e4bc39f` in the staging worktree. The migration keeps the matching selected malloc ledger
rather than assuming ownership of every live allocation. Its original Sol
slot completed the per-call custom-count/readiness checkpoint (`acb1f875` after rebase,
not landed): 3,684 affected build jobs and 52 focused axiom reports pass.
`CustomMemCall.call` carries the exact count transition in its actual post.
The actual unary setup/suffix continuation is now checked at `13320f38`
(not landed): 3,304 build jobs and 27 axiom reports pass. It retains the
physical count on one execution, but the full loop boundary still needs
refcounts and list links at the same returned placement. The active worker
supplies those complete channel returns and the out-list increment/no-wrap
proof. The ordinary loop invariant, startup zero and runtime suppliers remain
open; these checkpoints are not F1 closure.

The formatter layout/template checkpoint and its memmove integration repair
landed as `d89766ae` after the full 6,029-job build and all gate stages. Its
former Sol slot now proves
the first empty-skiplist insertion used by `caml_init_backtrace` in `a6-gc`.
The seed-zero path selects level 0 and allocates a 24-byte cell. Two evaluator
attempts hit the 12 GB cap; factored certificates now pass with a 6 GB Lean
diagnostic limit. The native summary, ownership/frame proof and reset
composition remain in progress.

Prepared next assignments (not additional running workers): native `vsnprintf`
wrapper execution (`tasks/sol-vsnprintf-wrapper.md`) and G2 split/remnant composition
(`tasks/sol-gc-split.md`), plus a proved named-resource reserve without the
absent fixed guards (`tasks/sol-named-reserve.md`). The complete channel-return task
(`tasks/sol-channel-returns.md`) is active before returning to the full loop
migration. There are still only two Sol workers.

G2 validation: the landing gate built 6029 jobs and audited 8325 declarations
before pushing `6d002aa5`. The refcount/library train passed all stages and
audited 8338 declarations before pushing `c5a18e5a`. G2 still has
search/pick/pop as separate summaries; split,
remnant-call composition, allocator readiness and full collection remain open.

Formatter checkpoint: `SnpFmt` and `Format.SvfLong` built (911 jobs), and
`vsnprintf_layout` admits the real FILE, buffer and seven varargs slots from
stack bounds/alignment alone. Wrapper execution, allocation, and the general
C_CALL2 return remain open, including large strings and nondecimal formats.
