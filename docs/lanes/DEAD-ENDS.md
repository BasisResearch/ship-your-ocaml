# Routes not to repeat

- 2026-10-21: a `workspace-write` worker cannot reach the user systemd bus
  or write the home integration queue. Launch the entire worker in the 12 GB
  scope and have the lead run integration after review. Keep the sandbox.

- 2026-10-21: `ulimit -v 12582912` prevents Lean thread/import initialization
  in large closures, even at low RSS and with two threads. Use the actual
  aggregate `MemoryMax=12G` cgroup cap without a virtual-address limit.
- `OpenOutRuntime.budget` quantified over every `runtimeOk` configuration
  cannot follow from that invariant: it does not bound prior custom calls.
  Supply the budget at a successful C_CALL from `Fits` and represented counts.
- `BarrierGrowthFull` cannot preserve G1 quietness on a full table: overflow
  requests a minor GC. Standing decision: discharge via G2, retain its premise.
- C4 hand-proof expansion triggered the abstraction gate. Preserve the draft;
  the approved discovery round 2 waits until F1 is closed.
- Named-value WIP's former ASCII-only node predicate was stronger than
  `GoodF1`, whose primitive accepts arbitrary bytes. The byte/string and
  strcmp source bridges are now generalized; an ASCII guard on `GoodF1`
  remains a rejected route.
- `CustomMemCall` returning `Ready k` alone does not establish exact counter
  increment. A named counter-transition post is needed for n-to-n+1 accounting.

- `formatInteger` currently accepts `d/i/u/x/X/o`, flags, width and precision
  (`OCaml/Bytecode/Data.lean`), despite older F1 prose saying `%d`. A `%d`-only
  native summary can help whileMin but cannot discharge the general
  `F1CcallOpen.format_int_c_call2` field. Preserve that boundary explicitly.

- `F1Heap.NamedRoom` currently uses `maxNamed = 16` and `maxNameLen = 64`,
  but the claimed BcSem guards are absent from `primF1Impl` and `GoodF1`.
  Do not infer those bounds for every F1 call. Generalize the reserve using
  proved bounds, or surface a real domain decision before adding restrictions.

- 2026-10-27: a nursery-only `caml_format_int` return theorem cannot close
  the current general `GoodF1` field. `formatInteger` accepts widths such
  as `%2048d`; its result can exceed 256 payload words while remaining
  within `g1Budget.heapWords`. `Instr.minorAlloc` constrains opcode
  allocations, not this primitive result. The vendored `runtime/alloc.c`
  sends such strings through `caml_alloc_shr` and `caml_check_urgent_gc`.
  Preserve the current domain and prove the large-result path; do not
  silently infer a small-string bound from `Fits`. The fixed major-free-list
  pin in `F1Pins` must also be revisited for that path. This is source-level
  scope analysis, not a kernel-checked reachable-state counterexample.

- 2026-10-27: replacing the formatter's `hap1`/`hap2` stack bounds with
  only `ArgsOut` scalar ownership bounds leaves argument loads unreduced
  across stack writes; `svf_intQ_cases` then reaches the default heartbeat
  limit. Expose `ArgsOut.frames` (derived from `ArgsOut.out`) to `svf_mem`
  before symbolic execution, rather than expanding the resulting load terms.
  The interval consequence requires `0 < len`: an empty argument window
  inside a write frame satisfies `ArgsOut.out` vacuously.

- 2026-10-21: removing the ASCII conjunct only from `NamedNode` could not
  close the named-table bridge: `NamedTable.NodeAt.name` independently used
  `CString`, whose shared `Vsa.MemRepr.CStr.cons` required bytes below 128.
  The one-byte key `[0x80]` exposes that contract obstruction by inspection.
  The byte C-string/strcmp source interface has now been generalized and
  the library battery regenerated. Do not insert an ASCII guard into `GoodF1`
  or a premise excluding successful calls. The original inspection was not
  a kernel-checked counterexample.

- 2026-10-21: `StackGeometry.named` only separates named footprints from
  the VM stack. It does not justify the `.field` case of `LogWindows`:
  `StackGeometry.named_domain_alias` (`OCaml/Vm/Sim/NamedGeometryObstruction.lean`)
  is kernel checked and constructs that geometry with a placed named node
  at `Caml_state->extern_sp`, proving an eight-byte store there overlaps
  the named footprint. This refutes the geometry-only frame route, not
  reachability of the alias. Extend the physical separation/ownership
  invariant and its producers; do not hide the missing fact in `GoodF1`
  or a new premise excluding successful calls.

- 2026-10-21: the manager canceled overlapping build processes after earlier
  interrupted attempts. `scripts/lean-capped.sh` now owns the per-worktree
  `flock --close` serialization as well as the memory-cap policy. Retry
  through that wrapper; do not infer a proof failure from the cancellation.
