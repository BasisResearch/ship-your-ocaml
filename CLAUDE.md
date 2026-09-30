# Proof discipline — the exponentiating layer is MANDATORY

This repository proves the bare-metal `ocamlrun` of OCaml 4.14.4
(`c/ocamlrun-riscv-htif.elf`) against the ZINC bytecode semantics `BcSem`
(Layer A), gives bytecode programs a machine-style program logic (Layer B′),
and states the compiler's correctness at the source level with the bootstrap
fixpoint (Layer C). The discipline is ship-your-interpreter's
(BasisResearch/ship-your-interpreter), where proof effort went
subexponential exactly when work was done by hand beside an abstraction that
already existed. `scripts/check_all.sh` stage a4
(`scripts/check_discipline.py` + `scripts/discipline_rules.tsv`) FAILS new
files that bypass it; rules O1–O7 cover `OCaml/`. Stage a8
(`scripts/check_abstraction_gate.py`) fails with "run /abstraction-discovery"
when an obligation cluster (`abstractions/clusters.def`) reaches 8 hand
proofs without its per-case cost falling by a third; the only allowed next
task is then a discovery round (`abstractions/ROUND-<n>.md`).

**Before ANY proof work:**
* Run `scripts/abs_inventory.sh` and reuse by name.
* Read PHASES.md for which abstractions are ported yet and PLAN.md for the
  layer you are in.

## Mandatory tool per task shape

The Availability column says:
* **here**: in this repository's copied layer (`Vsa/`, `VsaIris/`);
* **A0**: in ship-your-interpreter, blocked on the import cuts in
* **A0**: in ship-your-interpreter, outside the copied import closure, to be ported first.

| Task shape | Use (never hand-roll) | Availability |
|---|---|---|
| Whole function (multi-block: branches, loops, calls, tail jumps, `tohost` seams) | `scripts/syi/gen_fn.py --fn <f> --entry <pc> [--fold]`, which emits the block arms plus the derived `FnSummary` fold; fold combinators `FnSummary.{seq,callSplice,tailJump}` | generator + `FnSummary`: here; `segRowFramed`: A0 |
| Straight-line or branch/jump-terminated span | `#derive_case` segment + `segToTriple` (`SegToTripleFramed`) | A0 |
| Span ending in a call (`jal`) | `BridgeSeg.bridgeOfSeg` + `jalStep_of_obs`; `bridgeOfSegFull` when non-ABI registers must be kept | A0 |
| ABI register frame / memory frame on a run | `FrameMeta.abiFrame_of_wrChain`, `FrameMeta.memFrame_of_chain` (one `decide`); never per-site frame threading | A0 |
| Call splice (prefix ≫ callee ≫ suffix) | `callSeg`/`callSegConseq` (`DeriveCallSeg`) | here |
| Loop | `loopFromBody` (`DeriveLoop`) | here |
| Load / byte-read obligation | total reads, `RamRead{Policy,Single,Data,Scalar,Virtual,Load,Value}`; the model's `readByte` is `getD 0`, so never demand presence the densification (`fillZero`) already gives | here |
| Allocator machine run (`_malloc_r`, `_free_r`, `_realloc_r`) | `SWP pc R Mt` (`VsaIris/Vsa/SymRun.lean`) with generated step tables (`scripts/syi/gen_alloc_steps.py`); never a hand stage over `seg_step` | A0 |
| Iris-route block (segment, helper call, fuel loop) for total and partial WP | state it `∀ (Wp : MachWP M)` and use `Wp.run`/`wp_segW`/`wp_callW`/`wp_retW`/`wp_localRunW` (`VsaIris/MachWP.lean`) | here |
| Newlib stdout call (`print` → `fwrite` → `__sfvwrite_r` → `_write`) | the stdio step tables (`VsaIris/Vsa/Stdout/*`) | A0 |
| libgcc soft-int (`__muldi3`, `__udivdi3`, `__moddi3`, …) | the site/spec batteries (`Muldi3Spec`, `DivSpec`), regenerated at `ocamlrun` addresses | here (WHILE addresses) |
| Decode of an instruction word | the generated decode table (`experiments/syi/gen_decode_table.py`), one lemma per word | here (regenerate for `c/ocamlrun-riscv-htif.elf`) |
| Struct offsets, `Caml_state` fields, symbol addresses, `caml_interprete`'s register allocation | `OCaml/Vm/Layout.lean` (`scripts/gen_layout.py`, read from the ELF and `domain_state.tbl`, pattern-checked) — never a hand-written offset | here |
| Opcode numbering and operand counts | `OCaml/Bytecode/Opcode.lean` (`scripts/gen_opcodes.py` from `instruct.h` + `fix_code.c`) | here |
| A concrete bytecode program as a `Prog` | `runbc --lean FILE NAME` (the loader `OCaml/Bytecode/Load.lean`) | here |
| `BcSem` behaviour of a concrete program | `bcHalts_of_runTo` + `decide +kernel` on `runTo` (model: `OCaml/Programs/Validation.lean`); runs longer than a few thousand steps: chunk over explicit intermediate states | here |
| Growing `BcSem` (a new opcode or primitive) | transcribe the `interp.c` arm / C primitive into `stepI`/`primF1Impl`, then `runbc` against the host `ocamlrun` on a difftest before any proof; update `Fragment.lean`'s ledger (`ledger_exact` is `decide`d) | here |
| A `caml_interprete` arm (Layer A) | `ArmSim.next`, one generated segment family per arm (`scripts/syi/disasm_to_segment.py` → `gen_segment.py`), arm boundaries from `scripts/census.py` | A1 |
| Bytecode segment or loop spec over `BcSem` (Layer B′, from ANY state) | `OCaml/Logic/Symbolic.lean`: reduce the real `step` on a template state with free tail/env/heap/world (`Run.iter (bcK P) k tmpl = .ok tmpl'` by `rfl`), resolve symbolic branches with `step_br_fall`/`step_br_taken`, tagged arithmetic with the `*_ofNat` lemmas + `omega`, loops with `loop_rule` (section invariant + rank). Model: `OCaml/Programs/CountLoop.lean` (any bound). Never hand-list intermediate states with `.succ (.mk rfl)` (rule O7), never enumerate start values | here |
| Bytecode-level proofs (Layer B′) | `bcModel P` + the MachWP rules; certified instruction entries and symbolic block rules GENERATED by `scripts/gen_bc_rules.py` from `dumpobj` + CODE; `CertifiedBlock.run` for code locality, `ApplicationSummary` for calls (never hand-stepped `step P s`) | here |
| Run laws of any step relation (determinism, append/snoc/prefix, unique halting, halts-or-diverges, `Reaches` ↔ `∃ n`, transport between systems) | the run kernel `OCaml/Run/Kernel.lean`: give the relation a `Graph` + `ConsPres`/`ClosPres` presentation and use `iter`'s laws; lossy lockstep squares by `iter_transport`; adapters `bcK` (`Semantics.lean`), `vsaK` (`Run/Machine.lean`), `mmK` (`Run/Model.lean`). Never induct on a run relation (rule O5) | here |
| A representation component that must survive a minor GC (relocation) | `OCaml/Vm/Reloc.lean`: write it as an `Eqv` combinator term and use `Eqv.transport` (models `objAt_reloc`, `heapRepr_reloc`). The bridge to the real collector is `ScanCoherent`, and it needs the NoForgery and RememberedComplete premises (`abstractions/ROUND-1.md` §2, L3′). Never unfold `reloc` by hand (rule O6) | here |
| New post/entry predicate | named-field `structure ... : Prop where` (models: `VmReprAt`, `LoadedAt`); never an anonymous ∃/∧ tower | — |
| Consuming a landed ∃/∧ tower | write ONE named destructuring lemma beside its definition | — |

## Laws

1. **Elaboration budget.** NEVER raise `maxHeartbeats` (rule R2), and raise
   `maxRecDepth` only for kernel evaluation of generated literals
   (`Opcode.lean`'s 149-element lists, `decide +kernel` runs). A heartbeat bump or whnf timeout means the construction is
   wrong:
   * check ground literals first, then use more abstraction;
   * use one small `decide` per fact;
   * reflect on the first-order write log; never whnf the Sail state;
   * emit terms, not tactic scripts.
2. **No `sorry`/`axiom`/`native_decide`/`bv_decide`.** A theorem not yet
   proved is a `def …_Statement : Prop` or a named obligation structure
   (`OcamlrunSim`, `ArmSim`), listed in PHASES.md. A genuine gap is a NAMED,
   typed premise with a doc comment saying what supplies it.
3. **Duplication is a signal.** If work feels duplicated or mechanical,
   STOP. An abstraction is missing; build or name it, then instantiate. Two
   similar proofs means factor before writing the third.
4. **Infeasible steps.** If a plan step is infeasible, return the
   machine-checked obstruction, not a workaround.
5. **Builds and axioms.**
   * Build with `lake build <Module>` for the modules you touch; run one
     build at a time.
   * On shared machines, run it under a memory cap
     (`systemd-run --user --scope -p MemoryMax=30G …`).
   * The axioms of every new theorem must be ⊆ {propext, Classical.choice,
     Quot.sound}; `scripts/check_all.sh` stage a3 checks this (`OCaml/Audit.lean`).
6. **Hide complexity by shape.** If you are counting conjuncts
   (`h.2.2.2.2…`) or tracking positional indices, the statement wants a
   named-field structure. Rules R6 and R7 enforce this.
7. **Generated files are generated.**
   * Every file with a `GENERATED by` header is rewritten by its script, and
     `scripts/check_all.sh` stage a5 fails on drift.
   * Change the generator or its input, never the output.

## Extending the discipline

- **New enforced rule.** Append a TSV line to `scripts/discipline_rules.tsv`
  (id, glob, regex or `COUNT>N:needle`, message). No code changes are needed.
- **Genuine exception.** Put `-- discipline: allow(<rule-id>) <justification>`
  on or above the line.
- **Copied files.** Files copied from ship-your-interpreter are exempt
  (`scripts/discipline_grandfather.txt` lists the copied `Vsa/` and `VsaIris/` files). A copied file that you change is no longer
  a copy: remove it from that list.
- **New abstraction.** When one lands or is ported, update the Availability
  column above. If it can be bypassed by hand, add a rule that catches the
  hand version.

## Documentation

- **README.md** holds the plan and the headline numbers.
- **VALIDATION.md** holds the Phase 1 measurements.
- **PLAN.md** holds the layers, the GC strategy and the risks.
- **PHASES.md** holds the plan, the obligations and the exit criteria.
  Update its obligations table when a statement is discharged.
- **ATTRIBUTION.md** records provenance.
- State the current design, commands and proof obligations. Omit discussion
  history. Use Git for session history.
