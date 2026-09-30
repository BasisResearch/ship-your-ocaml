# Lane a1-arms

## NEEDS KIRAN

The requested nonvacuous `ArmSim L B P` is impossible as currently stated.
Choose/coordinate the shared invariant repair with A0 boot and A6 GC before
resuming the arm proofs. Recommended: keep the data representation separate
and parameterize the simulation by a named invariant carrying the running
platform, executable image, dispatch registers and allocator state; require
entry to establish it and each next arm to preserve it. This changes the
shared Layer A contract and the other lanes' obligations, not just an A1
implementation detail. No permission to weaken the theorem is inferred.

## Proved

All names below are in namespace `OCaml.Vm.Sim`, in
`OCaml/Vm/Sim/Obstruction.lean`:

* `repr_forceExit` (line 24): changing HTIF done/exit code preserves `VmRepr`.
* `forceExit_halted` (line 43): the resulting machine immediately halts.
* `forceExit_not_plus` (line 51): no positive machine segment starts there.
* `armSim_not_repr` (line 59): `ArmSim` contradicts any represented reachable
  state of a good program within budget.
* `loaded_not_armSim` (line 82): `Loaded L P c`, `Good P`, and `Fits B P`
  imply `¬ ArmSim L B P`, using entry to obtain the represented initial state.

The obstruction holds for every runtime predicate `L.runtimeOk`; strengthening
only `Loaded` cannot fix the next/halt fields. It does not refute the eventual
machine refinement theorem under a repaired simulation invariant.

## Validation

* Read lane brief, COMMON.md, CLAUDE.md, PLAN.md, PHASES.md; ran
  `scripts/abs_inventory.sh`; rebased on origin/main.
* `lake build OCaml.Vm.Sim.Obstruction` passed under `MemoryMax=24G`;
  reported module elaboration 1.2 seconds. No heartbeat changes or holes.
* All five theorems added to `OCaml/Audit.lean`; imported by `OCaml.lean`.
* Proof discipline and abstraction gate passed. This is an invariant
  obstruction, not an a8 per-arm cost failure; no arm-family cost claimed.
* `lake build OCaml` passed under `MemoryMax=24G` (484 jobs).
* Landing uses `scripts/integrate.sh` under an enclosing 24 GB scope; its
  complete build, axiom, discipline, image and abstraction gates must pass
  before it pushes this commit to main.

## Open / next

No entry, next, halt arm, F1 machine refinement, or machine `whileMin` theorem
has been proved. The existing `whileMin_bcSem` is bytecode-level only.
The PHASES.md ledger now records the checked obstruction explicitly.

After the shared invariant is repaired, consume A0's image/decode and boot
premises and generate one F1 family per measured build. The existing
`disasm_to_sites.py` supports addi/addiw/add/sub/subw but still lacks the
requested shift/addw/tagged ALU classes; generator help executes successfully.
Dispatch, allocation fast-path and primitive summaries remain open.
The existing generator machinery does not resolve the false arm precondition;
no hand-stepped substitute or circular primitive obligation was introduced.
