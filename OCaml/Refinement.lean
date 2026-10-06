import OCaml.Bytecode.GcSafe
import OCaml.Budget
import OCaml.Vm.Platform
import Vsa.Densify
import OCaml.Run.Machine
import OCaml.Vm.Caller
import OCaml.Run.Clock
import OCaml.Vm.Sim.Invariant
import OCaml.Vm.Sim.ArmGeometry
import OCaml.Vm.Gc.G1RoomDefs
import OCaml.Vm.Sim.Invocation

/-!
# Layer A: `ocamlrun` refines `BcSem`

The statement, its obligations, and everything that follows from the
obligations by determinism alone.

* `Loaded L P c` — the analogue of ship-your-interpreter's `Loaded` at
  `interp_run`: the machine is at `caml_interprete`'s entry, called by
  `caml_main` with the loaded program `P` (code, primitive table, global
  data in the heap, `argv`), with an empty VM stack.
* `OcamlrunRefinement L B` — **the Layer A theorem statement**: for every
  loaded program that stays inside the fragment and inside the resource
  budget `B`, the machine's halting behaviours are exactly `BcSem`'s and it
  diverges exactly when `BcSem` does.
* `OcamlrunSim L B` — forward simulation (the part that needs the binary):
  `BcSem` behaviours are machine behaviours. `ocamlrun_refinement_of_sim`
  derives the full equivalence from it (proved here).
* `ArmSim L B P` — the per-instruction obligations, one per `caml_interprete`
  arm (plus entry and the exits): from `Running L P s c` and `step P s = .next
  s'`, the machine reaches (in at least one step) a configuration
  representing `s'`. `simOfArms` derives `OcamlrunSim` from them (proved
  here). These are what the exponentiating layer generates, one family of
  segments per arm (PLAN.md §Layer A).

Why the budget: `BcSem`'s heap and stack are unbounded; the machine raises
`Out_of_memory`/`Stack_overflow` (or dies) when it runs out. `Fits B P`
bounds the words `BcSem` allocates and its stack depth along every run —
`B` is instantiated from the ELF's RAM layout and the baked-in
`OCAMLRUNPARAM` (PLAN.md §GC strategy: with the minor heap large enough
and collections excluded, allocated words are the right measure; once the
collector is verified, `Fits` is restated on live words).
-/

namespace OCaml

open OCaml.Bytecode OCaml.Vm Vsa.Machine

/-- Facts about the runtime at the cut point that `BcSem` does not
mention: the collector's and allocator's own invariants (minor heap
bounds, free lists, page table, `caml_something_to_do` clear, …). Kept
abstract, as ship-your-interpreter keeps `Layout.atInterpRun`; the Layer A
proof instantiates it with what `caml_main` establishes. -/
structure Layout where
  runtimeOk : Config → Prop
  /-- the configured heap budget: the free nursery holds every word the
  budget still allows (`Gc.G1Room`, no collection under G1) -/
  budget : Budget

/-- Every reachable state is within the budget. -/
def Fits (B : Budget) (P : Prog) : Prop :=
  ∀ s, Reach P s → s.stack.length ≤ B.stackWords ∧ s.heap.words ≤ B.heapWords

/-- **The loop geometry**: the arm geometry of a representation witness and the
G1 nursery room for the layout's budget. -/
structure LoopGeometry (L : Layout) (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop extends Vm.Sim.ArmGeometry P s c pl cp high where
  room : Vm.Gc.G1Room L.budget s c

/-- **The program is loaded** at `caml_interprete`'s entry
(`caml_interprete(caml_start_code, caml_code_size)`, `startup_byt.c`):
the ra/a0/a1 of that call, the code in memory, the initial VM state's
heap/globals/world laid out, an empty VM stack, and the runtime's own
invariants. -/
structure LoadedAt (L : Layout) (P : Prog) (c : Config) (pl : Place) (cp : ChanPlace)
    (high : Nat) : Prop where
  atEntry : pcOf c = some (BitVec.ofNat 64 Layout.sym_caml_interprete)
  /-- `a0 = caml_start_code` -/
  argCode : gpr c 10 = some (BitVec.ofNat 64 pl.codeBase)
  /-- `a1 = caml_code_size` (bytes) -/
  argSize : gpr c 11 = some (BitVec.ofNat 64 (4 * P.code.size))
  codeBase : (word c Layout.sym_caml_start_code).toNat = pl.codeBase
  code : ∀ i w, P.code[i]? = some w → word32 c (pl.codeBase + 4 * i) = w
  globals : valWord pl P.globals = some (word c Layout.sym_caml_global_data)
  /-- an empty VM stack: `stack_high = extern_sp = trapsp` -/
  stackHigh : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high
  externSp : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp)).toNat = high
  trapsp : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat = high
  heap : HeapRepr c pl cp P P.init
  world : WorldRepr c cp P.init.world
  platform : PlatformOk L.runtimeOk c
  primitives : PrimitiveBindings P c
  atomBase : (word c Layout.sym_caml_atom_table).toNat = pl.atomBase
  /-- caml_main called caml_interprete: return address, native frame, separation of
  the prologue's writes, dispatch clock and HTIF idleness (`OCaml/Vm/Caller.lean`) -/
  caller : ∃ sp callerRegs mainSaved, InterpCaller P c pl cp high sp callerRegs mainSaved
  /-- the stack/heap/code/nursery placement of the initial state (`OCaml/Vm/Sim/ArmGeometry.lean`) -/
  geometry : LoopGeometry L P P.init c pl cp high

def Loaded (L : Layout) (P : Prog) (c : Config) : Prop :=
  ∃ (pl : Place) (cp : ChanPlace) (high : Nat), LoadedAt L P c pl cp high

/-- Startup supplies the same platform predicate consumed at the loop head.
The prologue additionally establishes `LoopRegisters` and the VM data. -/
theorem Loaded.platform {L : Layout} {P : Prog} {c : Config} (h : Loaded L P c) :
    PlatformOk L.runtimeOk c := by
  obtain ⟨pl, cp, high, entry⟩ := h
  exact entry.platform

/-- Startup binds every PRIM name to the function pointer used by C_CALL. -/
theorem Loaded.primitives {L : Layout} {P : Prog} {c : Config} (h : Loaded L P c) :
    PrimitiveBindings P c := by
  obtain ⟨pl, cp, high, entry⟩ := h
  exact entry.primitives

/-- The runtime component of a loaded witness, independent of its placement. -/
theorem Loaded.runtime {L : Layout} {P : Prog} {c : Config} (h : Loaded L P c) :
    L.runtimeOk c := h.platform.runtime

/-- The represented state together with the loop geometry of the same
placement (`OCaml/Vm/Sim/Invariant.lean`, `ArmGeometry.lean`). -/
def StackPlaced (L : Layout) (P : Prog) (s : St) (c : Config) : Prop :=
  ∃ pl cp sp high, VmReprAt P s c pl cp sp high ∧ LoopGeometry L P s c pl cp high

/-- The loop-head representation: VM data and platform facts are separate
named parts. No platform field depends on the abstract heap placement.
`stack` is the VM stack geometry of some representation witness
(`OCaml/Vm/Sim/Invariant.lean`), from which the arms' stack premises follow
(`InvariantUse.lean`). -/
structure Running (L : Layout) (P : Prog) (s : St) (c : Config) : Prop where
  data : VmRepr P s c
  platform : PlatformOk L.runtimeOk c
  loop : LoopRegisters c
  stack : StackPlaced L P s c
  /-- the native invocation of `caml_interprete` is intact (`Invocation.lean`) -/
  native : Vm.Sim.NativePlaced c

/-- **Layer A (statement).** `ocamlrun` refines `BcSem`: for every loaded
program inside the fragment (`Good`), budget (`Fits`) and observational
GC-safety domain (`GcSafe`), the machine
halts with `(out, e)` iff `BcSem` does, and diverges iff `BcSem` does. -/
def OcamlrunRefinement (L : Layout) (B : Budget) : Prop :=
  ∀ P c, Loaded L P c → Good P → Fits B P → GcSafe P →
    (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c)

/-- **Forward simulation obligations** (the part that needs the binary). -/
structure OcamlrunSim (L : Layout) (B : Budget) : Prop where
  term_sim : ∀ P c, Loaded L P c → Good P → Fits B P → GcSafe P →
    ∀ out e, BcHalts P out e → Halts c out e
  div_sim : ∀ P c, Loaded L P c → Good P → Fits B P → GcSafe P → BcDiverges P → Diverges c

/-- Per program: forward simulation gives the full equivalence, by
determinism of both sides and `halts_or_diverges` (a `Good` program halts or
diverges). -/
theorem refines_of_forward {P : Prog} {c : Config} (hg : Good P)
    (fwd : ∀ out e, BcHalts P out e → Halts c out e) (dv : BcDiverges P → Diverges c) :
    (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c) := by
  rcases halts_or_diverges P hg with ⟨out', e', hb⟩ | hbd
  · refine ⟨fun out e => ⟨fwd out e, fun hm => ?_⟩, dv, fun hd => (Diverges.not_halts hd (fwd out' e' hb)).elim⟩
    obtain ⟨rfl, rfl⟩ := hm.deterministic (fwd out' e' hb); exact hb
  · exact ⟨fun out e => ⟨fwd out e, fun hm => (Diverges.not_halts (dv hbd) hm).elim⟩, dv, fun _ => hbd⟩

/-- **Layer A from forward simulation**. -/
theorem ocamlrun_refinement_of_sim {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    OcamlrunRefinement L B := fun P c hL hg hf hgc =>
  refines_of_forward hg (H.term_sim P c hL hg hf hgc) (H.div_sim P c hL hg hf hgc)

/-- The dense-memory form, as ship-your-interpreter states its headline
(`Loaded` of `fillZero c`: absent RAM bytes read as the zero they are). -/
theorem ocamlrun_refinement_fillZero {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    ∀ P c, Loaded L P (Vsa.Densify.fillZero c) → Good P → Fits B P → GcSafe P →
      (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c) := by
  intro P c hL hg hf hgc
  obtain ⟨h1, h2⟩ := ocamlrun_refinement_of_sim H P _ hL hg hf hgc
  exact ⟨fun out e => (h1 out e).trans (Vsa.Densify.halts_fillZero c out e).symm,
    h2.trans (Vsa.Densify.diverges_fillZero c).symm⟩

/-! ## Per-arm obligations -/

/-- At least one machine step. -/
def Plus (c c' : Config) : Prop := ∃ n, StepsN (n + 1) c c'

/-- **The loop-head invariant of the per-arm obligations**: `Running` plus
the platform tick counter that the generated segment lemmas consume. The
clock is a run invariant (`StepsN.tick_lt`), so arms conclude `Running` and
`LoopAt.of_plus` restores it. Ownership: docs/lanes/F1-split.md. -/
structure LoopAt (L : Layout) (P : Prog) (s : St) (c : Config) : Prop where
  running : Running L P s c
  clock : c.tick < 2

/-- An arm's `Running` conclusion re-establishes the loop-head invariant. -/
theorem LoopAt.of_plus {L : Layout} {P : Prog} {s s' : St} {c c' : Config}
    (h : LoopAt L P s c) (run : Plus c c') (running : Running L P s' c') : LoopAt L P s' c' :=
  ⟨running, let ⟨_, hn⟩ := run; hn.tick_lt h.clock⟩

/-- **The per-instruction obligations** for one program: entry, one per
`step` outcome. Each field is what one family of generated segment proofs
discharges (the `.next` field splits by `caml_interprete` arm). -/
structure ArmSim (L : Layout) (B : Budget) (P : Prog) : Prop where
  entry : ∀ c, Loaded L P c → Good P → Fits B P → GcSafe P → ∃ c', Plus c c' ∧ LoopAt L P P.init c'
  next : ∀ s s' c, Reach P s → Good P → Fits B P → GcSafe P → LoopAt L P s c → step P s = .next s' →
    ∃ c', Plus c c' ∧ LoopAt L P s' c'
  halt : ∀ s e w c, Reach P s → Good P → Fits B P → GcSafe P → LoopAt L P s c → step P s = .halt e w →
    Halts c (bytesToString w.console) e

/-! Machine run laws: corollaries of the run kernel (`OCaml/Run/Machine.lean`). -/

theorem _root_.Vsa.Machine.StepsN.append {n m : Nat} {a b c : Config} (h1 : StepsN n a b) (h2 : StepsN m b c) :
    StepsN (n + m) a c :=
  Run.vsa_stepsN_iff.2 (by rw [Run.iter_add, Run.vsa_stepsN_iff.1 h1]; exact Run.vsa_stepsN_iff.1 h2)

theorem _root_.Vsa.Machine.Steps.trans' {a b c : Config} (h1 : Steps a b) (h2 : Steps b c) : Steps a c :=
  Run.vsa_steps_iff.2 ((Run.vsa_steps_iff.1 h1).trans (Run.vsa_steps_iff.1 h2))

theorem _root_.Vsa.Machine.Halts.of_steps {c c' : Config} {out : String} {e : Nat} (h : Steps c c')
    (h' : Halts c' out e) : Halts c out e :=
  let ⟨σ, hh, ho⟩ := Run.vsa_halts_iff.1 h'; Run.vsa_halts_iff.2 ⟨σ, hh.of_reach (Run.vsa_steps_iff.1 h), ho⟩

theorem _root_.Vsa.Machine.StepsN.prefix' : ∀ {m k : Nat} {a c : Config}, StepsN (m + k) a c → ∃ b, StepsN m a b :=
  fun h => let ⟨b, hb⟩ := Run.iter_prefix (Run.vsa_stepsN_iff.1 h); ⟨b, Run.vsa_stepsN_iff.2 hb⟩

/-- **Simulation by an arbitrary relation** `R` for one program started
from `c0`: entry, one obligation per `step` outcome. `ArmSim` is its
instance at `LoopAt` (`ArmSim.simR`); a fragment may use a stronger loop
invariant (`OCaml/RefinementF1.lean`). -/
structure SimR (P : Prog) (c0 : Config) (R : St → Config → Prop) : Prop where
  entry : ∃ c', Plus c0 c' ∧ R P.init c'
  next : ∀ s s' c, Reach P s → R s c → step P s = .next s' → ∃ c', Plus c c' ∧ R s' c'
  halt : ∀ s e w c, Reach P s → R s c → step P s = .halt e w → Halts c (bytesToString w.console) e

/-- Along a `BcSem` run of `k` steps from a related state, the machine
runs at least `k` steps to a configuration related to the end state. -/
theorem run_simR {P : Prog} {R : St → Config → Prop}
    (next : ∀ s s' c, Reach P s → R s c → step P s = .next s' → ∃ c', Plus c c' ∧ R s' c') :
    ∀ {k : Nat} {s s' : St} {c : Config}, Reach P s → StepsN P k s s' → R s c →
      ∃ n c', k ≤ n ∧ StepsN n c c' ∧ R s' c' := by
  intro k s s' c hr hs hv
  -- discipline: allow(O5-run-induction) run_simR is the simulation induction (one obligation per BcSem step), not run algebra
  induction hs generalizing c with
  | zero => exact ⟨0, c, Nat.le_refl _, .zero _, hv⟩
  | @succ k a b d st _ ih =>
    obtain ⟨e⟩ := st
    obtain ⟨c1, ⟨n1, h1⟩, hv1⟩ := next a b c hr hv e
    obtain ⟨hn, hk⟩ := hr
    obtain ⟨n2, c2, hle, h2, hv2⟩ := ih ⟨hn + 1, hk.snoc (.mk e)⟩ hv1
    exact ⟨n1 + 1 + n2, c2, by omega, h1.append h2, hv2⟩

theorem SimR.term {P : Prog} {c0 : Config} {R : St → Config → Prop} (H : SimR P c0 R) :
    ∀ out e, BcHalts P out e → Halts c0 out e := by
  intro out e ⟨s, w, ⟨k, hk⟩, hst, ho⟩
  obtain ⟨c1, ⟨n0, h0⟩, hv0⟩ := H.entry
  obtain ⟨n, c', -, hn, hv⟩ := run_simR H.next ⟨0, .zero _⟩ hk hv0
  exact Halts.of_steps (h0.toSteps.trans' hn.toSteps) (ho ▸ H.halt s e w c' ⟨k, hk⟩ hv hst)

theorem SimR.div {P : Prog} {c0 : Config} {R : St → Config → Prop} (H : SimR P c0 R) :
    BcDiverges P → Diverges c0 := by
  intro hd m
  obtain ⟨c1, ⟨n0, h0⟩, hv0⟩ := H.entry
  obtain ⟨s, hs⟩ := hd m
  obtain ⟨n, c', hle, hn, -⟩ := run_simR H.next ⟨0, .zero _⟩ hs hv0
  obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le (show m ≤ n0 + 1 + n by omega)
  exact Vsa.Machine.StepsN.prefix' (hd' ▸ h0.append hn)

/-- **Per-program Layer A from any simulation relation.** -/
theorem SimR.refines {P : Prog} {c0 : Config} {R : St → Config → Prop} (H : SimR P c0 R)
    (hg : Good P) :
    (∀ out e, BcHalts P out e ↔ Halts c0 out e) ∧ (BcDiverges P ↔ Diverges c0) :=
  refines_of_forward hg H.term H.div

/-- `ArmSim` is the `LoopAt` instance of `SimR`. -/
theorem ArmSim.simR {L : Layout} {B : Budget} {P : Prog} {c : Config} (A : ArmSim L B P)
    (hL : Loaded L P c) (hg : Good P) (hf : Fits B P) (hgc : GcSafe P) : SimR P c (LoopAt L P) where
  entry := A.entry c hL hg hf hgc
  next s s' c hr hv e := A.next s s' c hr hg hf hgc hv e
  halt s e w c hr hv h := A.halt s e w c hr hg hf hgc hv h

/-- Along a `BcSem` run of `k` steps from a represented state, the machine
runs at least `k` steps to a configuration representing the end state. -/
theorem run_sim {L : Layout} {B : Budget} {P : Prog} (A : ArmSim L B P) (hg : Good P)
    (hf : Fits B P) (hgc : GcSafe P) :
    ∀ {k : Nat} {s s' : St} {c : Config}, Reach P s → StepsN P k s s' → LoopAt L P s c →
      ∃ n c', k ≤ n ∧ StepsN n c c' ∧ LoopAt L P s' c' :=
  run_simR fun s s' c hr hv e => A.next s s' c hr hg hf hgc hv e

/-- **Forward simulation from the per-arm obligations.** -/
theorem simOfArms {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) : OcamlrunSim L B where
  term_sim P _ hL hg hf hgc := ((A P).simR hL hg hf hgc).term
  div_sim P _ hL hg hf hgc := ((A P).simR hL hg hf hgc).div

/-- **Layer A from the per-arm obligations.** -/
theorem ocamlrun_refinement_of_arms {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) :
    OcamlrunRefinement L B :=
  ocamlrun_refinement_of_sim (simOfArms A)

end OCaml
