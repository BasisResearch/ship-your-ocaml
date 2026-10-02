import OCaml.Bytecode.GcSafe
import OCaml.Vm.Platform
import Vsa.Densify
import OCaml.Run.Machine

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

/-- Resource budget. -/
structure Budget where
  stackWords : Nat
  heapWords : Nat

/-- Every reachable state is within the budget. -/
def Fits (B : Budget) (P : Prog) : Prop :=
  ∀ s, Reach P s → s.stack.length ≤ B.stackWords ∧ s.heap.words ≤ B.heapWords

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

/-- The loop-head representation: VM data and platform facts are separate
named parts. No platform field depends on the abstract heap placement. -/
structure Running (L : Layout) (P : Prog) (s : St) (c : Config) : Prop where
  data : VmRepr P s c
  platform : PlatformOk L.runtimeOk c
  loop : LoopRegisters c

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

/-- **Layer A from forward simulation**, by determinism of both sides and
`halts_or_diverges` (a `Good` program halts or diverges). -/
theorem ocamlrun_refinement_of_sim {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    OcamlrunRefinement L B := by
  intro P c hL hg hf hgc
  have fwd := H.term_sim P c hL hg hf hgc
  have dv := H.div_sim P c hL hg hf hgc
  rcases halts_or_diverges P hg with ⟨out', e', hb⟩ | hbd
  · refine ⟨fun out e => ⟨fwd out e, fun hm => ?_⟩, dv, fun hd => (Diverges.not_halts hd (fwd out' e' hb)).elim⟩
    obtain ⟨rfl, rfl⟩ := hm.deterministic (fwd out' e' hb); exact hb
  · exact ⟨fun out e => ⟨fwd out e, fun hm => (Diverges.not_halts (dv hbd) hm).elim⟩, dv, fun _ => hbd⟩

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

/-- **The per-instruction obligations** for one program: entry, one per
`step` outcome. Each field is what one family of generated segment proofs
discharges (the `.next` field splits by `caml_interprete` arm). -/
structure ArmSim (L : Layout) (B : Budget) (P : Prog) : Prop where
  entry : ∀ c, Loaded L P c → Good P → Fits B P → GcSafe P → ∃ c', Plus c c' ∧ Running L P P.init c'
  next : ∀ s s' c, Reach P s → Good P → Fits B P → GcSafe P → Running L P s c → step P s = .next s' →
    ∃ c', Plus c c' ∧ Running L P s' c'
  halt : ∀ s e w c, Reach P s → Good P → Fits B P → GcSafe P → Running L P s c → step P s = .halt e w →
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

/-- Along a `BcSem` run of `k` steps from a represented state, the machine
runs at least `k` steps to a configuration representing the end state. -/
theorem run_sim {L : Layout} {B : Budget} {P : Prog} (A : ArmSim L B P) (hg : Good P)
    (hf : Fits B P) (hgc : GcSafe P) :
    ∀ {k : Nat} {s s' : St} {c : Config}, Reach P s → StepsN P k s s' → Running L P s c →
      ∃ n c', k ≤ n ∧ StepsN n c c' ∧ Running L P s' c' := by
  intro k s s' c hr hs hv
  -- discipline: allow(O5-run-induction) run_sim is the simulation induction (one ArmSim per BcSem step), not run algebra
  induction hs generalizing c with
  | zero => exact ⟨0, c, Nat.le_refl _, .zero _, hv⟩
  | @succ k a b d st _ ih =>
    obtain ⟨e⟩ := st
    obtain ⟨c1, ⟨n1, h1⟩, hv1⟩ := A.next a b c hr hg hf hgc hv e
    obtain ⟨hn, hk⟩ := hr
    obtain ⟨n2, c2, hle, h2, hv2⟩ := ih ⟨hn + 1, hk.snoc (.mk e)⟩ hv1
    exact ⟨n1 + 1 + n2, c2, by omega, h1.append h2, hv2⟩

/-- **Forward simulation from the per-arm obligations.** -/
theorem simOfArms {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) : OcamlrunSim L B where
  term_sim := by
    intro P c hL hg hf hgc out e ⟨s, w, ⟨k, hk⟩, hst, ho⟩
    obtain ⟨c0, ⟨n0, h0⟩, hv0⟩ := (A P).entry c hL hg hf hgc
    obtain ⟨n, c', -, hn, hv⟩ := run_sim (A P) hg hf hgc ⟨0, .zero _⟩ hk hv0
    exact Halts.of_steps (h0.toSteps.trans' hn.toSteps) (ho ▸ (A P).halt s e w c' ⟨k, hk⟩ hg hf hgc hv hst)
  div_sim := by
    intro P c hL hg hf hgc hd m
    obtain ⟨c0, ⟨n0, h0⟩, hv0⟩ := (A P).entry c hL hg hf hgc
    obtain ⟨s, hs⟩ := hd m
    obtain ⟨n, c', hle, hn, -⟩ := run_sim (A P) hg hf hgc ⟨0, .zero _⟩ hs hv0
    obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le (show m ≤ n0 + 1 + n by omega)
    exact Vsa.Machine.StepsN.prefix' (hd' ▸ h0.append hn)

/-- **Layer A from the per-arm obligations.** -/
theorem ocamlrun_refinement_of_arms {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) :
    OcamlrunRefinement L B :=
  ocamlrun_refinement_of_sim (simOfArms A)

end OCaml
