import OCaml.Refinement
import OCaml.Bytecode.Load
import OCaml.Vm.Sim.PrimitiveBindingData

namespace OCaml.Vm.Sim.PrimitiveBinding
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- Snapshot of the pre-binding loaded relation, retained for the checked
obstruction. Production LoadedAt additionally requires PrimitiveBindings. -/
structure UnboundLoadedAt (L : Layout) (P : Prog) (c : Config) (pl : Place) (cp : ChanPlace)
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


def UnboundLoaded (L : OCaml.Layout) (P : Prog) (c : Config) : Prop :=
  ∃ (pl : Place) (cp : ChanPlace) (high : Nat), UnboundLoadedAt L P c pl cp high

/-- The original headline shape over the legacy pre-binding relation. -/
def UnboundRefinement (L : OCaml.Layout) (B : Budget) : Prop :=
  ∀ P c, UnboundLoaded L P c → Good P → Fits B P →
    (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c)

/-- The legacy loaded relation forgets the primitive-name table. -/
theorem loaded_prims {L : OCaml.Layout} {P : Prog} {c : Config}
    (h : UnboundLoaded L P c) (prims : Array String) : UnboundLoaded L {P with prims := prims} c := by
  obtain ⟨pl, cp, high, h⟩ := h
  exact ⟨pl, cp, high, h.atEntry, h.argCode, h.argSize, h.codeBase, h.code,
    h.globals, h.stackHigh, h.externSp, h.trapsp, h.heap, h.world, h.platform⟩

private theorem good_of_halts {P : Prog} {out : String} {e : Nat}
    (h : BcHalts P out e) : Good P := by
  obtain ⟨w, hh, _⟩ := bcHalts_iff.1 h
  intro s hs
  obtain ⟨k, hk⟩ := hs
  have unique (r : Res) (hr : bcK P s = .error r) : r = .halt e w :=
    (show Run.HaltsK (bcK P) P.init r from ⟨s, ⟨k, stepsN_iff.1 hk⟩, hr⟩).unique hh
  constructor
  · intro bad
    have impossible := unique .unsupported (by simp only [bcK, bad])
    cases impossible
  · intro bad
    have impossible := unique .wrong (by simp only [bcK, bad])
    cases impossible

private theorem halts_of_check {P : Prog} {fuel e : Nat}
    (h : (runTo P fuel P.init).map (fun r => (r.1, bytesToString r.2.console)) = some (e, "")) :
    BcHalts P "" e := by
  match hr : runTo P fuel P.init, h with
  | some (e', w), h =>
    simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hw⟩ := h
    exact hw ▸ bcHalts_of_runTo hr

private theorem word_halts : BcHalts wordProbe "" 64 :=
  halts_of_check (fuel := 3) (by decide +kernel)
private theorem swapped_halts : BcHalts swappedProbe "" 63 :=
  halts_of_check (fuel := 3) (by decide +kernel)

private def probeBudget : Budget := ⟨0, wordProbe.heap0.words⟩

private theorem fits_of_checked {P : Prog}
    (stop : (match Run.iter (bcK P) 3 P.init with | .ok _ => false | .error _ => true) = true)
    (check : ∀ k : Fin 3, (match Run.iter (bcK P) k P.init with
      | .ok s => decide (s.stack.length ≤ probeBudget.stackWords ∧ s.heap.words ≤ probeBudget.heapWords)
      | .error _ => true) = true) : Fits probeBudget P := by
  have done : ∃ o, Run.iter (bcK P) 3 P.init = .error o := by
    cases hx : Run.iter (bcK P) 3 P.init with
    | ok s =>
      simp only [hx] at stop
      cases stop
    | error o => exact ⟨o, rfl⟩
  obtain ⟨o, ho⟩ := done
  intro s hs
  obtain ⟨k, hk⟩ := hs
  have hi := stepsN_iff.1 hk
  have hb := Run.iter_ok_lt ho hi
  have hc := check ⟨k, hb⟩
  simp only [hi] at hc
  exact of_decide_eq_true hc

private theorem word_fits : Fits probeBudget wordProbe :=
  fits_of_checked (by decide +kernel) (by decide +kernel)
private theorem swapped_fits : Fits probeBudget swappedProbe :=
  fits_of_checked (by decide +kernel) (by decide +kernel)

/-- Identical code/heap/world with different primitive names produce different
observable exits. Determinism rules out the unchanged headline for the legacy
primitive-unbound Loaded contract whenever this tiny program is loaded. -/
theorem primitive_binding_obstruction {L : OCaml.Layout} {B : Budget} {c : Config}
    (capacity : wordProbe.heap0.words ≤ B.heapWords)
    (loaded : UnboundLoaded L wordProbe c) : ¬ UnboundRefinement L B := by
  intro H
  have fits {P : Prog} (h : Fits probeBudget P) : Fits B P := by
    intro s hs
    obtain ⟨stack, heap⟩ := h s hs
    exact ⟨Nat.le_trans stack (Nat.zero_le _), Nat.le_trans heap capacity⟩
  have other : UnboundLoaded L swappedProbe c := loaded_prims loaded swappedProbe.prims
  have first := (H wordProbe c loaded (good_of_halts word_halts) (fits word_fits)).1 "" 64
  have second := (H swappedProbe c other (good_of_halts swapped_halts) (fits swapped_fits)).1 "" 63
  have impossible := (first.1 word_halts).deterministic (second.1 swapped_halts)
  omega

/-- The repaired predicate retains all old loaded facts. -/
theorem loaded_forget_primitives {L : OCaml.Layout} {P : Prog} {c : Config}
    (h : Loaded L P c) : UnboundLoaded L P c := by
  obtain ⟨pl, cp, high, h⟩ := h
  exact ⟨pl, cp, high, h.atEntry, h.argCode, h.argSize, h.codeBase, h.code,
    h.globals, h.stackHigh, h.externSp, h.trapsp, h.heap, h.world, h.platform⟩

/-- The new binding field excludes the two conflicting primitive tables from
one machine state, without changing OcamlrunRefinement's definition. -/
theorem loaded_probes_disjoint {L : OCaml.Layout} {c : Config} :
    ¬ (Loaded L wordProbe c ∧ Loaded L swappedProbe c) := by
  intro ⟨first, second⟩
  have a := first.primitives.get (i := 370) (name := "caml_sys_const_word_size")
    (by decide +kernel) PrimitiveEntries.entry_caml_sys_const_word_size
  have b := second.primitives.get (i := 370) (name := "caml_sys_const_int_size")
    (by decide +kernel) PrimitiveEntries.entry_caml_sys_const_int_size
  exact (by decide : BitVec.ofNat 64 Layout.sym_caml_sys_const_word_size ≠
    BitVec.ofNat 64 Layout.sym_caml_sys_const_int_size) (a.symm.trans b)

end OCaml.Vm.Sim.PrimitiveBinding
