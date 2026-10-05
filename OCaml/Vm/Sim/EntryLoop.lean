import OCaml.Vm.Sim.EntryNative
import OCaml.Vm.Sim.ReadOnly

/-!
# `ArmSim.entry`: from `Loaded` to the loop head

The native entry run (`entry_native`) writes only inside `entryFootprint`:
the interpreter's native frame, `caml_callback_depth` and
`Caml_state->external_raise`. The caller premise (`InterpCaller`) says that
footprint misses everything the initial representation observes, so the
loaded payload frames to the loop head, where the VM registers are those of
`P.init`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- A footprint entry's range misses whatever the footprint misses. -/
theorem outLRange_mem {fp : List WEntry} {f : WEntry} {a n : Nat} (hf : f ∈ fp)
    (h : OutLRange fp a n) : a + n ≤ f.1 ∨ f.1 + f.2.1 ≤ a := by
  induction fp with
  | nil => simp at hf
  | cons g fp ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · exact ih hf h.2

/-- **Cover**: a log whose entries lie inside footprint entries misses whatever
the footprint misses. -/
theorem outLRange_of_cover {log fp : List WEntry} {a n : Nat}
    (cover : ∀ e ∈ log, ∃ f ∈ fp, f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1)
    (h : OutLRange fp a n) : OutLRange log a n := by
  induction log with
  | nil => trivial
  | cons e log ih =>
    obtain ⟨f, hf, lo, hi⟩ := cover e (by simp)
    have := outLRange_mem hf h
    exact ⟨by omega, ih (fun e' he' => cover e' (by simp [he']))⟩

/-- The payload separation transfers along a cover. -/
theorem PayloadOutside.cover {log fp : List WEntry} {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {sp : Nat} (h : PayloadOutside fp P s c pl cp sp)
    (cover : ∀ e ∈ log, ∃ f ∈ fp, f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1) :
    PayloadOutside log P s c pl cp sp where
  domain := outLRange_of_cover cover h.domain
  stackHigh := outLRange_of_cover cover h.stackHigh
  trapsp := outLRange_of_cover cover h.trapsp
  codeBase := outLRange_of_cover cover h.codeBase
  atomBase := outLRange_of_cover cover h.atomBase
  globals := outLRange_of_cover cover h.globals
  code i w hi := outLRange_of_cover cover (h.code i w hi)
  stack i v hi := outLRange_of_cover cover (h.stack i v hi)
  heap l a o hl ha ho := ⟨outLRange_of_cover cover (h.heap l a o hl ha ho).header,
    outLRange_of_cover cover (h.heap l a o hl ha ho).payload⟩
  channels id ch a hc ha := outLRange_of_cover cover (h.channels id ch a hc ha)

/-- Entry writes only inside its footprint. -/
theorem entryLog_cover {sp : Nat} {regs : Nat → BitVec 64} {a0 : BitVec 64} {c : Config}
    (frame : EntryFrame sp) :
    ∀ e ∈ entryLog sp regs a0 c, ∃ f ∈ entryFootprint sp (word c Layout.sym_Caml_state).toNat,
      f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1 := by
  obtain ⟨b1, b2, b3⟩ := frame.nat
  intro e he
  simp only [entryLog, entrySaveLog, entryPrepLog, setjmpLog, entryResumeLog, Layout.interpSavedRegs,
    List.map, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact ⟨(sp - Layout.interpFrameBytes, Layout.interpFrameBytes, 0), by simp [entryFootprint],
        by simp only [Layout.interpFrameBytes, Layout.interpSaveOffset, entryBuffer]; omega,
        by simp only [Layout.interpFrameBytes, Layout.interpSaveOffset, entryBuffer]; omega⟩
    | exact ⟨(Layout.sym_caml_callback_depth, 4, 0), by simp [entryFootprint], Nat.le_refl _, Nat.le_refl _⟩
    | exact ⟨((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise, 8, 0),
        by simp [entryFootprint], Nat.le_refl _, Nat.le_refl _⟩

end OCaml.Vm.Sim
