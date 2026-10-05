import OCaml.Vm.Sim.StackLog
import OCaml.Vm.Sim.PayloadRestore

/-!
# Certificates for arm logs that also write VM-owned `Caml_state` fields

Exception, re-entry and C-call setup arms write both the free part of the VM
stack and a few `Caml_state` fields (`trapsp`, `extern_sp`, ...). For any log
whose windows are of those two kinds, `VmLogOk.of_windows` derives every
payload separation fact the arms need from the placement geometry.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem outWRange_of_forall {ws : List W} {a n : Nat} (h : ∀ w ∈ ws, a + n ≤ w.lo ∨ w.hi ≤ a) :
    OutWRange ws a n := by
  induction ws with
  | nil => trivial
  | cons w ws ih => exact ⟨h w (by simp), ih fun w' hw => h w' (by simp [hw])⟩

/-- An arm write window: in the free part of the VM stack allocation, or one
VM-owned `Caml_state` field. -/
def VmWriteWindow (c : Config) (sp high : Nat) (w : W) : Prop :=
  (high - Layout.stackBytes ≤ w.lo ∧ w.hi ≤ sp) ∨
    ∃ off ∈ vmDomainOffsets,
      w = ⟨(word c Layout.sym_Caml_state).toNat + off, (word c Layout.sym_Caml_state).toNat + off + 8⟩

/-- Everything such a log leaves untouched. -/
structure VmLogOk (log : List WEntry) (P : Prog) (s : St) (c : Config) (pl : Place)
    (cp : ChanPlace) (sp : Nat) : Prop where
  core : PayloadCoreOutside log P s c pl cp
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → ObjectOutside log a o
  image : ImageOutside log
  bindings : BindingsOutside log P c

/-- **One derivation for every VM write log.** -/
theorem VmLogOk.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : StackGeometry P s c pl cp high)
    (stackRepr : StackRepr c pl sp high s.stack) (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (inside : LogInW ws log)
    (vm : ∀ w ∈ ws, VmWriteWindow c sp high w) : VmLogOk log P s c pl cp sp := by
  have hs := stackRepr.1
  have hg := g.statics
  have hl := g.domainLow
  have hd := g.domain.1
  -- one target is apart from every window when it is apart from both kinds
  have apart : ∀ a n,
      (a + n ≤ high - Layout.stackBytes ∨ sp ≤ a) →
      (∀ off ∈ vmDomainOffsets, a + n ≤ (word c Layout.sym_Caml_state).toNat + off ∨
        (word c Layout.sym_Caml_state).toNat + off + 8 ≤ a) →
      OutLRange log a n := by
    intro a n hstack hdom
    apply outLRange_of_windows inside
    apply outWRange_of_forall
    intro w hw
    rcases vm w hw with ⟨lo, hi⟩ | ⟨off, member, rfl⟩
    · omega
    · exact hdom off member
  have offs : ∀ off ∈ vmDomainOffsets, 64 ≤ off ∧ off + 8 ≤ Layout.domainStateBytes ∧
      (off + 8 ≤ Layout.off_stack_high ∨ Layout.off_stack_high + 8 ≤ off) := by decide
  have staticN : ∀ a n, a + n ≤ Layout.sym_bss_end → OutLRange log a n := fun a n ha =>
    apart a n (Or.inl (by omega)) fun off member => Or.inl (by omega)
  have static : ∀ a, a + 8 ≤ Layout.sym_bss_end → OutLRange log a 8 := fun a ha => staticN a 8 ha
  -- a range apart from the whole `Caml_state` record and from the stack window
  have record : ∀ a n, (a + n ≤ high - Layout.stackBytes ∨ sp ≤ a) →
      OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
        (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] a n → OutLRange log a n := by
    intro a n hstack hrec
    apply apart a n hstack
    intro off member
    have ho := offs off member
    have hr := hrec.1
    dsimp only at hr
    omega
  refine ⟨⟨static _ (by decide), ?_, static _ (by decide), static _ (by decide), static _ (by decide),
    fun i w hw => ?_, fun id ch a hch hcp => ?_⟩, fun i v hv => ?_, fun l a o placed object => ?_,
    ⟨staticN _ _ (by decide), staticN _ _ (by decide)⟩, ⟨static _ (by decide), fun j name hj => ?_⟩⟩
  · have hh : Layout.off_stack_high + 8 ≤ Layout.domainStateBytes := by decide
    simp only [stackWindow] at hd
    apply apart _ 8 (by omega)
    intro off member
    have := offs off member
    omega
  · have h1 := (g.code i w hw).1
    simp only [stackWindow] at h1
    exact record _ 4 (by omega) (by
      have h2 := g.domainCode.1
      have bound : i < P.code.size := by simpa using (Array.getElem?_eq_some_iff.mp hw).1
      exact ⟨by dsimp only at h2 ⊢; omega, trivial⟩)
  · have h1 := (g.channels id ch a hch hcp).1
    simp only [stackWindow] at h1
    exact record _ _ (by omega) (g.domainChannels id ch a hch hcp)
  · have bound := (List.getElem?_eq_some_iff.mp hv).1
    apply apart _ 8 (Or.inr (by omega))
    intro off member
    have := offs off member
    simp only [stackWindow] at hd
    have hb : Layout.stackBytes ≤ high := by omega
    omega
  · have h1 := (g.heap l a o placed object).1
    have h2 := (g.domainHeap l a o placed object).1
    simp only [stackWindow] at h1
    dsimp only at h2
    exact ⟨record _ 8 (by omega) ⟨by dsimp only; omega, trivial⟩,
      record _ _ (by omega) ⟨by dsimp only; omega, trivial⟩⟩
  · have h1 := (g.primitives j name hj).1
    simp only [stackWindow] at h1
    exact record _ 8 (by omega) (g.domainPrims j name hj)

end OCaml.Vm.Sim
