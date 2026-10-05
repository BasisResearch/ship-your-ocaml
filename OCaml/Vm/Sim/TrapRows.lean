import OCaml.Vm.Sim.Pushtrap
import OCaml.Vm.Sim.Poptrap
import OCaml.Vm.Sim.VmLog

/-!
# Loop-head simulation of PUSHTRAP

The four-word trap frame goes into the free part of the VM stack and the new
trap pointer into `Caml_state->trapsp`: `VmLogOk.of_windows` separates both
from the payload, `RuntimeFrame.windows` frames the runtime invariant.
`trapBound` (the trap pointer never exceeds the stack plus the new frame) is
a BcSem reachability invariant and stays named.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **The trap-frame push is separated and writable.** -/
theorem PushtrapWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {env : BitVec 64} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (trapBound : s.trap ≤ s.stack.length + 4)
    (space : 8 * (s.stack.length + 4) ≤ Layout.stackBytes) :
    PushtrapWriteOk P s c pl cp sp high dest env := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have hl := g.domainLow
  have hal := g.domainAligned
  have hda := g.domainArena
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have off : Layout.off_trapsp + 8 ≤ Layout.domainStateBytes := by decide
  have room : 32 ≤ sp := by omega
  have inside := pushtrap_log_in (sp := sp) (domain := (word c Layout.sym_Caml_state).toNat)
    (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))
    env (tag64 (BitVec.ofNat 63 s.extra)) room
  have ok := VmLogOk.of_windows g stack (by omega) inside (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
    · exact Or.inr ⟨Layout.off_trapsp, by decide, rfl⟩)
  have dn : ((word c Layout.sym_Caml_state) + BitVec.ofNat 64 Layout.off_trapsp).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Layout.off_trapsp) (by decide),
      Nat.mod_eq_of_lt (by simp only [Vsa.Sim.DlHeap.heapEnd] at hda; omega)]
  refine ⟨room, by omega, trapBound, by simpa using g.write stack (k := 4) (by decide) (by omega),
    by simpa using g.write stack (k := 1) (by decide) (by omega),
    by simpa using g.write stack (k := 2) (by decide) (by omega),
    by simpa using g.write stack (k := 3) (by decide) (by omega),
    by simp only [Vsa.Sim.DlHeap.heapEnd] at hda; omega, ⟨?_, ?_, ?_, ?_⟩, by omega,
    ⟨ok.core, ok.stack, fun l a o _ placed object => ok.heap l a o placed object⟩, ok.image, ok.bindings⟩
  all_goals rw [dn]
  all_goals simp only [Layout.sym_tohost, Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd,
    Layout.off_trapsp, Layout.domainStateBytes] at *
  all_goals omega

/-- **PUSHTRAP from the loop head.** -/
theorem pushtrap_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHTRAP) (fetch : P.code[s.pc + 1]? = some w)
    (trapBound : s.trap ≤ s.stack.length + 4)
    (space : 8 * (s.stack.length + 4) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHTRAP, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  change opt (target s.pc 0 w.toInt) (fun hd => .next { (s.adv 2) with
    stack := .code hd :: Val.ofInt (s.stack.length + 4 - s.trap) :: s.env :: Val.ofInt s.extra :: s.stack,
    trap := s.stack.length + 4 }) = .next s' at shape
  obtain ⟨dest, jump, -⟩ := opt_next shape
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨env, -, envWord⟩ := input.env
  have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
  have dom := rf.domainWord c input.runtime
  have hs := input.stack.1
  have hg := input.geometry.statics
  obtain ⟨c', run, running⟩ := pushtrap_step_arm
    (rf.windows _ (by
      intro w' hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact Or.inr ⟨Layout.off_trapsp, by decide, by rw [dom]⟩))
    input (OperandAt.of_fetch input.geometry fetch) jump envWord
    (PushtrapWriteOk.of_geometry input.geometry input.stack trapBound space) step
  exact ⟨c', run, h.of_plus run running⟩

/-- **A trap-pointer store is separated and writable.** -/
theorem TrapWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high trap : Nat} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (space : 8 * s.stack.length ≤ Layout.stackBytes) :
    TrapWriteOk P s c pl cp sp high trap := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have hl := g.domainLow
  have hal := g.domainAligned
  have hda := g.domainArena
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have off : Layout.off_trapsp + 8 ≤ Layout.domainStateBytes := by decide
  have inside : LogInW [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩]
      (trapLog (word c Layout.sym_Caml_state).toNat high trap) := by
    simp only [trapLog, LogInW, InsideW, or_false, and_true]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have ok := VmLogOk.of_windows g stack space inside (by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact Or.inr ⟨Layout.off_trapsp, by decide, rfl⟩)
  have dn : ((word c Layout.sym_Caml_state) + BitVec.ofNat 64 Layout.off_trapsp).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Layout.off_trapsp) (by decide),
      Nat.mod_eq_of_lt (by simp only [Vsa.Sim.DlHeap.heapEnd] at hda; omega)]
  refine ⟨by omega, by simp only [Vsa.Sim.DlHeap.heapEnd] at hda; omega, ⟨?_, ?_, ?_, ?_⟩,
    ⟨ok.core, ok.stack, fun l a o _ placed object => ok.heap l a o placed object⟩, ok.image, ok.bindings⟩
  all_goals rw [dn]
  all_goals simp only [Layout.sym_tohost, Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd,
    Layout.off_trapsp, Layout.domainStateBytes] at *
  all_goals omega

/-- **POPTRAP from the loop head.** -/
theorem poptrap_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .POPTRAP)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : stepI P s ⟨.POPTRAP, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · rename_i handler link env extra rest frame
    obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
    have dom := rf.domainWord c input.runtime
    have len : 1 < s.stack.length := by rw [frame]; simp
    obtain ⟨c', run, running⟩ := poptrap_step_arm
      (rf.windows _ (by
        intro w hw
        simp only [List.mem_singleton] at hw
        subst hw
        exact Or.inr ⟨Layout.off_trapsp, by decide, by rw [dom]⟩))
      input (rf.quiet c input.runtime) frame
      (input.geometry.read input.stack (stack_space input.stack space) (i := 1) len).window
      (TrapWriteOk.of_geometry input.geometry input.stack space) step
    exact ⟨c', run, h.of_plus run running⟩
  · cases shape

end OCaml.Vm.Sim
