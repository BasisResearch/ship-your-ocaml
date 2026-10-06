import OCaml.Vm.Sim.PushRetaddr
import OCaml.Vm.Sim.StackLog

/-!
# Loop-head simulation of PUSH_RETADDR

The three-word return frame is pushed into the free part of the VM stack
allocation: separation from `StackGeometry.payload`, writability from
`StackGeometry.write`, runtime framing from `RuntimeFrame.push`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **The return-frame push is separated and writable.** -/
theorem RetaddrWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {env : BitVec 64} (g : ArmGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack)
    (space : 8 * (s.stack.length + 3) ≤ Layout.stackBytes) : RetaddrWriteOk P s c pl cp sp dest env := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have hb : 24 ≤ Layout.sym_bss_end := by decide
  have room : 24 ≤ sp := by omega
  have inside := logInW_widen (lo := high - Layout.stackBytes) (hi := sp)
    (retaddr_log_in (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env (tag64 (BitVec.ofNat 63 s.extra)) room)
    (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      dsimp only
      omega)
  have w1 := g.write stack (k := 1) (by decide) (by omega)
  have w2 := g.write stack (k := 2) (by decide) (by omega)
  have w3 := g.write stack (k := 3) (by decide) (by omega)
  exact ⟨room, by omega, by simpa using w2, by simpa using w3, by simpa using w1,
    g.payload stack inside, g.image inside, .of_free g.toStackGeometry stack inside,
    g.bindings stack inside⟩

/-- **PUSH_RETADDR from the loop head.** -/
theorem push_retaddr_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSH_RETADDR) (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * (s.stack.length + 3) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSH_RETADDR, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  change opt (target s.pc 0 w.toInt) (fun r => .next { (s.adv 2) with
    stack := .code r :: s.env :: Val.ofInt s.extra :: s.stack }) = .next s' at shape
  obtain ⟨dest, jump, -⟩ := opt_next shape
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨env, -, envWord⟩ := input.env
  obtain ⟨c', run, running⟩ := push_retaddr_step_arm
    (by simpa using rf.push input (k := 3) space) input
    (OperandAt.of_fetch input.geometry.toArmGeometry fetch) jump envWord
    (RetaddrWriteOk.of_geometry input.geometry.toArmGeometry input.stack space) step
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
