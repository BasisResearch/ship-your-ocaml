import OCaml.Vm.Sim.Muldi3
import OCaml.Vm.Primitives.Call
import OCaml.Vm.Boot.Startup.RuntimeReady

/-!
# Direct calls under allocator readiness

A generated `jal` site keeps a0-boot's `RuntimeReady` (`ready_call`), and a
`jal __muldi3` site returns with the product, the same memory and the
register frame (`ready_muldi3`). Both are stated for any call site, so every
`__muldi3` call in the runtime reuses them.
-/

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Boot.Startup OCaml.Vm.Sim LeanRV64DExecutable

/-- After a direct call: readiness with the new link, the target reached,
the carried argument registers, memory unchanged. -/
structure CallDone (H : List (Nat × Nat)) (capacity : Nat) (sp : BitVec 64) (call : CallInstr)
    (args : GRegs) (before after : Config) : Prop where
  ready : RuntimeReady H capacity sp call.link after
  pc : after.σ.regs.get? Register.PC = some call.target
  regs : GHolds after.σ args
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 1 → gprGet after.σ n = gprGet before.σ n

/-- **A direct call keeps readiness.** -/
theorem ready_call {H capacity sp ra} {call : CallInstr} (shape : CallShape call) (decode : CallDecode call)
    {c : Config} (pins : CallPins call c) (ready : RuntimeReady H capacity sp ra c)
    (args : GRegs) (holds : GHolds c.σ args) (keys : KeysOK (keysG args)) (avoid : KeysAvoidRa args)
    (value : BitVec 64) (result : lookupG 10 args = some value) (linkAligned : call.link.toNat % 4 = 0) :
    FnSummary call.pc (fun d => d = c) (CallDone H capacity sp call args c) := by
  apply (call_registers_summary shape decode c pins ready.good ready.image ready.tick ready.minstret
    args holds keys avoid result).weaken (fun _ h => h)
  intro after post
  have frame (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (other : n ≠ 1) : gprGet after.σ n = gprGet c.σ n :=
    post.toEffectPost.gpr_frame (by decide) n lower upper (by simpa using other)
  have stack : gprGet after.σ 2 = some sp := (frame 2 (by decide) (by decide) (by decide)).trans ready.stack
  refine ⟨?_, post.pc, post.regs.2, post.memory, post.output, frame⟩
  exact ready.effect post (by decide) (by simp [keysG]) (by decide) stack post.regs.1 linkAligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)

/-- After `__muldi3` returns to a call's link. -/
structure MulDone (H : List (Nat × Nat)) (capacity : Nat) (sp link x y : BitVec 64) (before after : Config) :
    Prop where
  ready : RuntimeReady H capacity sp link after
  pc : after.σ.regs.get? Register.PC = some link
  result : gprGet after.σ 10 = some (x * y)
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10, 11, 12, 13] → gprGet after.σ n = gprGet before.σ n

/-- **A `jal __muldi3` site keeps readiness** and returns the product. -/
theorem ready_muldi3 {H capacity sp ra x y} {call : CallInstr} (shape : CallShape call)
    (decode : CallDecode call) (target : call.target = 0x80037234#64) {c : Config} (pins : CallPins call c)
    (ready : RuntimeReady H capacity sp ra c) (left : gprGet c.σ 10 = some x) (right : gprGet c.σ 11 = some y)
    (linkAligned : call.link.toNat % 4 = 0) :
    FnSummary call.pc (fun d => d = c) (MulDone H capacity sp call.link x y c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  obtain ⟨c1, run1, C⟩ := (ready_call shape decode pins ready [(10, x), (11, y)] ⟨left, right, trivial⟩
    (by simp only [keysG, List.map]; decide) (by simp [KeysAvoidRa, keysG]) x rfl linkAligned).run d ⟨pc, rfl⟩
  have input : Muldi3Input x y call.link c1 :=
    { toLeafInput := C.ready.toLeafInput, left := C.regs.1, right := C.regs.2.1 }
  obtain ⟨c2, run2, a1, a2, a3, P⟩ := (muldi3_registers input).run c1 ⟨by rw [← target]; exact C.pc, rfl⟩
  have frame (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (other : n ∉ [10, 11, 12, 13]) :
      gprGet c2.σ n = gprGet c1.σ n :=
    P.toEffectPost.gpr_frame (by decide) n lower upper other
  have stack : gprGet c2.σ 2 = some sp :=
    (frame 2 (by decide) (by decide) (by decide)).trans C.ready.stack
  have link : gprGet c2.σ 1 = some call.link :=
    (frame 1 (by decide) (by decide) (by decide)).trans C.ready.raReg
  refine ⟨c2, run1.trans run2, ⟨?_, P.pc, P.regs.1, P.memory.trans C.memory, P.output.trans C.output, ?_⟩⟩
  · exact C.ready.effect P (by decide) (by simp [keysG]) (by decide) stack link linkAligned
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  · intro n lower upper other
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at other
    rw [frame n lower upper (by simp; omega), C.frame n lower upper other.1]

end OCaml.Vm.Gc
