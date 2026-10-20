import OCaml.Vm.Gc.ReadyCalls
import OCaml.Vm.Sim.SignedDivision
import OCaml.Vm.Boot.Startup.RuntimeKept
import OCaml.Vm.Boot.Startup.GprsSame

/-! A `jal __divdi3` site under allocator readiness returns the signed
quotient with the same memory (`ready_divdi3`), the `__divdi3` counterpart of
`OCaml.Vm.Gc.ready_muldi3`. Stated for any call site. -/
namespace OCaml.Vm.Boot.Startup
variable {live : Nat → Prop}
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Sim OCaml.Vm.Gc LeanRV64DExecutable

/-- After `__divdi3` returns to a call's link. -/
structure DivDone (live : Nat → Prop) (H : List (Nat × Nat)) (capacity : Nat) (sp link x y : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReadyL live H capacity sp link after
  pc : after.σ.regs.get? Register.PC = some link
  result : gprGet after.σ 10 = some (x.sdiv y)
  memory : after.σ.mem = before.σ.mem
  same : GprsSame before after ([1, 5, 10, 11, 12, 13] ++ [1])

/-- Nonnegative operands: `__divdi3` falls into `__udivdi3`, which returns
through the caller's link (no sign fixup, so `ra` survives). -/
theorem ready_divdi3 {H capacity sp ra x y} {call : CallInstr} (shape : CallShape call)
    (decode : CallDecode call) (target : call.target = 0x80037298#64) {c : Config} (pins : CallPins call c)
    (ready : RuntimeReadyL live H capacity sp ra c) (left : gprGet c.σ 10 = some x) (right : gprGet c.σ 11 = some y)
    (nonzero : y ≠ 0) (hx : x.msb = false) (hy : y.msb = false) (linkAligned : call.link.toNat % 4 = 0) :
    FnSummary call.pc (fun d => d = c) (DivDone live H capacity sp call.link x y c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  obtain ⟨c1, run1, C⟩ := (ready_call shape decode pins ready [(10, x), (11, y)] ⟨left, right, trivial⟩
    (by simp only [keysG]; decide) (by simp [KeysAvoidRa, keysG]) x rfl linkAligned).run d ⟨pc, rfl⟩
  have input : SignedDivisionInput x y call.link c1 :=
    { toLeafInput := C.ready.toLeafInput, left := C.regs.1, right := C.regs.2.1, nonzero := nonzero }
  obtain ⟨n, c2, run2, prepared⟩ := sdiv_pos_pos_prepare input (by rw [← target]; exact C.pc) hx hy
  obtain ⟨c3, run3, divided⟩ := signed_division_core prepared
  have positive : divisionNegative .quotient x y = false := by simp [divisionNegative, hx, hy]
  have P := signed_division_done divided positive
  have link : gprGet c3.σ 1 = some call.link := by
    have h := divided.raReg
    simp only [divisionReturn, positive, Bool.false_eq_true, ite_false] at h
    exact h
  have first : GprsSame d c1 [1] := ⟨fun n lo hi out => C.frame n lo hi (by simpa using out)⟩
  have second : GprsSame c1 c3 [1, 5, 10, 11, 12, 13] := GprsSame.of_stepFrame (by decide) P.frame
  refine ⟨c3, run1.trans (run2.toSteps.trans run3), ?_⟩
  exact ⟨C.ready.of_kept (log := []) (windows := []) ⟨P.good, P.image, P.minstret, link, linkAligned, P.tick⟩
      ((second.same 2 (by decide) (by decide) (by decide)).trans C.ready.stack) P.kept
      (P.frame.frame _ (by decide)) P.memory trivial (fun _ _ => trivial) trivial trivial (fun _ _ => trivial),
    P.pc, P.result, P.memory.trans C.memory, first.trans second⟩

end OCaml.Vm.Boot.Startup
