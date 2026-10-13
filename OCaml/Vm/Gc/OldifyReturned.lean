import OCaml.Vm.Gc.ForwardedCall
import OCaml.Vm.Gc.FreshSingle

/-! # The common return of `caml_oldify_one`

Every proved route of `caml_oldify_one` (already forwarded, fresh with queue
insertion, fresh single-field) ends in the same machine shape: the caller's
registers restored, the return to `ra`, the code kept, memory the route's
write log applied. `OldifyReturned R log` names that shape, and each route's
post projects to it with its own log. Loops over root slots and the mopup
queue compose `caml_oldify_one` calls through it; the route-specific slot
fact travels separately. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- **`caml_oldify_one` returned** with memory `writeLog before log`. Integer
registers are described by `registers` (the caller's ABI view); every other
non-noise register is kept. -/
structure OldifyReturned (R : Nat → BitVec 64) (log : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (OldifyEntry.callerRegs R)
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n, n < 32 → (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

/-- A route's frame over its own write set gives the common frame, once that
set names only integer registers. -/
theorem OldifyReturned.frame_of {before after : Config} {ws : List Nat} (small : ∀ n ∈ ws, n < 32)
    (native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ ws, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n, n < 32 → (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r :=
  fun r noise gprs => native r noise fun n hn => gprs n (small n hn)

/-- The already-forwarded route. -/
theorem ForwardedCall.Post.returned {R : Nat → BitVec 64} {before after : Config}
    (p : ForwardedCall.Post R before after) :
    OldifyReturned R (ForwardedCall.effect R before) before after :=
  ⟨p.good, p.minstret, p.tick, p.code, p.pc, p.registers, p.memory, p.output,
    OldifyReturned.frame_of (by decide) p.native⟩

/-- The fresh route with queue insertion. -/
theorem Fresh.Enqueued.returned {R : Nat → BitVec 64} {qs : List PendingCopy} {pl : Place}
    {before after : Config} (p : Fresh.Enqueued R qs pl before after) :
    OldifyReturned R (Fresh.allocationEffect R before ++ Fresh.enqueueEffect R qs before) before after :=
  ⟨p.good, p.minstret, p.tick, p.code, p.pc, p.registers, p.memory, p.output,
    OldifyReturned.frame_of (by decide) p.native⟩

/-- The fresh single-field route. -/
theorem Fresh.SingleResult.returned {R : Nat → BitVec 64} {target : BitVec 64} {log : List WEntry}
    {before after : Config} (p : Fresh.SingleResult R target log before after) :
    OldifyReturned R ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++ Fresh.singleEffect R target log before)
      before after :=
  ⟨p.good, p.minstret, p.tick, p.code, p.pc, p.registers, p.memory, p.output,
    OldifyReturned.frame_of (by decide) p.native⟩

end OCaml.Vm.Gc
