import OCaml.Vm.Sim.ReadOnly
import Vsa.Sim.FrameWriteSet
import OCaml.Vm.Primitives.ImageFrame
import Vsa.Sim.ChainFrameOut

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Only the four fixed loop registers and machine counters change. -/
def loopSetupWrites : List Register := [Register.x19, Register.x20, Register.x22, Register.x24] ++ noiseRegs

/-- Entry to the common loop-register initialization used by prologue and raises. -/
structure LoopSetupInput (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  pc : pcOf c = some (0x80001f40#64)
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = some 0#4
  /-- the unpinned callee-saved registers hold values -/
  saved : ∀ n ∈ unpinnedSaved, (gpr c n).isSome

/-- The exact read-only frame and initialized dispatch registers at loop entry. -/
structure LoopSetupPost (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  head : pcOf after = some (BitVec.ofNat 64 Layout.loopHead)
  loop : LoopRegisters after
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut loopSetupWrites before.σ after.σ

/-- The setup writes none of the unpinned callee-saved registers. -/
theorem loopSetup_saved {before after : Config} (frame : StepFrameOut loopSetupWrites before.σ after.σ)
    (saved : ∀ n ∈ unpinnedSaved, (gpr before n).isSome) : ∀ n ∈ unpinnedSaved, (gpr after n).isSome := by
  intro n hn
  have e : gpr after n = gpr before n := by
    simp only [unpinnedSaved, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl
    exact frame.frame (gprReg 26) (by decide)
  rw [e]; exact saved n hn

end OCaml.Vm.Sim
