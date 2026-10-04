import OCaml.Vm.Sim.ReadOnly
import OCaml.Vm.Sim.MainExitSegment
import OCaml.Vm.Sim.MainExitPins
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- main resumes after caml_main and calls caml_do_exit with status zero. -/
structure MainExitInput (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  pc : pcOf c = some (0x80001df0#64)

def mainExitWrites : List Register := [Register.x1, Register.x10] ++ noiseRegs

/-- Exact call-site state for the process-exit implementation. -/
structure MainExitPost (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (0x8001c5c8#64)
  status : gpr after 10 = some 0#64
  returnAddress : gpr after 1 = some (0x80001df8#64)
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut mainExitWrites before.σ after.σ

/-- Execute the pinned two-instruction main-to-exit call boundary. -/
theorem main_exit {c : Config} (h : MainExitInput c) :
    ∃ count after, StepsN count c after ∧ MainExitPost c after := by
  have bp : SegSt (0x80001df0#64) []
      (fun σ => Vsa.Sim.Code.CamlMainExitLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, trivial, h.good.minstret, h.tick, main_exit_loaded h.image, rfl, rfl⟩
  obtain ⟨count, after, _, run, post⟩ := tr_main_exit c.σ.mem c.σ c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  exact ⟨count, after, run, post.good,
    image_of_writeLog (log := []) h.image ⟨trivial, trivial⟩ memory, post.tick, post.pcAt,
    PinsHold.get post.pins ⟨1, by simp⟩, PinsHold.get post.pins ⟨0, by simp⟩,
    memory, frame.widenChecked (allowed := mainExitWrites) (by decide)⟩

end OCaml.Vm.Sim
