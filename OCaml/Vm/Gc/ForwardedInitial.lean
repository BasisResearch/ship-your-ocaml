import OCaml.Vm.Gc.ForwardedLoopState
import OCaml.Vm.Gc.ScanPayload

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Initialize the relocated scan from concrete platform/code/register pins.
The copied prefix is empty; both memory and native frames are reflexive. -/
theorem LoopAt.initial {R domain a b count start c expected}
    (data : LoopData R domain a b count start c expected)
    (good : GoodState c.σ)
    (minstret : ∃ v, c.σ.regs.get? Register.minstret = some v)
    (tick : c.tick < 2)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem)
    (oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem)
    (bound : start ≤ count)
    (pc : PCAt (if start < count then FieldCopy.pc else FieldCopy.exitPc) c)
    (registers : GHolds c.σ (carried (cursor R a start start))) :
    LoopAt R a b count start c expected start c := by
  refine ⟨FieldCopy.ScanAtWith.initial good minstret tick code bound pc ?_, oldifyCode, registers⟩
  have pins : GHolds c.σ (FieldCopy.regs (scanPtr a start) (R 18) (R 19) (BitVec.ofNat 64 start)) :=
    ⟨gholds_lookup _ registers rfl, gholds_lookup _ registers rfl,
      gholds_lookup _ registers rfl, gholds_lookup _ registers rfl, True.intro⟩
  simpa only [data.delta, data.target] using pins

end OCaml.Vm.Gc.ForwardedField
