import OCaml.Vm.Platform
import Vsa.Sim.WriteLogNF

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- The primitive's write ranges are disjoint from both immutable ELF sections. -/
structure ImageOutside (log : List WEntry) : Prop where
  text : OutLRange log Image.textBase Image.textSize
  rodata : OutLRange log Image.rodataBase Image.rodataSize

/-- Reuse the fixed-section range transport for a checked write log. -/
theorem image_of_writeLog {c c' : Config} {log : List WEntry}
    (image : ExecutableImage c) (outside : ImageOutside log)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : ExecutableImage c' := by
  constructor
  · apply image.text.transport
    intro a hlo hhi
    rw [memory]
    exact writeLog_out _ _ _ (outL_of_range outside.text hlo hhi)
  · apply image.rodata.transport
    intro a hlo hhi
    rw [memory]
    exact writeLog_out _ _ _ (outL_of_range outside.rodata hlo hhi)

end OCaml.Vm.Primitives
