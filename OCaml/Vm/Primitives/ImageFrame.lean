import OCaml.Vm.Platform
import Vsa.Sim.WriteLogNF

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- The primitive's write ranges are disjoint from both immutable ELF sections. -/
structure ImageOutside (log : List WEntry) : Prop where
  text : OutLRange log Image.textBase Image.textSize
  rodata : OutLRange log Image.rodataBase Image.rodataSize

theorem insert_isSome {m : Std.ExtHashMap Nat (BitVec 8)} {k : Nat} {v : BitVec 8} {a : Nat}
    (h : (m[a]?).isSome) : ((m.insert k v)[a]?).isSome := by
  rw [Std.ExtHashMap.getElem?_insert]
  split
  · rfl
  · exact h

/-- A write log only inserts: present bytes stay present. -/
theorem writeLog_isSome (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (a : Nat)
    (h : (m[a]?).isSome) : ((writeLog m log)[a]?).isSome := by
  induction log generalizing m with
  | nil => exact h
  | cons e rest ih =>
    apply ih
    obtain ⟨x, n, d⟩ := e
    unfold applyW
    split <;> repeat (first | exact h | apply insert_isSome)

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
  · intro i hi
    rw [memory]
    exact writeLog_isSome _ _ _ (image.impure i hi)

end OCaml.Vm.Primitives
