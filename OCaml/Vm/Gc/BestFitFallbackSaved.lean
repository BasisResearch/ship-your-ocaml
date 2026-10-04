import OCaml.Vm.Gc.BestFitMissing
import OCaml.Vm.Gc.SaveBank

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives

/-- Values installed by the fallback prologue's generated native-save log. -/
def bankRegs (R : Nat → BitVec 64) (bits : BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 14 then R 10 else if n = 12 then bits else R n

def saveShape : SaveBank.Shape saves :=
  ⟨saves.getLast!,by decide,by decide,by decide,by decide⟩

theorem effect_bank (R : Nat → BitVec 64) (bits : BitVec 64) :
    effect R bits = SaveBank.log (frameSp R) (bankRegs R bits) saves := rfl

theorem effect_high {R bits c} (input : Input R c) :
    ∀ e ∈ effect R bits, Layout.sym_tohost + 16 ≤ e.1 := by
  rw [effect_bank]
  exact SaveBank.high input.windows

/-- Every original fallback save reads back after the actual ffs call. -/
theorem Searched.saved {R before after} (post : Searched R before after)
    (input : Input R before) (cell : Nat × Nat) (member : cell ∈ saves) :
    word after (frameSp R + BitVec.ofNat 64 cell.2).toNat = bankRegs R (bitmap before) cell.1 := by
  rw [word,post.memory,effect_bank]
  exact saveShape.read before.σ.mem (frameSp R) (bankRegs R (bitmap before)) input.windows cell member

end OCaml.Vm.Gc.BestFitFallback
