import OCaml.Vm.Primitives.SmallNursery
import OCaml.Vm.Primitives.DoubleLayout

namespace OCaml.Vm.Primitives.SmallAllocation
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- The C allocator truncates its tag argument to unsigned 32 bits. -/
theorem tagWord_ofNat (tag : Nat) (bound : tag < 256) :
    tagWord (BitVec.ofNat 64 tag) = BitVec.ofNat 64 tag := by
  apply BitVec.eq_of_toNat_eq
  simp only [tagWord, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- Small block sizes and byte tags produce the represented header. -/
theorem blockHeader_ok (size tag : Nat) (small : size ≤ 256) (tagBound : tag < 256) :
    HeaderOk ((BitVec.ofNat 64 size <<< 10) + tagWord (BitVec.ofNat 64 tag)) size tag := by
  rw [tagWord_ofNat tag tagBound]
  unfold HeaderOk
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  constructor <;> omega

/-- Allocation initializes the header before the caller writes its fields. -/
theorem NurseryPost.header {ra size tag domain young before after}
    (post : NurseryPost ra (BitVec.ofNat 64 size) (BitVec.ofNat 64 tag) domain young before after)
    (small : size ≤ 256) (tagBound : tag < 256) :
    HeaderOk (word after (nurseryHeader young (BitVec.ofNat 64 size)).toNat) size tag := by
  have value : word after (nurseryHeader young (BitVec.ofNat 64 size)).toNat =
      (BitVec.ofNat 64 size <<< 10) + tagWord (BitVec.ofNat 64 tag) := by
    change bytesT after.σ.mem _ 8 = _
    rw [post.memory, constructorLog, writeLog_append]
    exact word_writeLog _ _ _
  rw [value]
  exact blockHeader_ok size tag small tagBound

end OCaml.Vm.Primitives.SmallAllocation
