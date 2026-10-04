import OCaml.Vm.Boot.Startup.FindCompare
import OCaml.Vm.Boot.Startup.NameData
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The signed word difference used by _findenv_r is the scanned length
for every name shorter than the positive signed-word range. -/
theorem findCompareCount_cursor (name : BitVec 64) (length : Nat) (small : length < 2^31) :
    findCompareCount name (nameCursor name length) = BitVec.ofNat 64 length := by
  unfold findCompareCount nameCursor
  have lowAdd : Sail.BitVec.extractLsb (name + BitVec.ofNat 64 length) 31 0 =
      Sail.BitVec.extractLsb name 31 0 + BitVec.ofNat 32 length := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, BitVec.toNat_ofNat,
      BitVec.toNat_add, Nat.shiftRight_zero]
    omega
  rw [lowAdd, BitVec.add_comm (Sail.BitVec.extractLsb name 31 0), BitVec.add_sub_cancel]
  change (BitVec.ofNat 32 length).signExtend 64 = BitVec.ofNat 64 length
  have msb : (BitVec.ofNat 32 length).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
end OCaml.Vm.Boot.Startup
