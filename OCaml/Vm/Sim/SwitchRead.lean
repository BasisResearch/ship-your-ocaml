import OCaml.Vm.Sim.SwitchArithmetic
import OCaml.Vm.Sim.IsintArithmetic
import OCaml.Vm.Primitives.StringEncoding
import Vsa.Sim.RamReadValue

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives Sail

/-- Tag selection connects the abstract value to the header byte read by SWITCH.
Ordinary objects supply it below; atom/infix headers need their corresponding
representation facts. No execution or postcondition is assumed. -/
structure SwitchTag (s : St) (pl : Place) (c : Config) (a tag : Nat) : Prop where
  word : valWord pl s.accu = some (BitVec.ofNat 64 a)
  tagOf : tag? s.heap s.accu = some tag
  header : (byte c (a - 8)).toNat = tag
  even : a % 2 = 0

/-- A represented ordinary object's header supplies its SWITCH tag. -/
theorem SwitchTag.of_object {P : Prog} {s : St} {pl : Place} {c : Config} {cp : ChanPlace}
    {sp high l a : Nat} {o : Obj} (h : VmReprAt P s c pl cp sp high)
    (aligned : EvenPlace pl) (accu : s.accu = .ptr l 0)
    (placed : pl.φ l = some a) (object : s.heap.get? l = some o) :
    SwitchTag s pl c a o.tag := by
  have live : Live s.heap (roots P s) l :=
    Live.root (v := s.accu) (by simp [roots]) (by simp [accu, Val.loc?])
  have represented := (payload_of_repr h).object_at live placed object
  refine ⟨?_, ?_, ?_, aligned.heap l a placed⟩
  · simp [accu, valWord, placed]
  · simp [tag?, accu, object]
  · have extracted := congrArg BitVec.toNat (word_byte_extract c (a - 8) 0 (by decide))
    simp only [Nat.mul_zero, Nat.add_zero, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_zero] at extracted
    exact extracted.symm.trans represented.1.1

/-- Read the packed SWITCH size operand's low halfword from code representation. -/
theorem switch_count_read {P : Prog} {pl : Place} {i : Nat} {w : BitVec 32} {c d : Config}
    (operand : OperandAt P pl i w) (code : CodeRepr P.code pl.codeBase c)
    (memory : d.σ.mem = c.σ.mem) :
    zero_extend (m := 64) (bytesT2 d.σ.mem (pl.codeBase + 4 * i)) =
      BitVec.ofNat 64 (w.toNat % 65536) := by
  have read : bytesT d.σ.mem (pl.codeBase + 4 * i) 4 = w := by
    simpa only [bytesT_four_eq] using operand.read32 code memory
  have extracted := bytesT_extract d.σ.mem (pl.codeBase + 4 * i) 4 0 2 (by decide)
  simp only [read, Nat.mul_zero, Nat.add_zero, bytesT_two_eq] at extracted
  rw [← extracted]
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_zero]

/-- An even native pointer selects the block branch. -/
theorem switch_block_low_bit (a : Nat) (even : a % 2 = 0) :
    BitVec.ofNat 64 a &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  change (a % 2^64) % 2 = 0
  omega

/-- Header observation survives the dispatch memory frame and zero extension. -/
theorem SwitchTag.read {s : St} {pl : Place} {c d : Config} {a tag : Nat}
    (h : SwitchTag s pl c a tag) (memory : d.σ.mem = c.σ.mem) :
    zero_extend (m := 64) (bytesT1 d.σ.mem (a - 8)) = BitVec.ofNat 64 tag := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, memory]
  have observed := congrArg (fun n => n % 2^64) h.header
  simpa only [byte_total] using observed

end OCaml.Vm.Sim
