import OCaml.Vm.Sim.GrabNurseryInput
import OCaml.Vm.Sim.GrabAllocPrefixSegment
import OCaml.Vm.Sim.GrabAllocPrefixPins
import OCaml.Vm.Sim.GrabAllocPrefixLayout
import OCaml.Vm.Sim.Immediate

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- GRAB's actual insufficient-arity prefix reserves its closure in the
nursery and establishes the initializer's native inputs. -/
theorem grab_reserve {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit : Nat} {required : BitVec 32}
    (h : ArmInput L P s .GRAB c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) required)
    (short : s.extra < required.toInt.toNat)
    (space : GrabNurseryInput s.extra a domain limit c)
    (dp : DispatchPost c .GRAB (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ nb after, StepsN nb d after ∧ GrabReserved c s.extra a domain after := by
  have nonnegative : 0 ≤ required.toInt := by omega
  have domainRead : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have youngRead := space.youngWrite.read
  have youngAddress : BitVec.ofNat 64 domain + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (domain + Layout.off_young_ptr) := by
    rw [BitVec.ofNat_add]; rfl
  have domainNat : (BitVec.ofNat 64 domain).toNat = domain := by
    simpa only [Layout.off_young_limit, Nat.add_zero] using space.limitRead.toNat
  have limitRead : RamReadAt domain 8 := by
    simpa only [Layout.off_young_limit, Nat.add_zero] using space.limitRead
  have readWord (address : Nat) : sign_extend (m := 64) (bytesT8 d.σ.mem address) = word c address := by
    simp only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have domainValue := (readWord Layout.sym_Caml_state).trans space.domainValue
  have youngValue := (readWord (domain + Layout.off_young_ptr)).trans space.youngValue
  have limitValue : sign_extend (m := 64) (bytesT8 d.σ.mem domain) = BitVec.ofNat 64 limit := by
    simpa only [Layout.off_young_limit, Nat.add_zero] using (readWord (domain + Layout.off_young_limit)).trans space.limitValue
  have headerNat : (BitVec.ofNat 64 (a - 8)).toNat = a - 8 :=
    Nat.mod_eq_of_lt (by have upper := space.headerWrite.upper; omega)
  have limitNat : (BitVec.ofNat 64 limit).toNat = limit :=
    Nat.mod_eq_of_lt (by have upper := space.headerWrite.upper; have capacity := space.capacity; omega)
  have capacity : zopz0zI_u (BitVec.ofNat 64 (a - 8)) (BitVec.ofNat 64 limit) = false := by
    apply bltu_false_of_ge
    rw [headerNat, limitNat]
    exact space.capacity
  have bp : SegSt (0x800027f4#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x18, BitVec.ofNat 64 s.extra⟩]
      (fun σ => Vsa.Sim.Code.CamlGrabAllocPrefixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x18 (by decide)).trans h.extra, trivial⟩,
      dp.good.minstret, dp.tick, grab_alloc_prefix_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  obtain ⟨nextMemory, written⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (domain + Layout.off_young_ptr) (sdData_val (BitVec.ofNat 64 (a - 8))) := ⟨_, rfl⟩
  have run := tr_grab_alloc_prefix (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
    (BitVec.ofNat 64 s.extra) d.σ.mem d.σ
  simp only [grab_alloc_prefix_domain, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat, domainRead.toNat] at run
  have first := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (sign_extend (m := 64) required) (by rw [operand.read32 h.code dp.memory])
    (grab_alloc_guard s.extra required (by have small := space.small; omega) nonnegative short)
    domainRead.lower domainRead.upper domainRead.htif (BitVec.ofNat 64 domain) domainValue.symm
  simp only [youngAddress, youngRead.toNat, domainNat] at first
  have reserve := first youngRead.lower youngRead.upper youngRead.htif
    (BitVec.ofNat 64 (a + 8 * (s.extra + 4))) youngValue.symm
    limitRead.lower limitRead.upper limitRead.htif (BitVec.ofNat 64 limit) limitValue.symm
  have size : BitVec.ofNat 64 s.extra + 4#64 = BitVec.ofNat 64 (s.extra + 4) := grab_size_word s.extra
  have reserved : BitVec.ofNat 64 (a + 8 * (s.extra + 4)) +
      (sign_extend (m := 64) (0xff8#12) - Sail.shift_bits_left (BitVec.ofNat 64 (s.extra + 4))
        (Sail.BitVec.extractLsb (0x03#6) 5 0)) = BitVec.ofNat 64 (a - 8) := by
    simpa only [BitVec.zero_add] using grab_reservation_word a (s.extra + 4) space.room
  simp only [size, BitVec.zero_add, reserved] at reserve
  obtain ⟨nb, after, _, steps, post⟩ := reserve space.youngWrite.lower space.youngWrite.upper
    space.youngWrite.htif space.youngWrite.aligned
    (image_entry_code space.image (List.mem_cons_self :
      (domain + Layout.off_young_ptr, 8, BitVec.ofNat 64 (a - 8)) ∈ grabReserveLog domain a) (by decide) (by decide)) nextMemory written capacity d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have fullMemory : after.σ.mem = writeLog c.σ.mem (grabReserveLog domain a) := by
    rw [memory, written, dp.memory]; rfl
  have bytes : gpr after 16 = some (BitVec.ofNat 64 (8 * (s.extra + 4))) := by
    have raw : gpr after 16 = some (Sail.shift_bits_left (BitVec.ofNat 64 (s.extra + 4))
      (Sail.BitVec.extractLsb (0x03#6) 5 0)) := PinsHold.get post.pins ⟨3, by simp⟩
    change gpr after 16 = some (BitVec.ofNat 64 (s.extra + 4) <<< (3 : Nat)) at raw
    simpa only [nat_shift_word] using raw
  exact ⟨nb, after, steps, post.good, post.tick, image_of_writeLog h.dispatch.image space.image fullMemory,
    post.pcAt, PinsHold.get post.pins ⟨4, by simp⟩, PinsHold.get post.pins ⟨2, by simp⟩, bytes,
    PinsHold.get post.pins ⟨0, by simp⟩, fullMemory,
    (dp.frame.trans rawFrame).widenChecked (allowed := grabReserveWrites) (by decide)⟩

end OCaml.Vm.Sim
