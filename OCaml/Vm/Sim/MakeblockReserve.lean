import OCaml.Vm.Sim.MakeblockReserved
import OCaml.Vm.Sim.MakeblockReserveSegment
import OCaml.Vm.Sim.MakeblockReservePins
import OCaml.Vm.Sim.MakeblockReserveLayout
import OCaml.Vm.Sim.Immediate

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The actual generic MAKEBLOCK nursery prefix decodes its size and tag,
checks the G1 capacity, and writes the reserved young pointer. -/
theorem makeblock_reserve {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit : Nat} {size tag : BitVec 32} {accu : BitVec 64}
    (h : ArmInput L P s .MAKEBLOCK c pl cp sp high)
    (sizeOperand : OperandAt P pl (s.pc + 1) size)
    (tagOperand : OperandAt P pl (s.pc + 2) tag)
    (nonnegative : 0 ≤ size.toInt) (nursery : size.toInt.toNat ≤ 256)
    (space : MakeblockInput P s c pl cp sp high size.toInt.toNat tag.toInt.toNat a domain limit accu)
    (dp : DispatchPost c .MAKEBLOCK (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ nb after, StepsN nb d after ∧ MakeblockReserved c pl s.pc size.toInt.toNat a domain tag after := by
  have sizeWord := nonnegative_word32 size nonnegative
  have reserveImage : ImageOutside (grabReserveLog domain a) :=
    imageOutside_sublist (List.sublist_append_left _ _) space.image
  have sizeGuard : zopz0zKzJ_u (256#64) (BitVec.ofNat 64 size.toInt.toNat) = true := by
    apply bgeu_of_le
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show size.toInt.toNat < 2^64 by omega)]
    omega
  have domainRead : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have youngRead := space.youngWrite.read
  have youngAddress : BitVec.ofNat 64 domain + 8#64 =
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
  have capacity : zopz0zKzJ_u (BitVec.ofNat 64 (a - 8)) (BitVec.ofNat 64 limit) = true := by
    apply bgeu_of_le
    rw [headerNat, limitNat]
    exact space.capacity
  have bp : SegSt (0x8000263c#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩]
      (fun σ => Vsa.Sim.Code.CamlMakeblockReserveLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc, trivial⟩,
      dp.good.minstret, dp.tick, makeblock_reserve_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  obtain ⟨nextMemory, written⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (domain + Layout.off_young_ptr) (sdData_val (BitVec.ofNat 64 (a - 8))) := ⟨_, rfl⟩
  have run := tr_makeblock_reserve (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d.σ.mem d.σ
  have pc2 := codePc_add pl s.pc 2
  have pc3 := codePc_add pl s.pc 3
  simp only [makeblock_reserve_domain, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) (0x00c#12) = 12#64 from by decide,
    show sign_extend (m := 64) (0x100#12) = 256#64 from by decide,
    BitVec.zero_add, codePc_succ, pc2, pc3,
    sizeOperand.geometry.toNat, tagOperand.geometry.toNat, domainRead.toNat] at run
  have first := run sizeOperand.geometry.lower sizeOperand.geometry.upper sizeOperand.geometry.htif
    (BitVec.ofNat 64 size.toInt.toNat) (by rw [sizeOperand.read32 h.code dp.memory, sizeWord])
    tagOperand.geometry.lower tagOperand.geometry.upper tagOperand.geometry.htif
    (sign_extend (m := 64) tag) (by rw [tagOperand.read32 h.code dp.memory])
    sizeGuard domainRead.lower domainRead.upper domainRead.htif (BitVec.ofNat 64 domain) domainValue.symm
  simp only [youngAddress, youngRead.toNat, domainNat] at first
  have reserve := first youngRead.lower youngRead.upper youngRead.htif
    (BitVec.ofNat 64 (a + 8 * (size.toInt.toNat))) youngValue.symm
    limitRead.lower limitRead.upper limitRead.htif (BitVec.ofNat 64 limit) limitValue.symm
  have reserved : BitVec.ofNat 64 (a + 8 * (size.toInt.toNat)) +
      (sign_extend (m := 64) (0xff8#12) - Sail.shift_bits_left (BitVec.ofNat 64 (size.toInt.toNat))
        (Sail.BitVec.extractLsb (0x03#6) 5 0)) = BitVec.ofNat 64 (a - 8) := by
    simpa only [BitVec.zero_add] using grab_reservation_word a (size.toInt.toNat) space.room
  simp only [reserved] at reserve
  obtain ⟨nb, after, _, steps, post⟩ := reserve space.youngWrite.lower space.youngWrite.upper
    space.youngWrite.htif space.youngWrite.aligned
    (image_entry_code reserveImage (List.mem_cons_self :
      (domain + Layout.off_young_ptr, 8, BitVec.ofNat 64 (a - 8)) ∈ grabReserveLog domain a) (by decide) (by decide)) nextMemory written capacity d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have fullMemory : after.σ.mem = writeLog c.σ.mem (grabReserveLog domain a) := by
    rw [memory, written, dp.memory]; rfl
  exact ⟨nb, after, steps, post.good, post.tick, image_of_writeLog h.dispatch.image reserveImage fullMemory,
    post.pcAt, PinsHold.get post.pins ⟨8, by simp⟩, PinsHold.get post.pins ⟨6, by simp⟩,
    PinsHold.get post.pins ⟨0, by simp⟩, PinsHold.get post.pins ⟨5, by simp⟩, fullMemory,
    (dp.frame.trans rawFrame).widenChecked (allowed := makeblockReserveWrites) (by decide)⟩

end OCaml.Vm.Sim
