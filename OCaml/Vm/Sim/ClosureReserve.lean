import OCaml.Vm.Sim.ClosureNurseryInput
import OCaml.Vm.Sim.ClosureReserveSegment
import OCaml.Vm.Sim.ClosureReservePins
import OCaml.Vm.Sim.ClosureReserveLayout

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The native closure reservation consumes the transported nursery observations
and reserves its metadata and captures without entering the GC slow path. -/
theorem closure_reserve {pl : Place} {pc sp count a domain limit : Nat} {accu : BitVec 64} {c d : Config}
    (space : ClosureNurseryInput sp count a domain limit accu c)
    (front : ClosurePrefixed c pl pc sp count accu d) :
    ∃ nb after, StepsN nb d after ∧ ClosureReserved c pl pc sp count a domain accu after := by
  have nursery := space.after front
  have small := front.fields.nurseryBound
  have domainRead : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have youngRead := nursery.youngWrite.read
  have limitRead : RamReadAt domain 8 := by simpa only [Layout.off_young_limit, Nat.add_zero] using nursery.limitRead
  have youngAddress : BitVec.ofNat 64 domain + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (domain + Layout.off_young_ptr) := by rw [BitVec.ofNat_add]; rfl
  have readWord (address : Nat) : sign_extend (m := 64) (bytesT8 d.σ.mem address) = word d address := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have domainValue := (readWord Layout.sym_Caml_state).trans nursery.domainValue
  have youngValue := (readWord (domain + Layout.off_young_ptr)).trans nursery.youngValue
  have limitValue : sign_extend (m := 64) (bytesT8 d.σ.mem domain) = BitVec.ofNat 64 limit := by
    simpa only [Layout.off_young_limit, Nat.add_zero] using (readWord (domain + Layout.off_young_limit)).trans nursery.limitValue
  have limitNat : (BitVec.ofNat 64 limit).toNat = limit :=
    Nat.mod_eq_of_lt (by have upper := nursery.headerWrite.upper; have capacity := nursery.capacity; omega)
  have guard : zopz0zI_u (BitVec.ofNat 64 (a - 8)) (BitVec.ofNat 64 limit) = false := by
    apply bltu_false_of_ge
    rw [nursery.headerWrite.read.toNat, limitNat]
    exact nursery.capacity
  have sizeWord := addiw_nat_add count 3 (offset := 0x003#12) (by decide) (by omega)
  have address := nursery_sub_reservation a (count + 2) nursery.room (by omega)
  have bp : SegSt (0x800029e8#64) [⟨Register.x17, BitVec.ofNat 64 count⟩]
      (fun σ => Vsa.Sim.Code.CamlClosureReserveLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨front.good, front.pcAt, ⟨front.fields.countReg, trivial⟩,
      front.good.minstret, front.tick, closure_reserve_loaded front.image, rfl, rfl⟩
  obtain ⟨nextMemory, written⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (domain + Layout.off_young_ptr) (sdData_val (BitVec.ofNat 64 (a - 8))) := ⟨_, rfl⟩
  have run := tr_closure_reserve (BitVec.ofNat 64 count) d.σ.mem d.σ
  simp only [closure_reserve_domain, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, domainRead.toNat, sizeWord] at run
  have first := run domainRead.lower domainRead.upper domainRead.htif (BitVec.ofNat 64 domain) domainValue.symm
  simp only [youngAddress, youngRead.toNat, limitRead.toNat] at first
  have second := first youngRead.lower youngRead.upper youngRead.htif (BitVec.ofNat 64 (a + 8 * (count + 2))) youngValue.symm
    limitRead.lower limitRead.upper limitRead.htif (BitVec.ofNat 64 limit) limitValue.symm
  simp only [show count + 3 = count + 2 + 1 by omega, address] at second
  obtain ⟨nb, after, _, steps, post⟩ := second nursery.youngWrite.lower nursery.youngWrite.upper nursery.youngWrite.htif nursery.youngWrite.aligned
    (image_entry_code nursery.image (List.mem_cons_self :
      (domain + Layout.off_young_ptr, 8, BitVec.ofNat 64 (a - 8)) ∈ grabReserveLog domain a) (by decide) (by decide))
    nextMemory written guard d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked (allowed := closureReserveWrites) (by decide)
  have reserveMemory : after.σ.mem = writeLog d.σ.mem (grabReserveLog domain a) := by
    rw [memory, written]; rfl
  have fullMemory : after.σ.mem = writeLog c.σ.mem (closurePushLog sp count accu ++ grabReserveLog domain a) := by
    rw [reserveMemory, front.memory, writeLog_append]
  exact ⟨nb, after, steps, post.good, post.tick, image_of_writeLog front.image nursery.image reserveMemory,
    post.pcAt, front.fields.frame frame (by decide), PinsHold.get post.pins ⟨0, by simp⟩, fullMemory,
    (front.frame.trans frame).widenChecked (allowed := closureReservationWrites) (by decide)⟩

end OCaml.Vm.Sim
