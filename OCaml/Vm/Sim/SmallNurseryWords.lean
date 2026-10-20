import OCaml.Vm.Sim.CopyStringInput
import OCaml.Vm.Gc.G1Guards
import OCaml.Vm.Gc.Readback

/-!
# `caml_alloc_small`'s nursery inputs from the domain words

`SmallAllocation.NurseryMemory` at any call site, from three scalar facts:
the `Caml_state` word names a domain record `D` above `.bss`, whose
`young_ptr` and `young_limit` words read `Y` and `Lm`, with room for the
block's header and fields between them, and the block apart from the record.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- `caml_alloc_small`'s two stores: `young_ptr` and the block's header. -/
theorem SmallAllocation.constructorLog_words {ra size tag : BitVec 64} {D Y : Nat} (hD : D + 8 < 2 ^ 64)
    (hY : Y < 2 ^ 64) (small : size.toNat < 2 ^ 32) (fits : 8 + 8 * size.toNat ≤ Y) :
    SmallAllocation.constructorLog ra size tag (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y) =
      [(D + 8, 8, BitVec.ofNat 64 (Y - 8 - 8 * size.toNat)),
       (Y - 8 - 8 * size.toNat, 8, (size <<< 10) + SmallAllocation.tagWord tag)] := by
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have shifted : (size <<< 3).toNat = 8 * size.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hdr : SmallAllocation.nurseryHeader (BitVec.ofNat 64 Y) size = BitVec.ofNat 64 (Y - 8 - 8 * size.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [SmallAllocation.nurseryHeader, BitVec.toNat_sub, shifted, nat _ hY, BitVec.toNat_ofNat]
    omega
  have ys : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + 8 := by
    simp only [DoubleAllocation.youngSlot, Layout.off_young_ptr, ← BitVec.ofNat_add]; exact nat _ hD
  simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog, SmallAllocation.initializationLog,
    SmallAllocation.reservedRegisters, ys, List.cons_append, List.nil_append]
  rw [show BitVec.ofNat 64 Y - 8#64 - size <<< 3 = SmallAllocation.nurseryHeader (BitVec.ofNat 64 Y) size from rfl,
    hdr, nat _ (by omega)]

/-- **`caml_alloc_small(size, tag)`'s nursery inputs** at a config whose
domain words read `D`, `Y` and `Lm`. -/
theorem SmallAllocation.NurseryMemory.of_words {ra size tag : BitVec 64} {c : Config} {D Y Lm : Nat}
    (domain : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (young : word c (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y)
    (limit : word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm)
    (domainLow : Layout.sym_bss_end ≤ D) (domainHigh : D + Layout.domainStateBytes ≤ 2 ^ 32)
    (domainAligned : D % 8 = 0) (small : size.toNat < 2 ^ 32)
    (room : Lm + 8 * size.toNat + 8 ≤ Y) (limitLow : Layout.sym_bss_end ≤ Lm) (youngHigh : Y ≤ 2 ^ 32)
    (youngAligned : Y % 8 = 0)
    (apart : D + Layout.domainStateBytes + 8 * size.toNat + 8 ≤ Y ∨ Y ≤ D) :
    SmallAllocation.NurseryMemory ra size tag (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm) c := by
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have cs : Layout.sym_Caml_state = 0x80064d08 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have shifted : (size <<< 3).toNat = 8 * size.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hdr : SmallAllocation.nurseryHeader (BitVec.ofNat 64 Y) size = BitVec.ofNat 64 (Y - 8 - 8 * size.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [SmallAllocation.nurseryHeader, BitVec.toNat_sub, shifted, nat _ (by omega : Y < 2 ^ 64),
      BitVec.toNat_ofNat]
    omega
  have ys : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + 8 := by
    simp only [DoubleAllocation.youngSlot, Layout.off_young_ptr, ← BitVec.ofNat_add]; exact nat _ (by omega)
  have ls : (DoubleAllocation.limitSlot (BitVec.ofNat 64 D)).toNat = D := by
    simp only [DoubleAllocation.limitSlot, Layout.off_young_limit, ← BitVec.ofNat_add, Nat.add_zero]
    exact nat _ (by omega)
  have gd : DoubleAllocation.domainGlobal.toNat = Layout.sym_Caml_state := rfl
  have hlog := SmallAllocation.constructorLog_words (ra := ra) (tag := tag) (size := size) (D := D) (Y := Y)
    (by omega) (by omega) small (by omega)
  have hy : Y - 8 - 8 * size.toNat + 8 ≤ Y := by omega
  refine { domainValue := ?_, youngValue := ?_, limitValue := ?_, youngWrite := ?_, limitRead := ?_,
           headerWrite := ?_, room := ?_, reserveImage := ?_, initializeImage := ?_, domainAfterHeader := ?_,
           youngAfterHeader := ?_ }
  · rw [gd]; exact domain
  · rw [ys]; exact young
  · rw [ls]; simpa only [Layout.off_young_limit, Nat.add_zero] using limit
  · rw [show DoubleAllocation.youngSlot (BitVec.ofNat 64 D) = BitVec.ofNat 64 (D + 8) from
      BitVec.eq_of_toNat_eq (by rw [ys, nat _ (by omega)])]
    exact window_of_nat (by rw [tohost]; rw [bss] at domainLow; omega) (by simp only [Layout.domainStateBytes] at domainHigh; omega) (by omega)
  · rw [show DoubleAllocation.limitSlot (BitVec.ofNat 64 D) = BitVec.ofNat 64 D from
      BitVec.eq_of_toNat_eq (by rw [ls, nat _ (by omega)])]
    exact (window_of_nat (by rw [tohost]; rw [bss] at domainLow; omega) (by simp only [Layout.domainStateBytes] at domainHigh; omega) domainAligned).read
  · rw [hdr]
    exact window_of_nat (by rw [tohost]; rw [bss] at limitLow; omega) (by omega) (by omega)
  · rw [SmallAllocation.nurseryHeader, BitVec.sub_sub]
    apply Gc.bltu_room
    simp only [BitVec.toNat_add, shifted, nat _ (by omega : Y < 2 ^ 64), nat _ (by omega : Lm < 2 ^ 64),
      BitVec.toNat_ofNat]
    omega
  · apply imageOutside_of_above
    intro e he
    simp only [StringAllocation.reservationLog, List.mem_singleton] at he
    subst he; rw [ys]; omega
  · apply imageOutside_of_above
    intro e he
    simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, List.mem_singleton] at he
    subst he
    show Layout.sym_bss_end ≤ (SmallAllocation.nurseryHeader (BitVec.ofNat 64 Y) size).toNat
    rw [hdr, nat _ (by omega)]; omega
  · rw [hlog, gd, bytesT_writeLog_out]
    · exact domain
    · simp only [OutLRange, and_true]; rw [cs]; rw [bss] at domainLow limitLow; omega
  · rw [hlog, ys, hdr]
    exact Gc.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [List.drop, OutLRange, and_true]
      simp only [Layout.domainStateBytes] at apart; omega)

end OCaml.Vm.Sim
