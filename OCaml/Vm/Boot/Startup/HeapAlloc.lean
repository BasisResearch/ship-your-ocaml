import OCaml.Vm.Boot.Startup.HeapAllocSteps
import OCaml.Vm.Boot.Startup.StatAllocReady
import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.RuntimeWindows
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_alloc_for_heap(req) end to end, without huge pages. -/
/-- Where the chunk head lies. -/
theorem chunkHead_nat (mem : BitVec 64) (fits : mem.toNat + 4152 < 2 ^ 64) :
    (chunkHead mem).toNat = (mem.toNat + 56) / 4096 * 4096 + 4040 := by
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold chunkHead pageNumber
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  rw [p64] at fits
  generalize mem.toNat = m at *
  rw [Nat.mod_eq_of_lt (a := m + 56) (by omega)]
  omega

/-- The head and the chunk lie inside the raw block of `asize + 4152` bytes. -/
theorem chunk_inside (mem : BitVec 64) (asize : Nat) (fits : mem.toNat + asize + 4152 < 2 ^ 64) :
    mem.toNat < (chunkHead mem).toNat ∧ (chunkHead mem).toNat + 56 + asize ≤ mem.toNat + (asize + 4152) ∧
      ((chunkHead mem).toNat + 56) % 4096 = 0 := by
  rw [chunkHead_nat mem (by omega)]
  omega

/-- A chunk head inside a raw block of the arena. -/
structure ChunkSpot (mem : BitVec 64) (asize : Nat) : Prop where
  low : heapStart ≤ mem.toNat
  high : mem.toNat + (asize + 4152) ≤ heapEnd

theorem ChunkSpot.head_nat {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) :
    (chunkHead mem).toNat = (mem.toNat + 56) / 4096 * 4096 + 4040 := by
  have := S.high
  unfold heapEnd at this
  exact chunkHead_nat mem (by omega)

theorem ChunkSpot.field_nat {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (off : Nat) (h : off ≤ 56) :
    (chunkHead mem + BitVec.ofNat 64 off).toNat = (chunkHead mem).toNat + off := by
  have high := S.high
  have head := S.head_nat
  unfold heapEnd at high
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, head, Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ChunkSpot.bounds {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) :
    mem.toNat < (chunkHead mem).toNat ∧ (chunkHead mem).toNat + 56 + asize ≤ mem.toNat + (asize + 4152) ∧
      (chunkHead mem).toNat % 8 = 0 := by
  have head := S.head_nat
  rw [head]
  omega

theorem chunk_window_nat {h m a off : Nat} (low : 0x8007d140 ≤ m) (lt : m < h) (fits : h + 56 + a ≤ m + (a + 4152))
    (high : m + (a + 4152) ≤ 0x86800000) (hal : h % 8 = 0) (bound : off + 8 ≤ 56) (oal : off % 8 = 0) :
    0x80000000 ≤ h + off ∧ h + off + 8 ≤ 0x100000000 ∧ 0x80061fc0 + 16 ≤ h + off ∧ (h + off) % 8 = 0 := by
  omega

theorem ChunkSpot.window {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (off : Nat) (h : off + 8 ≤ 56)
    (aligned : off % 8 = 0) : WriteWindow (chunkHead mem + BitVec.ofNat 64 off) 8 := by
  obtain ⟨lt, fits, hal⟩ := S.bounds
  obtain ⟨lower, upper, htif, al⟩ := chunk_window_nat (h := (chunkHead mem).toNat) (m := mem.toNat) (a := asize)
    S.low lt fits S.high hal h aligned
  rw [← S.field_nat off (by omega)] at lower upper htif al
  exact ⟨lower, upper, htif, al⟩

theorem ChunkSpot.log_in {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (a : BitVec 64) :
    LogInW [⟨mem.toNat, mem.toNat + (asize + 4152)⟩] (chunkHeadLog mem a) := by
  have b := S.bounds
  simp only [chunkHeadLog, LogInW, InsideW, S.field_nat 32 (by decide), S.field_nat 40 (by decide),
    S.field_nat 48 (by decide), S.field_nat 16 (by decide), or_false, and_true]
  omega

theorem ChunkSpot.outside {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (a : BitVec 64) :
    ImageOutside (chunkHeadLog mem a) := by
  have b := S.bounds
  have low := S.low
  unfold heapStart at low
  constructor <;> simp only [chunkHeadLog, OutLRange, S.field_nat 32 (by decide), S.field_nat 40 (by decide),
    S.field_nat 48 (by decide), S.field_nat 16 (by decide), and_true] <;>
    simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega

theorem ChunkSpot.log_out {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (a : BitVec 64) {x n : Nat}
    (apart : x + n ≤ (chunkHead mem).toNat ∨ (chunkHead mem).toNat + 56 ≤ x) : OutLRange (chunkHeadLog mem a) x n := by
  simp only [chunkHeadLog, OutLRange, S.field_nat 32 (by decide), S.field_nat 40 (by decide),
    S.field_nat 48 (by decide), S.field_nat 16 (by decide), and_true]
  omega

theorem ChunkSpot.above {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) {x : Nat} (high : heapEnd ≤ x) :
    (chunkHead mem).toNat + 56 ≤ x := by
  have b := S.bounds
  have h := S.high
  omega

theorem NativeFrame.alloc_high {sp : BitVec 64} (frame : NativeFrame sp (32 + allocHeadroom)) {x : Nat}
    (hx : nativeFrameBase sp 32 ≤ x) : heapEnd ≤ x :=
  Nat.le_trans (Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (Nat.le_add_right 32 allocHeadroom) _)
    frame.lower)) hx

theorem NativeFrame.alloc_below {sp : BitVec 64} (frame : NativeFrame sp (32 + allocHeadroom)) {x : Nat}
    (low : x < sp.toNat - (32 + allocHeadroom)) : x < (nativeStack sp 32).toNat - allocHeadroom := by
  have f32 : NativeFrame sp 32 := frame.resize (Nat.le_add_right 32 allocHeadroom) (by decide)
  rw [f32.stack_nat]
  unfold nativeFrameBase
  rw [Nat.sub_sub]
  exact low

/-- The chunk head's fields. -/
structure ChunkHeadAt (m : Std.ExtHashMap Nat (BitVec 8)) (mem asize : BitVec 64) : Prop where
  block : bytesT m (chunkHead mem).toNat 8 = mem
  size : bytesT m (chunkHead mem + 16#64).toNat 8 = asize
  stop : bytesT m (chunkHead mem + 32#64).toNat 8 = chunkStart mem + asize
  redarkenEnd : bytesT m (chunkHead mem + 40#64).toNat 8 = chunkStart mem + asize
  redarkenFirst : bytesT m (chunkHead mem + 48#64).toNat 8 = chunkStart mem

theorem ChunkSpot.read {mem : BitVec 64} {asize : Nat} (S : ChunkSpot mem asize) (a : BitVec 64)
    (m : Std.ExtHashMap Nat (BitVec 8)) : ChunkHeadAt (writeLog m (chunkHeadLog mem a)) mem a := by
  have b := S.bounds
  have f (off : Nat) (h : off ≤ 56) := S.field_nat off h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact word_writeLog_at _ _ 4 _ _ rfl trivial
  · exact word_writeLog_at _ _ 3 _ _ rfl (by simp only [chunkHeadLog, List.drop, OutLRange, f 16 (by decide), and_true]; omega)
  · exact word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [chunkHeadLog, List.drop, OutLRange, f 16 (by decide), f 32 (by decide), f 40 (by decide),
        f 48 (by decide), and_true]; omega)
  · exact word_writeLog_at _ _ 1 _ _ rfl (by
      simp only [chunkHeadLog, List.drop, OutLRange, f 16 (by decide), f 40 (by decide), f 48 (by decide), and_true]
      omega)
  · exact word_writeLog_at _ _ 2 _ _ rfl (by
      simp only [chunkHeadLog, List.drop, OutLRange, f 16 (by decide), f 48 (by decide), and_true]; omega)

/-- caml_alloc_for_heap(req) is called; huge pages are off. -/
structure HeapAllocCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra req : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x8000ac40#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, req)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (32 + allocHeadroom)
  huge : bytesT c.σ.mem 0x80064b08 8 = 0#64
  charged : vsaChg (heapChunkSize req + 4152#64).toNat charge
  /-- The chunk is smaller than 4 GiB. -/
  small : (heapChunkSize req).toNat + 4152 < 2 ^ 32

/-- The raw block `mem` holds the chunk and its head. -/
structure HeapAllocDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra req mem : BitVec 64) (before after : Config) :
    Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (1, ra), (10, chunkStart mem)]
  ready : RuntimeReady ((mem.toNat, (heapChunkSize req + 4152#64).toNat) :: H) capacity sp ra after
  fresh : FreshBlock vsaLayoutP H mem.toNat (heapChunkSize req + 4152#64).toNat
  head : ChunkHeadAt after.σ.mem mem (heapChunkSize req)
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k
  kept : ∀ x, x < sp.toNat - (32 + allocHeadroom) → ¬ vsaFoot H x →
    (x < (chunkHead mem).toNat ∨ (chunkHead mem).toNat + 56 ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  caller : ∀ x, sp.toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem alloc_for_heap (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra req : BitVec 64)
    (A : HeapAllocCall H capacity charge sp ra req c) :
    ∃ mem after, Steps c after ∧ HeapAllocDone H capacity sp ra req mem c after := by
  have frame32 : NativeFrame sp 32 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameA : NativeFrame (nativeStack sp 32) allocHeadroom := A.frame.nested (front := 32) (by decide)
  have regs := A.regs
  obtain ⟨d1, run1, p1⟩ := (heap_alloc_test c ra req A.ready.toLeafInput ⟨gholds_lookup (n := 10) _ regs rfl, trivial⟩
    A.huge).run c ⟨A.pc, rfl⟩
  have k1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15]) : gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready1 := A.ready.window_log (windows := []) p1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((k1 2 (by decide) (by decide) (by decide)).trans A.ready.stack)
    ((k1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg) A.ready.aligned trivial (fun _ _ => trivial)
    trivial trivial (fun _ _ => trivial)
  obtain ⟨d2, run2, p2⟩ := (heap_alloc_size d1 ra req ready1.toLeafInput
    ⟨gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have k2 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15, 14, 10]) : gprGet d2.σ r = gprGet d1.σ r :=
    p2.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready2 := ready1.window_log (windows := []) p2 (by decide) (by simp only [keysG]; decide) (by decide)
    ((k2 2 (by decide) (by decide) (by decide)).trans ready1.stack)
    ((k2 1 (by decide) (by decide) (by decide)).trans ready1.raReg) ready1.aligned trivial (fun _ _ => trivial)
    trivial trivial (fun _ _ => trivial)
  obtain ⟨d3, run3, p3⟩ := (heap_alloc_frame d2 sp ra 4152#64 ready2.toLeafInput
    ⟨(k2 2 (by decide) (by decide) (by decide)).trans ((k1 2 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 2) _ regs rfl)), gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩).run d2 ⟨p2.pc, rfl⟩
  have k3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [2]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready3 : RuntimeReady H (capacity + charge) (nativeStack sp 32) ra d3 :=
    ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p3.regs rfl)
      ((k3 1 (by decide) (by decide) (by decide)).trans ready2.raReg) ready2.aligned frame32 (by simp only [LogInW])
  -- caml_stat_alloc_noexc(asize + 4152), keeping asize at 8(sp)
  obtain ⟨d4, run4, p4⟩ := (heap_alloc_call d3 sp ra (heapChunkSize req) ready3.toLeafInput frame32
    ⟨(k3 14 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 14) _ p2.regs rfl),
      gholds_lookup (n := 10) _ p3.regs rfl, ready3.raReg, gholds_lookup (n := 2) _ p3.regs rfl, trivial⟩).run d3
    ⟨p3.pc, rfl⟩
  have k4 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [10] ++ [1]) : gprGet d4.σ r = gprGet d3.σ r :=
    p4.toEffectPost.gpr_frame (by decide) r lo hi out
  have inside4 : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 (heapAllocSlots ra (heapChunkSize req))) :=
    frame32.word_log_inside fun off value member => by simp [heapAllocSlots] at member; omega
  have ready4 : RuntimeReady H (capacity + charge) (nativeStack sp 32) jal_8000ac78_call.link d4 :=
    ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k4 2 (by decide) (by decide) (by decide)).trans ready3.stack) (gholds_lookup (n := 1) _ p4.regs rfl)
      (by decide) frame32 inside4
  have slot4 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ heapAllocSlots ra (heapChunkSize req)) :
      bytesT d4.σ.mem (nativeFrameBase sp 32 + off) 8 = value := by
    rw [p4.memory]
    exact frame32.word_log_read (by intro o w h; simp [heapAllocSlots] at h; omega) (by simp [heapAllocSlots]) _ member
  obtain ⟨d5, run5, ⟨B⟩⟩ := (stat_alloc_ready d4 H capacity charge (heapChunkSize req + 4152#64) _ _ ready4 frameA
    (gholds_lookup (n := 10) _ p4.regs rfl) A.charged).run d4 ⟨p4.pc, rfl⟩
  have fresh : FreshBlock vsaLayoutP H (vsaReg d5 10).toNat (heapChunkSize req + 4152#64).toNat :=
    B.allocation.result.fresh
  have memReg : gprGet d5.σ 10 = some (vsaReg d5 10) := library_gpr B.ready.platform (by decide) (by decide) rfl
  have pc5 : PCAt jal_8000ac78_call.link d5 := library_pc B.allocation.good B.allocation.result.frame.pc
  have keep5 (a : Nat) (above : (nativeStack sp 32).toNat ≤ a) :
      (d5.σ.mem[a]?).getD 0 = (d4.σ.mem[a]?).getD 0 := B.caller_byte frameA above
  have saved5 (k : Nat) (member : k ∈ abiSaved) : gprGet d5.σ k = gprGet d4.σ k := B.saved_gpr member
  have ready5 := B.ready
  generalize hmem : vsaReg d5 10 = mem at fresh memReg ready5
  have nonzero : mem ≠ 0#64 := fun h => fresh.1 (by rw [h]; rfl)
  have sizeNat : (heapChunkSize req + 4152#64).toNat = (heapChunkSize req).toNat + 4152 := by
    rw [BitVec.toNat_add]; have := A.small; simp only [BitVec.toNat_ofNat]; omega
  have spot : ChunkSpot mem (heapChunkSize req).toNat :=
    ⟨fresh.2.1, by have := fresh.2.2.1; rw [sizeNat] at this; exact this⟩
  have stackNat : (nativeStack sp 32).toNat = sp.toNat - 32 := frame32.stack_nat
  have base32 : nativeFrameBase sp 32 = sp.toNat - 32 := rfl
  -- the chunk head
  obtain ⟨d6, run6, p6⟩ := (heap_alloc_head d5 sp jal_8000ac78_call.link mem (heapChunkSize req) ready5.toLeafInput
    frame32 ⟨memReg, ready5.stack, trivial⟩ nonzero
    (by rw [word_observed (m := d4.σ.mem) _ fun i hi => keep5 _ (by rw [stackNat, base32]; omega)]
        exact slot4 8 _ (by simp [heapAllocSlots]))
    (fun off h al => spot.window off h al) (spot.outside _)).run d5 ⟨pc5, rfl⟩
  have k6 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [13, 15, 14, 10, 12]) : gprGet d6.σ r = gprGet d5.σ r :=
    p6.toEffectPost.gpr_frame (by decide) r lo hi out
  have blockOwned : (mem.toNat, (heapChunkSize req).toNat + 4152) ∈
      (mem.toNat, (heapChunkSize req + 4152#64).toNat) :: H := by rw [sizeNat]; exact List.mem_cons_self ..
  have ready6 := ready5.window_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
    ((k6 2 (by decide) (by decide) (by decide)).trans ready5.stack)
    ((k6 1 (by decide) (by decide) (by decide)).trans ready5.raReg) ready5.aligned (spot.log_in _)
    (fun pin member => arenaWindow_out_pins spot.low pin member)
    (by simp only [OutWRange, and_true]; exact Or.inl (Nat.le_trans (by decide) spot.low))
    (by simp only [OutWRange, and_true]; exact Or.inl (Nat.le_trans (by decide) spot.low))
    (fun a foot => by
      simp only [OutW, and_true]
      exact block_foot_out spot.low blockOwned foot)
  have spLow := A.frame.lower
  have high32 (x : Nat) (hx : nativeFrameBase sp 32 ≤ x) : heapEnd ≤ x := A.frame.alloc_high hx
  -- restore ra and return
  obtain ⟨d7, run7, p7⟩ := (heap_alloc_return d6 sp ra (chunkStart mem) jal_8000ac78_call.link ready6.toLeafInput frame32
    ⟨(k6 2 (by decide) (by decide) (by decide)).trans ready5.stack, gholds_lookup (n := 10) _ p6.regs rfl, trivial⟩
    (by
      rw [p6.memory, bytesT_writeLog_out _ (spot.log_out _ (Or.inr (spot.above (high32 _ (Nat.le_add_right _ _))))),
        word_observed (m := d4.σ.mem) _ fun i hi => keep5 _ (by rw [stackNat, base32]; omega)]
      exact slot4 24 _ (by simp [heapAllocSlots]))
    A.ready.aligned).run d6 ⟨p6.pc, rfl⟩
  have k7 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [1, 2]) : gprGet d7.σ r = gprGet d6.σ r :=
    p7.toEffectPost.gpr_frame (by decide) r lo hi out
  have mem7 : d7.σ.mem = writeLog d5.σ.mem (chunkHeadLog mem (heapChunkSize req)) := by
    rw [p7.memory, show writeLog d6.σ.mem [] = d6.σ.mem from rfl, p6.memory]
  have low3 (x : Nat) : (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p3.memory, p2.memory, p1.memory]; rfl
  refine ⟨mem, d7, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), {
    pc := p7.pc
    regs := p7.regs
    ready := ready6.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p7.regs rfl) (gholds_lookup (n := 1) _ p7.regs rfl) A.ready.aligned frame32
      (by simp only [LogInW])
    fresh := fresh
    head := by rw [mem7]; exact spot.read _ _
    saved := fun k member => by
      have range : 1 ≤ k ∧ k ≤ 31 := by simp [abiSaved] at member; omega
      have out (L : List Nat) (low : ∀ m ∈ L, m ∉ abiSaved) : k ∉ L := fun mem => low k mem member
      rw [k7 k range.1 range.2 (out _ (by decide)), k6 k range.1 range.2 (out _ (by decide)), saved5 k member,
        k4 k range.1 range.2 (out _ (by decide)), k3 k range.1 range.2 (out _ (by decide)),
        k2 k range.1 range.2 (out _ (by decide)), k1 k range.1 range.2 (out _ (by decide))]
    kept := fun x low foot apart => by
      have below := A.frame.alloc_below low
      rw [mem7, writeLog_out _ _ _ (outL_of_range (spot.log_out _ (n := 1) (by omega)) (Nat.le_refl _)
          (Nat.lt_succ_self _)),
        B.kept_byte below foot, p4.memory,
        frameOn_writeLog _ _ _ inside4 x ⟨Or.inl (show x < nativeFrameBase sp 32 by
          rw [stackNat] at below; rw [base32]; omega), trivial⟩,
        low3]
    caller := fun x above => by
      rw [mem7, writeLog_out _ _ _ (outL_of_range (spot.log_out _ (n := 1)
          (Or.inr (spot.above (high32 _ (by rw [base32]; omega))))) (Nat.le_refl _) (Nat.lt_succ_self _)),
        keep5 _ (by rw [stackNat]; omega), p4.memory, frameOn_writeLog _ _ _ inside4 x ⟨Or.inr above, trivial⟩, low3] }⟩
end OCaml.Vm.Boot.Startup
