import OCaml.Vm.Boot.Startup.MakeFreeSteps
import OCaml.Vm.Boot.Startup.ClearReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! bf_make_free_blocks(chunk, size, 1, Caml_white) end to end: one blue free
block of the whole chunk becomes the best-fit tree's root. -/

/-- A window inside a live block of the arena. -/
theorem ownedWindow_ok {H : List (Nat × Nat)} {q n lo hi : Nat} (low : heapStart ≤ q) (owned : (q, n) ∈ H)
    (start : q ≤ lo) (stop : hi ≤ q + n) : WindowsOk H [⟨lo, hi⟩] := by
  refine ⟨fun pin member => ?_, ?_, ?_, fun a foot => ?_⟩
  · have := arenaWindow_out_pins (n := hi - lo) (p := lo) (by omega) pin member
    simp only [OutW, and_true] at this ⊢
    omega
  · simp only [OutWRange, and_true]
    exact Or.inl (Nat.le_trans (by decide) (Nat.le_trans low start))
  · simp only [OutWRange, and_true]
    exact Or.inl (Nat.le_trans (by decide) (Nat.le_trans low start))
  · have := block_foot_out low owned foot
    simp only [OutW, and_true]
    omega

theorem window_of_heap {x : BitVec 64} {w : Nat} (lo : heapStart ≤ x.toNat) (hi : x.toNat + w ≤ heapEnd)
    (al : x.toNat % w = 0) : WriteWindow x w := by
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have hT : Layout.sym_tohost = 0x80061fc0 := rfl
  rw [hS] at lo
  rw [hE] at hi
  exact ⟨by omega, by omega, by rw [hT]; omega, al⟩

theorem WindowsOk.cons {H : List (Nat × Nat)} {w : W} {ws : List W} (head : WindowsOk H [w]) (tail : WindowsOk H ws) :
    WindowsOk H (w :: ws) := by
  refine ⟨fun pin m => ?_, ?_, ?_, fun a foot => ?_⟩
  · have h := head.pins pin m; simp only [OutW, and_true] at h; exact ⟨h, tail.pins pin m⟩
  · have h := head.domain; simp only [OutWRange, and_true] at h; exact ⟨h, tail.domain⟩
  · have h := head.pool; simp only [OutWRange, and_true] at h; exact ⟨h, tail.pool⟩
  · have h := head.heap a foot; simp only [OutW, and_true] at h; exact ⟨h, tail.heap a foot⟩

/-- The chunk `[p, p + 8 size)` lies in the live block `(q, n)`; the tree is empty. -/
structure MakeFreeCall (H : List (Nat × Nat)) (capacity : Nat) (sp ra p size s0 s1 s2 s3 s4 s5 s6 s7 s8 cur : BitVec 64)
    (q n : Nat) (c : Config) : Prop where
  pc : PCAt 0x80006fac#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, p), (11, size), (12, 1#64), (13, 0#64), (8, s0), (9, s1), (18, s2),
    (19, s3), (20, s4), (21, s5), (22, s6), (23, s7), (24, s8)]
  ready : RuntimeReady H capacity sp ra c
  frame : NativeFrame sp 80
  fits : size.toNat ≤ 2 ^ 54
  large : 18 ≤ size.toNat
  ownedLow : heapStart ≤ q
  owned : (q, n) ∈ H
  ownedHigh : q + n ≤ heapEnd
  chunkStart : q ≤ p.toNat
  chunkStop : p.toNat + 8 * size.toNat ≤ q + n
  aligned : p.toNat % 8 = 0
  tree : bytesT c.σ.mem largeTreeAddr 8 = 0#64
  least : bytesT c.σ.mem largeLeastAddr 8 = 0#64
  curWsz : bytesT c.σ.mem flCurWszAddr 8 = cur

/-- The best-fit tree's root block `b`: no children, its own sibling ring. -/
structure TreeRoot (m : Std.ExtHashMap Nat (BitVec 8)) (b : BitVec 64) : Prop where
  root : bytesT m largeTreeAddr 8 = b
  left : bytesT m (b + 8#64).toNat 8 = 0#64
  right : bytesT m (b + 16#64).toNat 8 = 0#64
  prev : bytesT m (b + 24#64).toNat 8 = b
  next : bytesT m (b + 32#64).toNat 8 = b

/-- bf_make_free_blocks returned: the chunk is one blue free block, the tree's
root; `caml_fl_cur_wsz` grew by the chunk's size. -/
structure MadeFree (H : List (Nat × Nat)) (capacity : Nat) (sp ra p size s0 s1 s2 s3 s4 s5 s6 s7 s8 cur : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (24, s8), (23, s7), (22, s6), (21, s5), (20, s4), (19, s3), (18, s2), (9, s1),
    (8, s0), (1, ra), (10, p + 8#64)]
  ready : RuntimeReady H capacity sp ra after
  header : bytesT after.σ.mem p.toNat 8 = mfbHeader size
  tree : TreeRoot after.σ.mem (p + 8#64)
  curWsz : bytesT after.σ.mem flCurWszAddr 8 = cur + 1#64 + (size - 1#64)

theorem make_free_blocks (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra p size s0 s1 s2 s3 s4 s5 s6 s7 s8 cur : BitVec 64) (q n : Nat)
    (A : MakeFreeCall H capacity sp ra p size s0 s1 s2 s3 s4 s5 s6 s7 s8 cur q n c) :
    ∃ after, Steps c after ∧ MadeFree H capacity sp ra p size s0 s1 s2 s3 s4 s5 s6 s7 s8 cur c after := by
  have regs := A.regs
  have nonempty : size ≠ 0#64 := fun h => by have := A.large; rw [h] at this; simp at this
  obtain ⟨d1, run1, p1⟩ := (mfb_entry c sp ra p size A.ready.toLeafInput
    ⟨gholds_lookup (n := 11) _ regs rfl, gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 10) _ regs rfl,
      trivial⟩ nonempty).run c ⟨A.pc, rfl⟩
  -- discipline: allow(O8-hand-gpr-frame) landed before GprsSame; migrate when this composition is next touched
  have k1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [2]) : gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready1 : RuntimeReady H capacity (nativeStack sp 80) ra d1 :=
    A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p1.regs rfl)
      ((k1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg) A.ready.aligned A.frame (by simp only [LogInW])
  have r1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [2]) (v : BitVec 64) (h : gprGet c.σ r = some v) :
      gprGet d1.σ r = some v := (k1 r lo hi out).trans h
  obtain ⟨d2, run2, p2⟩ := (mfb_save d1 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 p ready1.toLeafInput A.frame
    ⟨r1 23 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 23) _ regs rfl), gholds_lookup (n := 2) _ p1.regs rfl,
      r1 18 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 18) _ regs rfl),
      r1 19 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 19) _ regs rfl),
      r1 20 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 20) _ regs rfl),
      r1 21 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 21) _ regs rfl),
      r1 22 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 22) _ regs rfl),
      r1 24 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 24) _ regs rfl),
      r1 1 (by decide) (by decide) (by decide) _ A.ready.raReg,
      r1 8 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 8) _ regs rfl),
      r1 9 (by decide) (by decide) (by decide) _ (gholds_lookup (n := 9) _ regs rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have k2 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [23]) : gprGet d2.σ r = gprGet d1.σ r :=
    p2.toEffectPost.gpr_frame (by decide) r lo hi out
  have inside2 : LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (nativeWordLog sp 80 (mfbSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8)) :=
    A.frame.word_log_inside fun off value member => by simp [mfbSlots] at member; omega
  have ready2 : RuntimeReady H capacity (nativeStack sp 80) ra d2 :=
    ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p2.regs rfl)
      (gholds_lookup (n := 1) _ p2.regs rfl) A.ready.aligned A.frame inside2
  obtain ⟨d3, run3, p3⟩ := (mfb_setup d2 ra p size 1#64 0#64 ready2.toLeafInput
    ⟨(k2 11 (by decide) (by decide) (by decide)).trans (r1 11 (by decide) (by decide) (by decide) _
        (gholds_lookup (n := 11) _ regs rfl)), gholds_lookup (n := 10) _ p2.regs rfl,
      (k2 13 (by decide) (by decide) (by decide)).trans (r1 13 (by decide) (by decide) (by decide) _
        (gholds_lookup (n := 13) _ regs rfl)),
      (k2 12 (by decide) (by decide) (by decide)).trans (r1 12 (by decide) (by decide) (by decide) _
        (gholds_lookup (n := 12) _ regs rfl)), gholds_lookup (n := 23) _ p2.regs rfl, trivial⟩).run d2 ⟨p2.pc, rfl⟩
  have k3 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [18, 19, 22, 24, 23, 20, 21]) : gprGet d3.σ r = gprGet d2.σ r :=
    p3.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready3 : RuntimeReady H capacity (nativeStack sp 80) ra d3 :=
    ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k3 2 (by decide) (by decide) (by decide)).trans ready2.stack)
      ((k3 1 (by decide) (by decide) (by decide)).trans ready2.raReg) A.ready.aligned A.frame (by simp only [LogInW])
  -- the header
  have pLow : heapStart ≤ p.toNat := Nat.le_trans A.ownedLow A.chunkStart
  have pHigh : p.toNat + 8 * size.toNat ≤ heapEnd := Nat.le_trans A.chunkStop A.ownedHigh
  have large := A.large
  have pLowN : 0x8007d140 ≤ p.toNat := pLow
  have pHighN : p.toNat + 8 * size.toNat ≤ 0x86800000 := pHigh
  have chunkW := ownedWindow_ok (H := H) A.ownedLow A.owned A.chunkStart A.chunkStop
  have headerOut : ImageOutside [(p.toNat, 8, mfbHeader size)] := by
    have := pLow; unfold heapStart at this
    constructor <;> simp only [OutLRange, and_true] <;> simp only [Image.textBase, Image.textSize, Image.rodataBase,
      Image.rodataSize] <;> omega
  obtain ⟨d4, run4, p4⟩ := (mfb_block d3 ra p size 0#64 1#64 ready3.toLeafInput
    ⟨gholds_lookup (n := 18) _ p3.regs rfl, gholds_lookup (n := 23) _ p3.regs rfl, gholds_lookup (n := 22) _ p3.regs rfl,
      gholds_lookup (n := 24) _ p3.regs rfl, gholds_lookup (n := 19) _ p3.regs rfl, gholds_lookup (n := 20) _ p3.regs rfl,
      gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩ A.fits A.large (by decide)
    (window_of_heap pLow (by omega) A.aligned) headerOut).run d3 ⟨p3.pc, rfl⟩
  have k4 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [9, 15, 14, 13, 22, 8, 10]) : gprGet d4.σ r = gprGet d3.σ r :=
    p4.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready4 : RuntimeReady H capacity (nativeStack sp 80) ra d4 :=
    ready3.window_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k4 2 (by decide) (by decide) (by decide)).trans ready3.stack)
      ((k4 1 (by decide) (by decide) (by decide)).trans ready3.raReg) A.ready.aligned
      (by simp only [LogInW, InsideW, and_true]; omega) chunkW.pins chunkW.domain chunkW.pool chunkW.heap
  -- jal bf_insert_block(p + 8)
  obtain ⟨d5, run5, p5⟩ := (call_registers_summary jal_80007098_call_shape jal_80007098_call_decode d4
    (jal_80007098_call_pins p4.image) p4.good p4.image p4.tick p4.minstret [(10, p + 8#64)]
    ⟨gholds_lookup (n := 10) _ p4.regs rfl, trivial⟩ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (value := p + 8#64) rfl).run d4 ⟨p4.pc, rfl⟩
  have k5 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [1]) : gprGet d5.σ r = gprGet d4.σ r :=
    p5.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready5 : RuntimeReady H capacity (nativeStack sp 80) jal_80007098_call.link d5 :=
    ready4.effect_written p5 (by decide) (fun r w _ _ => by
        simp only [List.mem_singleton] at w; subst w; rw [gholds_lookup (n := 1) _ p5.regs rfl]; rfl) (by decide)
      ((k5 2 (by decide) (by decide) (by decide)).trans ready4.stack) (gholds_lookup (n := 1) _ p5.regs rfl) (by decide)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have mem5 : d5.σ.mem = writeLog d3.σ.mem [(p.toNat, 8, mfbHeader size)] := p5.memory.trans p4.memory
  -- globals below the arena are untouched so far
  have frameHigh : heapEnd ≤ nativeFrameBase sp 80 := by
    have := A.frame.lower; unfold nativeFrameBase; omega
  have frameHighN : 0x86800000 ≤ nativeFrameBase sp 80 := frameHigh
  have lowByte (x : Nat) (hx : x < heapStart) : (d5.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have hx' : x < nativeFrameBase sp 80 := Nat.lt_of_lt_of_le hx (Nat.le_trans (by decide) frameHigh)
    rw [mem5, writeLog_out _ _ _ (by simp only [OutL, and_true]; exact Or.inl (Nat.lt_of_lt_of_le hx pLow)), p3.memory,
      show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory, frameOn_writeLog _ _ _ inside2 x ⟨Or.inl hx', trivial⟩, p1.memory]
    rfl
  have globalWord (a : Nat) (ha : a + 8 ≤ heapStart) : bytesT d5.σ.mem a 8 = bytesT c.σ.mem a 8 :=
    word_observed _ fun i hi => lowByte _ (by omega)
  have treeD5 : bytesT d5.σ.mem largeTreeAddr 8 = 0#64 := by rw [globalWord _ (by decide)]; exact A.tree
  have leastD5 : bytesT d5.σ.mem largeLeastAddr 8 = 0#64 := by rw [globalWord _ (by decide)]; exact A.least
  have back : p + 8#64 - 8#64 = p := BitVec.add_sub_cancel _ _
  obtain ⟨d6, run6, p6⟩ := (bib_find d5 jal_80007098_call.link (p + 8#64) (mfbHeader size) ready5.toLeafInput
    ⟨gholds_lookup (n := 10) _ p5.regs rfl, gholds_lookup (n := 1) _ p5.regs rfl, trivial⟩
    (by rw [back]; have w := window_of_heap (w := 8) pLow (by omega) A.aligned
        exact ⟨w.lower, w.upper, Or.inr (Nat.le_trans (Nat.add_le_add_left (by decide) _) w.htif)⟩)
    (by rw [back, mem5]; exact word_writeLog_at _ _ 0 _ _ rfl trivial) treeD5 leastD5).run d5
    ⟨by rw [← jal_80007098_call_target]; exact p5.pc, rfl⟩
  have k6 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [16, 14, 13, 11, 12]) : gprGet d6.σ r = gprGet d5.σ r :=
    p6.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready6 : RuntimeReady H capacity (nativeStack sp 80) jal_80007098_call.link d6 :=
    ready5.window_log (windows := []) p6 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k6 2 (by decide) (by decide) (by decide)).trans ready5.stack)
      ((k6 1 (by decide) (by decide) (by decide)).trans ready5.raReg) ready5.aligned trivial (fun _ _ => trivial)
      trivial trivial (fun _ _ => trivial)
  -- the root
  have nodeIn : p.toNat + 8 + 40 ≤ p.toNat + 8 * size.toNat := by omega
  have pf (off : Nat) (h : off ≤ 40) : (p + 8#64 + BitVec.ofNat 64 off).toNat = p.toNat + 8 + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    have := pHigh; unfold heapEnd at this; omega
  have pb : (p + 8#64).toNat = p.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; have := pHigh; unfold heapEnd at this; omega
  have treeG := globalWindow_ok (H := H) (lo := largeTreeAddr) (hi := largeTreeAddr + 8) (by decide) (by decide)
    (by decide) (fun a lo hi => by unfold largeTreeAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have rootW := chunkW.cons treeG
  have rootIn : LogInW [⟨p.toNat, p.toNat + 8 * size.toNat⟩, ⟨largeTreeAddr, largeTreeAddr + 8⟩] (rootLog (p + 8#64)) := by
    have a16 := pf 16 (by decide)
    have a8 := pf 8 (by decide)
    have a32 := pf 32 (by decide)
    have a24 := pf 24 (by decide)
    simp only [rootLog, LogInW, InsideW, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl,
      show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl,
      show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, a16, a8, a32, a24, pb, or_false, and_true]
    omega
  have rootOut : ImageOutside (rootLog (p + 8#64)) := by
    have := pLow; unfold heapStart at this
    constructor <;> simp only [rootLog, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl,
      show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl,
      show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide),
      pf 24 (by decide), pb, largeTreeAddr, and_true] <;>
      simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega
  obtain ⟨d7, run7, p7⟩ := (bib_root d6 jal_80007098_call.link (p + 8#64) ready6.toLeafInput
    ⟨gholds_lookup (n := 10) _ p6.regs rfl, gholds_lookup (n := 12) _ p6.regs rfl, gholds_lookup (n := 1) _ p6.regs rfl,
      trivial⟩
    (fun off h al => window_of_heap (by rw [pf off (by omega)]; omega) (by rw [pf off (by omega)]; omega)
      (by rw [pf off (by omega)]; have := A.aligned; omega))
    (window_of_heap (by rw [pb]; omega) (by rw [pb]; omega) (by rw [pb]; have := A.aligned; omega)) rootOut).run d6
    ⟨p6.pc, rfl⟩
  have k7 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15]) : gprGet d7.σ r = gprGet d6.σ r :=
    p7.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready7 : RuntimeReady H capacity (nativeStack sp 80) jal_80007098_call.link d7 :=
    ready6.window_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k7 2 (by decide) (by decide) (by decide)).trans ready6.stack) (gholds_lookup (n := 1) _ p7.regs rfl)
      ready6.aligned rootIn rootW.pins rootW.domain rootW.pool rootW.heap
  have mem7 : d7.σ.mem = writeLog d5.σ.mem (rootLog (p + 8#64)) := by rw [p7.memory, p6.memory]; rfl
  have rootMiss (a w : Nat) (low : a + w ≤ heapStart) (tree : a + w ≤ largeTreeAddr ∨ largeTreeAddr + 8 ≤ a) :
      OutLRange (rootLog (p + 8#64)) a w := by
    simp only [rootLog, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]
    unfold largeTreeAddr at tree
    have lowN : a + w ≤ 0x8007d140 := low
    omega
  -- caml_fl_cur_wsz += size
  obtain ⟨d8, run8, p8⟩ := (mfb_count d7 jal_80007098_call.link (size - 1#64) cur (p + 8#64) ready7.toLeafInput
    ⟨(k7 21 (by decide) (by decide) (by decide)).trans ((k6 21 (by decide) (by decide) (by decide)).trans
      ((k5 21 (by decide) (by decide) (by decide)).trans ((k4 21 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 21) _ p3.regs rfl)))),
      (k7 8 (by decide) (by decide) (by decide)).trans ((k6 8 (by decide) (by decide) (by decide)).trans
        ((k5 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ p4.regs rfl))),
      gholds_lookup (n := 10) _ p7.regs rfl, trivial⟩
    (by rw [mem7, bytesT_writeLog_out _ (rootMiss _ _ (by decide) (by decide)), globalWord _ (by decide)]
        exact A.curWsz)).run d7 ⟨p7.pc, rfl⟩
  have k8 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15]) : gprGet d8.σ r = gprGet d7.σ r :=
    p8.toEffectPost.gpr_frame (by decide) r lo hi out
  have curG := globalWindow_ok (H := H) (lo := flCurWszAddr) (hi := flCurWszAddr + 8) (by decide) (by decide) (by decide)
    (fun a lo hi => by unfold flCurWszAddr at lo hi; unfold allocGlobal InRange; omega) (by decide) (by decide)
  have ready8 : RuntimeReady H capacity (nativeStack sp 80) jal_80007098_call.link d8 :=
    ready7.window_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k8 2 (by decide) (by decide) (by decide)).trans ready7.stack)
      ((k8 1 (by decide) (by decide) (by decide)).trans ready7.raReg) ready7.aligned
      (by simp only [LogInW, InsideW, flCurWszAddr]; decide) curG.pins curG.domain curG.pool curG.heap
  -- no chunk left
  obtain ⟨d9, run9, p9⟩ := (mfb_next d8 jal_80007098_call.link size p (p + 8#64) ready8.toLeafInput
    ⟨(k8 18 (by decide) (by decide) (by decide)).trans ((k7 18 (by decide) (by decide) (by decide)).trans
      ((k6 18 (by decide) (by decide) (by decide)).trans ((k5 18 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 18) _ p4.regs rfl)))),
      (k8 9 (by decide) (by decide) (by decide)).trans ((k7 9 (by decide) (by decide) (by decide)).trans
        ((k6 9 (by decide) (by decide) (by decide)).trans ((k5 9 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 9) _ p4.regs rfl)))),
      (k8 19 (by decide) (by decide) (by decide)).trans ((k7 19 (by decide) (by decide) (by decide)).trans
        ((k6 19 (by decide) (by decide) (by decide)).trans ((k5 19 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 19) _ p4.regs rfl)))),
      gholds_lookup (n := 10) _ p8.regs rfl, trivial⟩).run d8 ⟨p8.pc, rfl⟩
  have k9 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [18, 9, 19]) : gprGet d9.σ r = gprGet d8.σ r :=
    p9.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready9 : RuntimeReady H capacity (nativeStack sp 80) jal_80007098_call.link d9 :=
    ready8.stack_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
      ((k9 2 (by decide) (by decide) (by decide)).trans ready8.stack)
      ((k9 1 (by decide) (by decide) (by decide)).trans ready8.raReg) ready8.aligned A.frame (by simp only [LogInW])
  have mem9 : d9.σ.mem = writeLog (writeLog d5.σ.mem (rootLog (p + 8#64))) [(flCurWszAddr, 8, cur + 1#64 + (size - 1#64))] := by
    rw [p9.memory, show writeLog d8.σ.mem [] = d8.σ.mem from rfl, p8.memory, mem7]
  -- the saved registers
  have saved9 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ mfbSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8) :
      bytesT d9.σ.mem (nativeFrameBase sp 80 + off) 8 = value := by
    have high : heapEnd ≤ nativeFrameBase sp 80 + off := Nat.le_trans frameHigh (Nat.le_add_right _ _)
    rw [mem9, bytesT_writeLog_out _ (by simp only [OutLRange, flCurWszAddr, and_true]; unfold heapEnd at high; omega),
      bytesT_writeLog_out _ (by
        simp only [rootLog, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]; have := pHigh; omega),
      mem5, bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; omega), p3.memory,
      show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory]
    exact A.frame.word_log_read (by intro o w h; simp [mfbSlots] at h; omega) (by simp [mfbSlots]) _ member
  obtain ⟨d10, run10, p10⟩ := (mfb_return d9 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 (p + 8#64) jal_80007098_call.link
    ready9.toLeafInput A.frame ⟨ready9.stack, gholds_lookup (n := 10) _ p9.regs rfl, trivial⟩ saved9
    A.ready.aligned).run d9 ⟨p9.pc, rfl⟩
  have mem10 : d10.σ.mem = d9.σ.mem := p10.memory
  refine ⟨d10, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans run10)))))))), {
    pc := p10.pc
    regs := p10.regs
    ready := ready9.stack_log p10 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p10.regs rfl) (gholds_lookup (n := 1) _ p10.regs rfl) A.ready.aligned A.frame
      (by simp only [LogInW])
    header := by
      rw [mem10, mem9, bytesT_writeLog_out _ (by simp only [OutLRange, flCurWszAddr, and_true]; omega),
        bytesT_writeLog_out _ (by simp only [rootLog, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]; omega), mem5]
      exact word_writeLog_at _ _ 0 _ _ rfl trivial
    tree := by
      rw [mem10, mem9]
      have cur (x : Nat) (hx : heapStart ≤ x) : OutLRange [(flCurWszAddr, 8, cur + 1#64 + (size - 1#64))] x 8 := by
        simp only [OutLRange, flCurWszAddr, and_true]; unfold heapStart at hx; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [bytesT_writeLog_out _ (by simp only [OutLRange, flCurWszAddr, largeTreeAddr, and_true]; decide)]
        exact word_writeLog_at _ _ 5 _ _ rfl trivial
      · rw [bytesT_writeLog_out _ (cur _ (by rw [show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, pf 8 (by decide)]; omega))]
        exact word_writeLog_at _ _ 1 _ _ rfl (by simp only [rootLog, List.drop, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]; omega)
      · rw [bytesT_writeLog_out _ (cur _ (by rw [show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, pf 16 (by decide)]; omega))]
        exact word_writeLog_at _ _ 0 _ _ rfl (by simp only [rootLog, List.drop, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]; omega)
      · rw [bytesT_writeLog_out _ (cur _ (by rw [show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 24 (by decide)]; omega))]
        exact word_writeLog_at _ _ 3 _ _ rfl (by simp only [rootLog, List.drop, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]; omega)
      · rw [bytesT_writeLog_out _ (cur _ (by rw [show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, pf 32 (by decide)]; omega))]
        exact word_writeLog_at _ _ 2 _ _ rfl (by simp only [rootLog, List.drop, OutLRange, show p + 8#64 + 16#64 = p + 8#64 + BitVec.ofNat 64 16 from rfl, show p + 8#64 + 8#64 = p + 8#64 + BitVec.ofNat 64 8 from rfl, show p + 8#64 + 32#64 = p + 8#64 + BitVec.ofNat 64 32 from rfl, show p + 8#64 + 24#64 = p + 8#64 + BitVec.ofNat 64 24 from rfl, pf 16 (by decide), pf 8 (by decide), pf 32 (by decide), pf 24 (by decide), pb, largeTreeAddr, and_true]; omega)
    curWsz := by rw [mem10, mem9]; exact word_writeLog_at _ _ 0 _ _ rfl trivial }⟩
end OCaml.Vm.Boot.Startup
