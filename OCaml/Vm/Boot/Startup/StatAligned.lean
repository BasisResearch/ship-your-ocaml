import OCaml.Vm.Boot.Startup.StatAlignedSteps
import OCaml.Vm.Boot.Startup.StatAllocReady
import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_stat_alloc_aligned_noexc(size, 0, out): `caml_stat_alloc_noexc(size +
4096)`, the next page boundary above the block, and the raw block stored
through `out`, a slot of the caller's frame. -/

/-- caml_stat_alloc_aligned_noexc is called with modulo 0 and an out slot at
`outOff` in the caller's frame `(outSp, outSize)`. -/
structure StatAlignedCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra size out outSp : BitVec 64)
    (outSize outOff : Nat) (c : Config) : Prop where
  pc : PCAt 0x8000ab80#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, size), (11, 0#64), (12, out)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (32 + allocHeadroom)
  charged : vsaChg (size + 4096#64).toNat charge
  outFrame : NativeFrame outSp outSize
  outAt : out = nativeStack outSp outSize + BitVec.ofNat 64 outOff
  outBound : outOff + 8 ≤ outSize
  outAligned : outOff % 8 = 0
  /-- The caller's frame lies at or above the callee's stack pointer. -/
  outAbove : sp.toNat ≤ nativeFrameBase outSp outSize

/-- The block `raw` of `size + 4096` bytes is allocated and stored at `out`;
`pageAbove raw` is returned. -/
structure StatAlignedDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra size out raw : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (1, ra), (10, pageAbove raw)]
  ready : RuntimeReady ((raw.toNat, (size + 4096#64).toNat) :: H) capacity sp ra after
  fresh : FreshBlock vsaLayoutP H raw.toNat (size + 4096#64).toNat
  stored : bytesT after.σ.mem out.toNat 8 = raw
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k
  /-- Memory below the allocator's scratch window that it did not own. -/
  kept : ∀ x, x < sp.toNat - (32 + allocHeadroom) → ¬ vsaFoot H x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  /-- The caller's memory apart from the out slot. -/
  caller : ∀ x, sp.toNat ≤ x → (x < out.toNat ∨ out.toNat + 8 ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem stat_alloc_aligned (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra size out outSp : BitVec 64) (outSize outOff : Nat)
    (A : StatAlignedCall H capacity charge sp ra size out outSp outSize outOff c) :
    ∃ raw after, Steps c after ∧ StatAlignedDone H capacity sp ra size out raw c after := by
  have frame32 : NativeFrame sp 32 := A.frame.resize (by unfold allocHeadroom; omega) (by decide)
  have frameA : NativeFrame (nativeStack sp 32) allocHeadroom := A.frame.nested (front := 32) (by decide)
  have stackNat : (nativeStack sp 32).toNat = sp.toNat - 32 := frame32.stack_nat
  have base0 : nativeFrameBase sp 32 = sp.toNat - 32 := rfl
  have spLow := A.frame.lower
  have regs := A.regs
  -- a5 = 4096; addi sp, sp, -32
  obtain ⟨d1, run1, p1⟩ := (stat_aligned_frame c sp ra size A.ready.toLeafInput
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 10) _ regs rfl, trivial⟩).run c ⟨A.pc, rfl⟩
  have keep1 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [15, 2]) : gprGet d1.σ r = gprGet c.σ r :=
    p1.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready1 : RuntimeReady H (capacity + charge) (nativeStack sp 32) ra d1 :=
    A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide) (gholds_lookup (n := 2) _ p1.regs rfl)
      ((keep1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg) A.ready.aligned frame32
      (by simp only [LogInW])
  -- a0 = size + 4096; save ra, the modulo and out; call caml_stat_alloc_noexc
  obtain ⟨d2, run2, p2⟩ := (stat_aligned_entry d1 sp ra size 0#64 out ready1.toLeafInput frame32
    ⟨gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 15) _ p1.regs rfl,
      (keep1 1 (by decide) (by decide) (by decide)).trans A.ready.raReg, gholds_lookup (n := 2) _ p1.regs rfl,
      (keep1 11 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 11) _ regs rfl),
      (keep1 12 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 12) _ regs rfl), trivial⟩).run d1
    ⟨p1.pc, rfl⟩
  have keep2 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [10] ++ [1]) : gprGet d2.σ r = gprGet d1.σ r :=
    p2.toEffectPost.gpr_frame (by decide) r lo hi out
  have inside2 : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 (statAlignedSlots ra 0#64 out)) :=
    frame32.word_log_inside fun off value member => by simp [statAlignedSlots] at member; omega
  have ready2 : RuntimeReady H (capacity + charge) (nativeStack sp 32) jal_8000ab98_call.link d2 :=
    ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep2 2 (by decide) (by decide) (by decide)).trans ready1.stack) (gholds_lookup (n := 1) _ p2.regs rfl)
      (by decide) frame32 inside2
  have slot2 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ statAlignedSlots ra 0#64 out) :
      bytesT d2.σ.mem (nativeFrameBase sp 32 + off) 8 = value := by
    rw [p2.memory]
    exact frame32.word_log_read (by intro o w h; simp [statAlignedSlots] at h; omega)
      (by simp [statAlignedSlots]) _ member
  -- caml_stat_alloc_noexc(size + 4096)
  obtain ⟨d3, run3, ⟨B⟩⟩ := (stat_alloc_ready d2 H capacity charge (size + 4096#64) _ _ ready2 frameA
    (gholds_lookup (n := 10) _ p2.regs rfl) A.charged).run d2 ⟨p2.pc, rfl⟩
  have fresh : FreshBlock vsaLayoutP H (vsaReg d3 10).toNat (size + 4096#64).toNat := B.allocation.result.fresh
  have rawReg : gprGet d3.σ 10 = some (vsaReg d3 10) := library_gpr B.ready.platform (by decide) (by decide) rfl
  have ready3 : RuntimeReady (((vsaReg d3 10).toNat, (size + 4096#64).toNat) :: H) capacity (nativeStack sp 32)
    jal_8000ab98_call.link d3 := B.ready
  have keep3 (a : Nat) (above : (nativeStack sp 32).toNat ≤ a) :
      (d3.σ.mem[a]?).getD 0 = (d2.σ.mem[a]?).getD 0 := B.caller_byte frameA above
  have saved3 (k : Nat) (member : k ∈ abiSaved) : gprGet d3.σ k = gprGet d2.σ k := B.saved_gpr member
  have pc3 : PCAt jal_8000ab98_call.link d3 := library_pc B.allocation.good B.allocation.result.frame.pc
  generalize hraw : vsaReg d3 10 = raw at fresh rawReg ready3
  have nonzero : raw ≠ 0#64 := fun h => fresh.1 (by rw [h]; rfl)
  -- the out slot
  have outWindow : WriteWindow out 8 := by
    rw [A.outAt, nativeStack, A.outFrame.address _ (by have := A.outBound; omega)]
    exact A.outFrame.word A.outBound A.outAligned
  have outLog : [(out.toNat, 8, raw)] = nativeWordLog outSp outSize [(outOff, raw)] := by
    rw [A.outAt]; rfl
  have outInside : LogInW [⟨nativeFrameBase outSp outSize, outSp.toNat⟩] [(out.toNat, 8, raw)] := by
    rw [outLog]
    exact A.outFrame.word_log_inside fun off value member => by simp at member; have := A.outBound; omega
  have outNat : out.toNat = nativeFrameBase outSp outSize + outOff := by
    rw [A.outAt, nativeStack, A.outFrame.address _ (by have := A.outBound; omega)]
    exact A.outFrame.slot_nat (off := outOff) (by have := A.outBound; omega)
  have outAbove := A.outAbove
  have frameSlot (off : Nat) (bound : off + 8 ≤ 32) (i : Nat) (hi : i < 8) :
      (nativeStack sp 32).toNat ≤ nativeFrameBase sp 32 + off + i := by
    rw [stackNat, base0]; omega
  -- round up, store raw at out
  obtain ⟨d4, run4, p4⟩ := (stat_aligned_round d3 sp jal_8000ab98_call.link raw out ready3.toLeafInput frame32
    ⟨ready3.stack, rawReg, trivial⟩ nonzero
    (by rw [word_observed (m := d2.σ.mem) _ fun i hi => keep3 _ (frameSlot 8 (by decide) i hi)]
        exact slot2 8 0#64 (by simp [statAlignedSlots]))
    (by rw [word_observed (m := d2.σ.mem) _ fun i hi => keep3 _ (frameSlot 0 (by decide) i hi)]
        exact slot2 0 out (by simp [statAlignedSlots]))
    outWindow (A.outFrame.image_outside outInside)).run d3 ⟨pc3, rfl⟩
  have keep4 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [11, 12, 15, 10]) : gprGet d4.σ r = gprGet d3.σ r :=
    p4.toEffectPost.gpr_frame (by decide) r lo hi out
  have ready4 : RuntimeReady ((raw.toNat, (size + 4096#64).toNat) :: H) capacity (nativeStack sp 32)
      jal_8000ab98_call.link d4 :=
    ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
      ((keep4 2 (by decide) (by decide) (by decide)).trans ready3.stack)
      ((keep4 1 (by decide) (by decide) (by decide)).trans ready3.raReg) ready3.aligned A.outFrame outInside
  have below4 (x : Nat) (hx : x < out.toNat ∨ out.toNat + 8 ≤ x) :
      (d4.σ.mem[x]?).getD 0 = (d3.σ.mem[x]?).getD 0 := by
    rw [p4.memory, writeLog_out _ _ _ (by simp only [OutL, and_true]; exact hx)]
  -- restore ra and return
  obtain ⟨d5, run5, p5⟩ := (stat_aligned_return d4 sp ra (pageAbove raw) jal_8000ab98_call.link
    ready4.toLeafInput frame32 ⟨gholds_lookup (n := 2) _ p4.regs rfl, gholds_lookup (n := 10) _ p4.regs rfl, trivial⟩
    (by
      rw [word_observed (m := d2.σ.mem) _ fun i hi => by
        rw [below4 _ (Or.inl (by rw [base0] at *; omega)), keep3 _ (frameSlot 24 (by decide) i hi)]]
      exact slot2 24 ra (by simp [statAlignedSlots]))
    A.ready.aligned).run d4 ⟨p4.pc, rfl⟩
  have keep5 (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 31) (out : r ∉ [1, 2]) : gprGet d5.σ r = gprGet d4.σ r :=
    p5.toEffectPost.gpr_frame (by decide) r lo hi out
  have mem5 : d5.σ.mem = d4.σ.mem := p5.memory
  refine ⟨raw, d5, run1.trans (run2.trans (run3.trans (run4.trans run5))), {
    pc := p5.pc
    regs := p5.regs
    ready := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p5.regs rfl) (gholds_lookup (n := 1) _ p5.regs rfl) A.ready.aligned frame32
      (by simp only [LogInW])
    fresh := fresh
    stored := by
      rw [mem5, p4.memory]
      exact word_writeLog_at _ _ 0 _ _ rfl trivial
    saved := fun k member => by
      have lo : 1 ≤ k := by simp [abiSaved] at member; omega
      have hi : k ≤ 31 := by simp [abiSaved] at member; omega
      have unwritten (L : List Nat) (scratch : ∀ m ∈ L, m ∈ [1, 2, 10, 11, 12, 15]) : k ∉ L := fun h => by
        have := scratch k h
        simp [abiSaved] at member
        simp at this
        omega
      rw [keep5 k lo hi (unwritten _ (by decide)), keep4 k lo hi (unwritten _ (by decide)), saved3 k member,
        keep2 k lo hi (unwritten _ (by decide)), keep1 k lo hi (unwritten _ (by decide))]
    kept := fun x low foot => by
      have lowOut : x < out.toNat := by omega
      have lowA : x < (nativeStack sp 32).toNat - allocHeadroom := by rw [stackNat]; omega
      have lowF : x < nativeFrameBase sp 32 := by rw [base0]; omega
      rw [mem5, below4 x (Or.inl lowOut), B.kept_byte lowA foot, p2.memory,
        frameOn_writeLog _ _ _ inside2 x ⟨Or.inl lowF, trivial⟩, p1.memory]
      rfl
    caller := fun x above outside => by
      rw [mem5, below4 x outside, keep3 x (by rw [stackNat]; omega), p2.memory,
        frameOn_writeLog _ _ _ inside2 x ⟨Or.inr above, trivial⟩, p1.memory]
      rfl }⟩
end OCaml.Vm.Boot.Startup
