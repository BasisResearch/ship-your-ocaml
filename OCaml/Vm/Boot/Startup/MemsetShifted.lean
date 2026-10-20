import OCaml.Vm.Boot.Startup.MemsetWords
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Boot.Startup.MemsetTail
import OCaml.Vm.Boot.Startup.MemsetBytes
import OCaml.Vm.Boot.Startup.MemsetShiftHeadNormalized
import OCaml.Vm.Boot.Startup.MemsetShiftHeadImage
import OCaml.Vm.Boot.Startup.MemsetShiftHeadCallInterface
import OCaml.Vm.Boot.Startup.MemsetShiftFixNormalized
import OCaml.Vm.Boot.Startup.MemsetShiftFixImage

/-! newlib's `memset(p, 0, n)` for a pointer eight bytes past a 16-byte
boundary (`p ≡ 8 mod 16`) and `n ≡ 0 mod 16`: the misaligned head stores eight
bytes through a computed call into the byte table, the fixup re-enters the
aligned path at `p + 8`, the pair loop clears `(n - 16) / 16` pairs, and the
computed tail stores the last eight bytes. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives

/-- `clearWords` as one write log. -/
def clearLog (base : Nat) : Nat → List WEntry
  | 0 => []
  | n + 1 => clearLog base n ++ [(base + 8 * n, 8, 0#64)]

theorem clearWords_log (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) :
    ∀ n, clearWords m base n = writeLog m (clearLog base n)
  | 0 => rfl
  | n + 1 => by rw [clearWords, clearLog, writeLog_append, clearWords_log m base n]

theorem shifted_mask16 {p : BitVec 64} (shifted : p.toNat % 16 = 8) :
    p &&& Functions.sign_extend (m := 64) 0x00f#12 = 8#64 := by
  rw [show Functions.sign_extend (m := 64) 0x00f#12 = 15#64 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2^4 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  exact shifted

theorem big_guard {n : BitVec 64} (big : 16 ≤ n.toNat) :
    guardB bop.BGEU (0#64 + Functions.sign_extend (m := 64) 15#12) n = false := by
  rw [show 0#64 + Functions.sign_extend (m := 64) 15#12 = 15#64 by decide]
  unfold guardB Functions.zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (by intro hc; exact absurd (Int.ofNat_le.mp hc) (by simp only [BitVec.toNat_ofNat]; omega))

private theorem zero_imm : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

def memsetShiftEntryBlocks : List BBlock := memsetX276cFSeg ++ memsetX2778TSeg

/-- The entry checks on a shifted pointer branch to the misaligned head. -/
theorem memset_shift_entry (c : Config) (p n ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, p), (11, 0#64), (12, n)]) (shifted : p.toNat % 16 = 8) (big : 16 ≤ n.toNat) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [6, 14, 15] c ra 0x8004281c#64 [(15, 8#64), (14, p), (6, 15#64), (10, p), (11, 0#64), (12, n)]) := by
  have mask := shifted_mask16 shifted
  have input : BlockInput memsetShiftEntryBlocks 0x8004276c#64 [(10, p), (11, 0#64), (12, n)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [10, 11, 12]; decide
    shape := by change ChainOK _ [10, 11, 12] _; decide
    tick := leaf.tick
    facts := by
      have code := memsetPrefix_code leaf.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals simp only [memsetprefix_line_8004276c, memsetprefix_line_80042770, memsetprefix_line_80042778, runGM,
        stepGM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, zero_imm, BitVec.add_zero, Nat.reduceEqDiff,
        ite_true, ite_false]
      all_goals try rw [mask]
      all_goals first | exact big_guard big | decide }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetShiftEntryBlocks, memsetX276cFSeg, memsetX2778TSeg, List.cons_append, List.nil_append, evalBlocks,
      evalBlock, SegEvalState.init, memsetprefix_line_8004276c, memsetprefix_line_80042770, memsetprefix_line_80042778,
      runGM, stepGM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, zero_imm, BitVec.add_zero,
      Nat.reduceEqDiff, ite_true, ite_false] at pins
    rw [mask] at pins
    exact ⟨gholds_lookup_eq pins rfl rfl, gholds_lookup (n := 14) _ pins rfl, gholds_lookup_eq pins rfl (by decide),
      gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, trivial⟩
  · decide
  · decide

/-- The head computes the byte-table entry for an eight-byte head and keeps `ra` in `t0`. -/
theorem memset_shift_head (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(15, 8#64), (1, ra)]) :
    FnSummary 0x8004281c#64 (fun d => d = c)
      (BoundaryPost [13, 5] c ra 0x8004282c#64 [(13, 0x80042840#64), (5, ra), (15, 8#64), (1, ra)]) := by
  have input : BlockInput memsetX281cSeg 0x8004281c#64 [(15, 8#64), (1, ra)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [15, 1]; decide
    shape := by change ChainOK _ [15, 1] _; decide
    tick := leaf.tick
    facts := by
      have code := memsetShiftHead_code leaf.image
      chain_facts code with "Vsa.Sim.Code.memset_at_" }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetX281cSeg, evalBlocks, evalBlock, SegEvalState.init, memsetshifthead_line_8004281c,
      memsetshifthead_line_80042820, memsetshifthead_line_80042824, memsetshifthead_line_80042828, runGM, stepGM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by rw [zero_imm, BitVec.add_zero]),
      gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 1) _ pins rfl, trivial⟩
  · decide
  · decide

theorem shift_minus : 8#64 + Functions.sign_extend (m := 64) 0xff0#12 = -8#64 := by decide

theorem fix_guard {n : BitVec 64} (big : 32 ≤ n.toNat) :
    guardB bop.BGEU 15#64 (n + -8#64) = false := by
  unfold guardB Functions.zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  rw [← BitVec.sub_eq_add_neg]
  have sub : (n - 8#64).toNat = n.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]; rfl
  exact decide_eq_false (by intro hc; rw [sub] at hc; exact absurd (Int.ofNat_le.mp hc) (by simp only [BitVec.toNat_ofNat]; omega))

def memsetShiftFixBlocks : List BBlock := memsetX2830FSeg ++ memsetX2844Seg

/-- The fixup restores `ra` and re-enters the aligned path at `p + 8` with `n - 8` bytes. -/
theorem memset_shift_fix (c : Config) (p n ra : BitVec 64) (leaf : LeafInput 0x80042830#64 c)
    (regs : GHolds c.σ [(5, ra), (15, 8#64), (14, p), (12, n), (6, 15#64), (10, p)]) (big : 32 ≤ n.toNat) :
    FnSummary 0x80042830#64 (fun d => d = c)
      (WriteRegistersPost [1, 15, 14, 12] [] c 0x80042780#64 p [(1, ra), (15, -8#64), (14, p - -8#64), (12, n + -8#64),
        (5, ra), (6, 15#64), (10, p)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput memsetShiftFixBlocks 0x80042830#64
        [(5, ra), (15, 8#64), (14, p), (12, n), (6, 15#64), (10, p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [5, 15, 14, 12, 6, 10]; decide
      shape := by change ChainOK _ [5, 15, 14, 12, 6, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := memsetShiftFix_code leaf.image
        chain_facts code with "Vsa.Sim.Code.memset_at_"
        all_goals simp only [memsetshiftfix_line_80042830, memsetshiftfix_line_80042834, memsetshiftfix_line_80042838,
          memsetshiftfix_line_8004283c, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some,
          Nat.reduceEqDiff, ite_true, ite_false, zero_imm, BitVec.add_zero, shift_minus]
        all_goals first | exact fix_guard big | decide }))
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetShiftFixBlocks, memsetX2830FSeg, memsetX2844Seg, List.cons_append, List.nil_append, evalBlocks,
      evalBlock, SegEvalState.init, memsetshiftfix_line_80042830, memsetshiftfix_line_80042834,
      memsetshiftfix_line_80042838, memsetshiftfix_line_8004283c, runGM, stepGM, srcVal, lookupG, eraseG, wvalM,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, zero_imm, BitVec.add_zero, shift_minus] at pins
    exact ⟨gholds_lookup (n := 1) _ pins rfl, gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 14) _ pins rfl,
      gholds_lookup (n := 12) _ pins rfl, gholds_lookup (n := 5) _ pins rfl, gholds_lookup (n := 6) _ pins rfl,
      gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

def memsetRealignBlocks : List BBlock := memsetX2780FSeg ++ memsetX2784Seg

/-- Re-entry at the aligned path: the pair limit and the remainder. -/
theorem memset_realign (c : Config) (b m ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, 0#64), (12, m), (14, b), (10, v)]) :
    FnSummary 0x80042780#64 (fun d => d = c)
      (BoundaryPost [13, 12] c ra 0x80042790#64 [(13, (m &&& Functions.sign_extend (m := 64) 0xff0#12) + b),
        (12, m &&& Functions.sign_extend (m := 64) 0x00f#12), (11, 0#64), (14, b), (10, v)]) := by
  have input : BlockInput memsetRealignBlocks 0x80042780#64 [(11, 0#64), (12, m), (14, b), (10, v)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [11, 12, 14, 10]; decide
    shape := by change ChainOK _ [11, 12, 14, 10] _; decide
    tick := leaf.tick
    facts := by
      have code := memsetPrefix_code leaf.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals simp only [srcVal, lookupG, runGM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
      all_goals decide }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetRealignBlocks, memsetX2780FSeg, memsetX2784Seg, List.cons_append, List.nil_append, evalBlocks,
      evalBlock, SegEvalState.init, memsetprefix_line_80042784, memsetprefix_line_80042788, memsetprefix_line_8004278c,
      runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false] at pins
    exact ⟨gholds_lookup (n := 13) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, gholds_lookup (n := 11) _ pins rfl,
      gholds_lookup (n := 14) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · decide
  · decide

/-- The byte table's eight stores at `q`, for any `q` above the image. -/
theorem bytes_add_nat (q : BitVec 64) (hi : q.toNat + 8 ≤ heapEnd) (k : Nat) (hk : k < 8) :
    (q + BitVec.ofNat 64 k).toNat = q.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : heapEnd < 2 ^ 64 := by decide
  rw [Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem bytes_windows (q : BitVec 64) (lo : Layout.sym_tohost + 16 ≤ q.toNat) (hi : q.toNat + 8 ≤ heapEnd) :
    ∀ i : Nat, i < 8 → WriteWindow (q + BitVec.ofNat 64 i) 1 := fun i hi' => by
  have hE : heapEnd = 0x86800000 := rfl
  have hT : Layout.sym_tohost = 0x80061fc0 := rfl
  rw [hE] at hi
  rw [hT] at lo
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bytes_add_nat q (by rw [hE]; exact hi) i hi'] <;> (try rw [hT]) <;> omega

theorem bytes_outside (q : BitVec 64) (lo : Layout.sym_tohost + 16 ≤ q.toNat) (hi : q.toNat + 8 ≤ heapEnd) :
    ImageOutside (memsetBytesLog q) := by
  have a (k : Nat) (hk : k < 8) := bytes_add_nat q hi k hk
  have hT : Layout.sym_tohost = 0x80061fc0 := rfl
  rw [hT] at lo
  constructor <;> simp only [memsetBytesLog, OutLRange, a 7 (by decide), a 6 (by decide), a 5 (by decide),
    a 4 (by decide), a 3 (by decide), a 2 (by decide), a 1 (by decide), and_true] <;>
    simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega

theorem regFrame_trans {c d e : Config} {W1 W2 W : List Nat}
    (f1 : ∀ r : Register, (∀ n ∈ W1, gprReg n ≠ r) → (∀ q ∈ noiseRegs, (q == r) = false) →
      d.σ.regs.get? r = c.σ.regs.get? r)
    (f2 : ∀ r : Register, (∀ n ∈ W2, gprReg n ≠ r) → (∀ q ∈ noiseRegs, (q == r) = false) →
      e.σ.regs.get? r = d.σ.regs.get? r)
    (s1 : ∀ n ∈ W1, n ∈ W) (s2 : ∀ n ∈ W2, n ∈ W) :
    ∀ r : Register, (∀ n ∈ W, gprReg n ≠ r) → (∀ q ∈ noiseRegs, (q == r) = false) →
      e.σ.regs.get? r = c.σ.regs.get? r :=
  fun r out noise => (f2 r (fun n hn => out n (s2 n hn)) noise).trans (f1 r (fun n hn => out n (s1 n hn)) noise)

/-- The shifted path's writes: the head bytes, the pairs from `p + 8`, the tail bytes. -/
def memsetShiftLog (p : BitVec 64) (count : Nat) : List WEntry :=
  memsetBytesLog p ++ clearLog (p.toNat + 8) (2 * count) ++ memsetBytesLog (pairCursor (p.toNat + 8) count)

def memsetShiftRegs (p ra : BitVec 64) (count : Nat) : GRegs :=
  [(6, 15#64), (14, pairCursor (p.toNat + 8) count), (15, -8#64), (13, 0x800427cc#64), (5, 0x800427b0#64),
    (12, 8#64), (1, ra), (10, p), (11, 0#64)]

/-- `memset(p, 0, n)` with `p ≡ 8 mod 16` and `n = 16 count + 16`. -/
theorem memset_shifted (c : Config) (p n ra : BitVec 64) (count : Nat) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, p), (11, 0#64), (12, n)]) (shifted : p.toNat % 16 = 8) (pos : 0 < count)
    (size : n.toNat = 16 * count + 16) (lower : Layout.sym_tohost + 16 ≤ p.toNat) (upper : p.toNat + n.toNat ≤ heapEnd)
    (limit : (n + -8#64) &&& Functions.sign_extend (m := 64) 0xff0#12 = BitVec.ofNat 64 (16 * count))
    (rem : (n + -8#64) &&& Functions.sign_extend (m := 64) 0x00f#12 = 8#64) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (WriteRegistersPost [6, 14, 15, 13, 5, 12, 1] (memsetShiftLog p count) c ra p (memsetShiftRegs p ra count)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have hE : heapEnd = 0x86800000 := rfl
  have up := upper
  rw [hE] at up
  have base0 : p - -8#64 = pairCursor (p.toNat + 8) 0 := by
    unfold pairCursor
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (-8#64).toNat = 18446744073709551608 from rfl]
    have := p.isLt
    simp only [Nat.reducePow] at *
    omega
  have span : ZeroPairSpan (p.toNat + 8) count := ⟨by omega, by rw [hE]; omega, by omega⟩
  have cur : (pairCursor (p.toNat + 8) count).toNat = p.toNat + 8 + 16 * count := span.cursor_nat (Nat.le_refl _)
  -- the entry checks branch to the misaligned head
  obtain ⟨d1, run1, E⟩ := (memset_shift_entry c p n ra leaf regs shifted (by omega)).run c ⟨pc, rfl⟩
  have gE := GprsSame.of_regFrame (W := [6, 14, 15]) (by decide) E.frame
  obtain ⟨d2, run2, Hd⟩ := (memset_shift_head d1 ra E.toLeafInput
    ⟨gholds_lookup (n := 15) _ E.regs rfl, E.raReg, trivial⟩).run d1 ⟨E.pc, rfl⟩
  have gH := GprsSame.of_regFrame (W := [13, 5]) (by decide) Hd.frame
  -- the computed call into the byte table: eight head bytes
  have callRegs : GHolds d2.σ [(13, 0x80042840#64), (10, p), (11, 0#64), (14, p), (5, ra), (12, n), (6, 15#64),
      (15, 8#64)] :=
    ⟨gholds_lookup (n := 13) _ Hd.regs rfl, gH.get (by decide) (by decide) (by decide) (gholds_lookup (n := 10) _ E.regs rfl),
      gH.get (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ E.regs rfl),
      gH.get (by decide) (by decide) (by decide) (gholds_lookup (n := 14) _ E.regs rfl),
      gholds_lookup (n := 5) _ Hd.regs rfl,
      gH.get (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ E.regs rfl),
      gH.get (by decide) (by decide) (by decide) (gholds_lookup (n := 6) _ E.regs rfl),
      gholds_lookup (n := 15) _ Hd.regs rfl, trivial⟩
  obtain ⟨d3, run3, C⟩ := (indirect_registers_summary jalr_8004282c_call_shape jalr_8004282c_call_decode d2
    (jalr_8004282c_call_pins Hd.image) Hd.good Hd.image Hd.tick Hd.minstret _ callRegs (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) 0x80042840#64 rfl (by decide) (result := p) rfl).run d2 ⟨Hd.pc, rfl⟩
  have tgt : jalr_8004282c_call.target 0x80042840#64 = 0x800427d8#64 := by decide
  have link : jalr_8004282c_call.link = 0x80042830#64 := by decide
  have gC := GprsSame.of_post C (by decide)
  have headIn : MemsetBytesInput p p jalr_8004282c_call.link d3 := {
    toLeafInput := ⟨C.good, C.image, C.minstret, gholds_lookup (n := 1) _ C.regs rfl, by rw [link]; decide, C.tick⟩
    destination := gholds_lookup (n := 10) _ C.regs rfl
    cursor := gholds_lookup (n := 14) _ C.regs rfl
    zero := gholds_lookup (n := 11) _ C.regs rfl
    windows := bytes_windows p lower (by omega)
    outside := bytes_outside p lower (by omega) }
  obtain ⟨d4, run4, B1⟩ := (memset_bytes d3 p p _ headIn).run d3 ⟨by rw [← tgt]; exact C.pc, rfl⟩
  have gB1 := GprsSame.of_post B1 (by decide)
  -- the fixup re-enters the aligned path at p + 8
  have g24 := gC.trans gB1
  obtain ⟨d5, run5, X⟩ := (memset_shift_fix d4 p n ra
    ⟨B1.good, B1.image, B1.minstret, by rw [← link]; exact gholds_lookup (n := 1) _ B1.regs rfl, by decide, B1.tick⟩
    ⟨g24.get (by decide) (by decide) (by decide) (gholds_lookup (n := 5) _ callRegs rfl),
      g24.get (by decide) (by decide) (by decide) (gholds_lookup (n := 15) _ callRegs rfl),
      gholds_lookup (n := 14) _ B1.regs rfl,
      g24.get (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ callRegs rfl),
      g24.get (by decide) (by decide) (by decide) (gholds_lookup (n := 6) _ callRegs rfl),
      gholds_lookup (n := 10) _ B1.regs rfl, trivial⟩ (by omega)).run d4 ⟨by rw [← link]; exact B1.pc, rfl⟩
  have gX := GprsSame.of_post X (by decide)
  obtain ⟨d6, run6, R⟩ := (memset_realign d5 (p - -8#64) (n + -8#64) ra p
    ⟨X.good, X.image, X.minstret, gholds_lookup (n := 1) _ X.regs rfl, leaf.aligned, X.tick⟩
    ⟨gX.get (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ B1.regs rfl), gholds_lookup (n := 12) _ X.regs rfl,
      gholds_lookup (n := 14) _ X.regs rfl, gholds_lookup (n := 10) _ X.regs rfl, trivial⟩).run d5 ⟨X.pc, rfl⟩
  have gR := GprsSame.of_regFrame (W := [13, 12]) (by decide) R.frame
  -- the pairs
  have entry : ZeroPairsAt (p.toNat + 8) count 0 ra p d6 d6 := {
    leaf := R.toLeafInput
    bound := by omega
    pc := by simp only [pos, ite_true]; exact R.pc
    destination := gholds_lookup (n := 10) _ R.regs rfl
    zero := gholds_lookup (n := 11) _ R.regs rfl
    cursor := by rw [← base0]; exact gholds_lookup (n := 14) _ R.regs rfl
    limitReg := by
      have v := gholds_lookup (n := 13) _ R.regs rfl
      rw [limit, base0] at v
      have addr : BitVec.ofNat 64 (16 * count) + pairCursor (p.toNat + 8) 0 = pairCursor (p.toNat + 8) count := by
        simp only [pairCursor, ← BitVec.ofNat_add]
        congr 1; omega
      rw [addr] at v
      exact v
    memory := rfl
    output := rfl
    frame := fun _ _ _ => rfl }
  obtain ⟨d7, run7, Z⟩ := zero_pairs span d6 d6 entry
  have gZ := GprsSame.of_regFrame (W := [14]) (by decide) Z.frame
  -- the computed tail: eight bytes
  have pc7 : PCAt 0x800427a0#64 d7 := by have := Z.pc; simp only [Nat.lt_irrefl, ite_false] at this; exact this
  have size6 : gprGet d6.σ 12 = some 8#64 := by have := gholds_lookup (n := 12) _ R.regs rfl; rw [rem] at this; exact this
  have mask6 : gprGet d6.σ 6 = some 15#64 := gR.get (by decide) (by decide) (by decide) (gholds_lookup (n := 6) _ X.regs rfl)
  obtain ⟨d8, run8, T⟩ := (memset_tail_dispatch d7 ra Z.leaf (gZ.get (by decide) (by decide) (by decide) size6)
    (gZ.get (by decide) (by decide) (by decide) mask6)).run d7 ⟨pc7, rfl⟩
  have gT := GprsSame.of_regFrame (W := [13, 5]) (by decide) T.frame
  have tailIn : MemsetBytesInput p (pairCursor (p.toNat + 8) count) ra d8 := {
    toLeafInput := T.toLeafInput
    destination := gT.get (by decide) (by decide) (by decide) Z.destination
    cursor := gT.get (by decide) (by decide) (by decide) Z.cursor
    zero := gT.get (by decide) (by decide) (by decide) Z.zero
    windows := bytes_windows _ (by rw [cur]; omega) (by rw [cur, hE]; omega)
    outside := bytes_outside _ (by rw [cur]; omega) (by rw [cur, hE]; omega) }
  obtain ⟨d9, run9, B2⟩ := (memset_bytes d8 p _ ra tailIn).run d8 ⟨T.pc, rfl⟩
  have gB2 := GprsSame.of_post B2 (by decide)
  have pairsKept : GprsKept d6 d7 :=
    GprsKept.of_regFrame (W := [14]) (by decide) (by decide)
      (fun n hn => by rw [List.mem_singleton.mp hn, Z.cursor]; rfl) Z.frame
  have g15 := (((gR.trans gZ).trans gT).trans gB2).get (n := 15) (by decide) (by decide) (by decide)
    (gholds_lookup (n := 15) _ X.regs rfl)
  refine ⟨d9, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9))))))),
    { toEffectPost := {
        good := B2.good
        image := B2.image
        minstret := B2.minstret
        tick := B2.tick
        pc := B2.pc
        result := B2.result
        memory := ?_
        output := B2.output.trans (T.output.trans (Z.output.trans (R.output.trans (X.output.trans (B1.output.trans
          (C.output.trans (Hd.output.trans E.output)))))))
        frame := ?_
        kept := E.kept.trans (Hd.kept.trans (C.kept.trans (B1.kept.trans (X.kept.trans (R.kept.trans (pairsKept.trans
          (T.kept.trans B2.kept))))))) }
      regs := ⟨gB2.get (by decide) (by decide) (by decide) (gholds_lookup (n := 6) _ T.regs rfl),
        gholds_lookup (n := 14) _ B2.regs rfl, g15,
        gB2.get (by decide) (by decide) (by decide) (gholds_lookup (n := 13) _ T.regs rfl),
        gB2.get (by decide) (by decide) (by decide) (gholds_lookup (n := 5) _ T.regs rfl),
        gB2.get (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ T.regs rfl),
        gholds_lookup (n := 1) _ B2.regs rfl, gholds_lookup (n := 10) _ B2.regs rfl,
        gholds_lookup (n := 11) _ B2.regs rfl, trivial⟩ }⟩
  · rw [B2.memory, T.memory, Z.memory, R.memory, X.memory, show writeLog d4.σ.mem [] = d4.σ.mem from rfl, B1.memory,
      C.memory, Hd.memory, E.memory, clearWords_log, ← writeLog_append, ← writeLog_append, memsetShiftLog,
      List.append_assoc]
  · have f1 := regFrame_trans E.frame Hd.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    have f2 := regFrame_trans f1 C.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    have f3 := regFrame_trans f2 B1.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    have f4 := regFrame_trans f3 X.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    have f5 := regFrame_trans f4 R.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    have f6 := regFrame_trans f5 Z.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    have f7 := regFrame_trans f6 T.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)
    exact regFrame_trans f7 B2.frame (W := [6, 14, 15, 13, 5, 12, 1]) (by decide) (by decide)

theorem LogInW.append {ws : List W} : ∀ {l1 l2 : List WEntry}, LogInW ws l1 → LogInW ws l2 → LogInW ws (l1 ++ l2)
  | [], _, _, h2 => h2
  | _ :: _, _, h1, h2 => ⟨h1.1, LogInW.append h1.2 h2⟩

theorem clearLog_in {lo hi base : Nat} : ∀ n, lo ≤ base → base + 8 * n ≤ hi → LogInW [⟨lo, hi⟩] (clearLog base n)
  | 0, _, _ => trivial
  | n + 1, h1, h2 => LogInW.append (clearLog_in n h1 (by omega))
      ⟨by simp only [InsideW, or_false]; omega, trivial⟩

theorem bytesLog_in (q : BitVec 64) {lo hi : Nat} (h1 : lo ≤ q.toNat) (h2 : q.toNat + 8 ≤ hi) (fits : q.toNat + 8 ≤ heapEnd) :
    LogInW [⟨lo, hi⟩] (memsetBytesLog q) := by
  have a (k : Nat) (hk : k < 8) := bytes_add_nat q fits k hk
  simp only [memsetBytesLog, LogInW, InsideW, or_false, a 7 (by decide), a 6 (by decide), a 5 (by decide),
    a 4 (by decide), a 3 (by decide), a 2 (by decide), a 1 (by decide), and_true]
  omega

/-- The shifted path writes only `[p, p + n)`. -/
theorem memsetShiftLog_in (p : BitVec 64) (count : Nat) (upper : p.toNat + 16 * count + 16 ≤ heapEnd) :
    LogInW [⟨p.toNat, p.toNat + 16 * count + 16⟩] (memsetShiftLog p count) := by
  have hE : heapEnd = 0x86800000 := rfl
  have cur : (pairCursor (p.toNat + 8) count).toNat = p.toNat + 8 + 16 * count := by
    unfold pairCursor
    rw [BitVec.toNat_ofNat]
    rw [hE] at upper
    exact Nat.mod_eq_of_lt (by omega)
  have up := upper
  rw [hE] at up
  exact LogInW.append
    (LogInW.append (bytesLog_in p (lo := p.toNat) (hi := p.toNat + 16 * count + 16) (Nat.le_refl _) (by omega)
        (by rw [hE]; omega))
      (clearLog_in (lo := p.toNat) (hi := p.toNat + 16 * count + 16) (base := p.toNat + 8) (2 * count) (by omega)
        (by omega)))
    (bytesLog_in _ (lo := p.toNat) (hi := p.toNat + 16 * count + 16) (by rw [cur]; omega) (by rw [cur]; omega)
      (by rw [cur, hE]; omega))

end OCaml.Vm.Boot.Startup
