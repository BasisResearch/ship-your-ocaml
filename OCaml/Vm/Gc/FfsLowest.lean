import OCaml.Vm.Gc.FfsZero
import OCaml.Vm.Gc.LoopFold

/-! # `ffs` on a nonzero word

newlib's `ffs(x)` (`0x80042cd0`) tests `(x >> i) & 1` for `i = 0, 1, …`
(the loop body is unrolled twice, `0x80042ce0` and `0x80042cf0`) and returns
`i + 1` at the first set bit. For a word whose lowest set bit among the low
32 is `k` (`Lowest x k`) it returns `k + 1`, writes only `a0`, `a4`, `a5` and
no memory (`nonzero`). The best-fit allocator calls it on the filtered
small-list bitmap (`bf_allocate`'s next-size search). -/
namespace OCaml.Vm.Gc.FfsLowest
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def blk (s : List BBlock) : BBlock := s.getD 0 {body := [], term := none}

/-- The loop's bit test `(x >> i) & 1` (`sraw`, `andi`). -/
def test (x i : BitVec 64) : BitVec 64 :=
  Functions.sign_extend (m := 64) (Functions.shift_bits_right_arith (Sail.BitVec.extractLsb x 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb i 31 0) 4 0)) &&& 1#64

/-- The counter step `addiw a4, a4, 1`. -/
def bump (i : BitVec 64) : BitVec 64 := Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (i + 1#64) 31 0)

def pc : BitVec 64 := 0x80042cd0#64
def loopPc : BitVec 64 := 0x80042ce0#64
def entryRegs (ra x : BitVec 64) : GRegs := [(1, ra), (10, x)]
def loopRegs (ra x i : BitVec 64) : GRegs := [(1, ra), (10, x), (14, i)]

def headBlocks : List BBlock := [blk ffsX2cd0TSeg]
/-- bit `i` set: return `i + 1` -/
def exitA : List BBlock := [blk ffsX2ce0TSeg, blk ffsX2cd8Seg]
/-- bits `i`, `i + 1` clear: back to the loop with `i + 2` -/
def again : List BBlock := [blk ffsX2ce0FSeg, blk ffsX2cf0TSeg]
/-- bit `i` clear, `i + 1` set: return `i + 2` -/
def exitB : List BBlock := [blk ffsX2ce0FSeg, blk ffsX2cf0FSeg, blk ffsX2d00Seg, blk ffsX2cd8Seg]

/-- `k` is the lowest set bit of `x`'s low word. -/
structure Lowest (x : BitVec 64) (k : Nat) : Prop where
  small : k < 32
  set : x.getLsbD k = true
  below : ∀ j < k, x.getLsbD j = false

theorem amount (n : Nat) (h : n < 32) :
    Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0) 4 0 = BitVec.ofNat 5 n := by
  have all : ∀ k < 32,
      Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 k) 31 0) 4 0 = BitVec.ofNat 5 k := by decide
  exact all n h

/-- The bit test reads bit `n` of the low word. -/
theorem test_ofNat (x : BitVec 64) {n : Nat} (h : n < 32) :
    test x (BitVec.ofNat 64 n) = if x.getLsbD n then 1#64 else 0#64 := by
  unfold test
  rw [amount n h]
  unfold Functions.shift_bits_right_arith
  simp only [Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_sshiftRight,
    Sail.BitVec.extractLsb]
  have nn : ((n : Int) % 32).toNat = n := by omega
  rw [nn]
  by_cases j0 : j = 0
  · subst j0
    by_cases b : x.getLsbD n <;> simp [b, h, show n ≤ 31 by omega]
  · by_cases b : x.getLsbD n <;> simp [b, j0]

theorem bump_ofNat {n : Nat} (h : n < 33) : bump (BitVec.ofNat 64 n) = BitVec.ofNat 64 (n + 1) := by
  have all : ∀ k < 33, bump (BitVec.ofNat 64 k) = BitVec.ofNat 64 (k + 1) := by decide
  exact all n h

theorem test_set {x : BitVec 64} {n : Nat} (h : n < 32) (b : x.getLsbD n = true) :
    (test x (BitVec.ofNat 64 n) != 0#64) = true := by
  rw [test_ofNat x h, if_pos b]; decide

theorem test_clear {x : BitVec 64} {n : Nat} (h : n < 32) (b : x.getLsbD n = false) :
    (test x (BitVec.ofNat 64 n) != 0#64) = false := by
  rw [test_ofNat x h, if_neg (by simp [b])]; decide

theorem test_clear_eq {x : BitVec 64} {n : Nat} (h : n < 32) (b : x.getLsbD n = false) :
    (test x (BitVec.ofNat 64 n) == 0#64) = true := by
  rw [test_ofNat x h, if_neg (by simp [b])]; decide

theorem test_set_eq {x : BitVec 64} {n : Nat} (h : n < 32) (b : x.getLsbD n = true) :
    (test x (BitVec.ofNat 64 n) == 0#64) = false := by
  rw [test_ofNat x h, if_pos b]; decide

/-! ## Code -/

def allBlocks : List BBlock :=
  [blk ffsX2cd0TSeg, blk ffsX2ce0TSeg, blk ffsX2ce0FSeg, blk ffsX2cf0TSeg, blk ffsX2cf0FSeg, blk ffsX2d00Seg,
    blk ffsX2cd8Seg]

theorem all_code {mem : Std.ExtHashMap Nat (BitVec 8)} (code : Code.FfsLoaded mem) : ChainCode mem allBlocks := by
  intro b member
  simp only [allBlocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals simp only [blk, ffsX2cd0TSeg, ffsX2ce0TSeg, ffsX2ce0FSeg, ffsX2cf0TSeg, ffsX2cf0FSeg, ffsX2d00Seg,
    ffsX2cd8Seg, List.getD_cons_zero, CodeFacts]
  all_goals chain_facts code with "Vsa.Sim.Code.ffs_at_"

theorem code_of {mem : Std.ExtHashMap Nat (BitVec 8)} (code : Code.FfsLoaded mem) {bs : List BBlock}
    (sub : ∀ b ∈ bs, b ∈ allBlocks) : ChainCode mem bs :=
  fun b h => all_code code b (sub b h)

/-! ## Register-level runs -/

theorem src15A (ra x i : BitVec 64) : srcVal 15 (runGM (blk ffsX2ce0TSeg).body (loopRegs ra x i) []) = test x i := rfl
theorem src15A' (ra x i : BitVec 64) : srcVal 15 (runGM (blk ffsX2ce0FSeg).body (loopRegs ra x i) []) = test x i := rfl
theorem src15B (ra x i : BitVec 64) :
    srcVal 15 (runGM (blk ffsX2cf0TSeg).body (runGM (blk ffsX2ce0FSeg).body (loopRegs ra x i) [])
      (ldsRunM (blk ffsX2ce0FSeg).body [])) =
      test x (bump i) := rfl
theorem src15B' (ra x i : BitVec 64) :
    srcVal 15 (runGM (blk ffsX2cf0FSeg).body (runGM (blk ffsX2ce0FSeg).body (loopRegs ra x i) [])
      (ldsRunM (blk ffsX2ce0FSeg).body [])) =
      test x (bump i) := rfl
theorem src10 (ra x : BitVec 64) : srcVal 10 (runGM (blk ffsX2cd0TSeg).body (entryRegs ra x) []) = x := rfl

macro "ffs_data" : tactic => `(tactic|
  simp [AccessPlan, blk, ffsX2cd0TSeg, ffsX2ce0TSeg, ffsX2ce0FSeg, ffsX2cf0TSeg, ffsX2cf0FSeg, ffsX2d00Seg,
    ffsX2cd8Seg, MemFacts, mkLine, decodeM])

theorem ret_control (ra : BitVec 64) (aligned : ra.toNat % 4 = 0) (L : GRegs) (lookup : srcVal 1 L = ra) :
    TermFactsO L (blk ffsX2cd8Seg).term := by
  change (Sail.BitVec.update (srcVal 1 L + Functions.sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
  rw [lookup, ret_tgt ra aligned]
  exact aligned


theorem sub_head : ∀ b ∈ headBlocks, b ∈ allBlocks := by
  intro b h; simp only [headBlocks, List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp [allBlocks]
theorem sub_exitA : ∀ b ∈ exitA, b ∈ allBlocks := by
  intro b h; simp only [exitA, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> simp [allBlocks]
theorem sub_exitB : ∀ b ∈ exitB, b ∈ allBlocks := by
  intro b h; simp only [exitB, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [allBlocks]
theorem sub_again : ∀ b ∈ again, b ∈ allBlocks := by
  intro b h; simp only [again, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> simp [allBlocks]

theorem add_zero12 (v : BitVec 64) : v + Functions.sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero, BitVec.add_zero]

theorem exitA_regs (ra x i : BitVec 64) :
    lookupG 10 (evalBlocks exitA (SegEvalState.init (loopRegs ra x i) [])).regs =
      some (bump i + Functions.sign_extend (m := 64) (0x000#12)) ∧
    lookupG 14 (evalBlocks exitA (SegEvalState.init (loopRegs ra x i) [])).regs = some (bump i) :=
  ⟨rfl, rfl⟩

theorem exitB_regs (ra x i : BitVec 64) :
    lookupG 10 (evalBlocks exitB (SegEvalState.init (loopRegs ra x i) [])).regs =
      some (bump (bump i) + Functions.sign_extend (m := 64) (0x000#12)) ∧
    lookupG 14 (evalBlocks exitB (SegEvalState.init (loopRegs ra x i) [])).regs = some (bump (bump i)) :=
  ⟨rfl, rfl⟩

theorem again_regs (ra x i : BitVec 64) :
    lookupG 1 (evalBlocks again (SegEvalState.init (loopRegs ra x i) [])).regs = some ra ∧
    lookupG 10 (evalBlocks again (SegEvalState.init (loopRegs ra x i) [])).regs = some x ∧
    lookupG 14 (evalBlocks again (SegEvalState.init (loopRegs ra x i) [])).regs = some (bump (bump i)) :=
  ⟨rfl, rfl, rfl⟩

theorem head_regs (ra x : BitVec 64) :
    lookupG 1 (evalBlocks headBlocks (SegEvalState.init (entryRegs ra x) [])).regs = some ra ∧
    lookupG 10 (evalBlocks headBlocks (SegEvalState.init (entryRegs ra x) [])).regs = some x ∧
    lookupG 14 (evalBlocks headBlocks (SegEvalState.init (entryRegs ra x) [])).regs = some (BitVec.ofNat 64 0) :=
  ⟨rfl, rfl, rfl⟩

theorem exitA_pc (ra x i : BitVec 64) :
    evalBlocksPC loopPc (SegEvalState.init (loopRegs ra x i) []) exitA =
      Sail.BitVec.update (ra + Functions.sign_extend (m := 64) (0x000#12)) 0 0#1 := rfl

theorem exitB_pc (ra x i : BitVec 64) :
    evalBlocksPC loopPc (SegEvalState.init (loopRegs ra x i) []) exitB =
      Sail.BitVec.update (ra + Functions.sign_extend (m := 64) (0x000#12)) 0 0#1 := rfl

theorem again_pc (ra x i : BitVec 64) :
    evalBlocksPC loopPc (SegEvalState.init (loopRegs ra x i) []) again = loopPc := rfl

theorem head_pc (ra x : BitVec 64) :
    evalBlocksPC pc (SegEvalState.init (entryRegs ra x) []) headBlocks = loopPc := rfl

theorem no_log (L : GRegs) (bs : List BBlock) (h : (evalBlocks bs (SegEvalState.init L [])).log = []) (m : Std.ExtHashMap Nat (BitVec 8)) :
    writeLog m (evalBlocks bs (SegEvalState.init L [])).log = m := by rw [h]; rfl

/-! ## Iterations -/

/-- The loop's state at `0x80042ce0`. -/
structure Active (ra x : BitVec 64) (k : Nat) (start c : Config) : Prop where
  index : ∃ i, i ≤ k ∧ GHolds c.σ (loopRegs ra x (BitVec.ofNat 64 i))
  pc : PCAt loopPc c
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  memory : c.σ.mem = start.σ.mem
  output : c.σ.sailOutput = start.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10, 14, 15], (gprReg n == r) = false) → c.σ.regs.get? r = start.σ.regs.get? r

/-- `ffs` has returned `k + 1`. -/
structure Post (ra : BitVec 64) (k : Nat) (start after : Config) : Prop where
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (BitVec.ofNat 64 (k + 1))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  memory : after.σ.mem = start.σ.mem
  output : after.σ.sailOutput = start.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = start.σ.regs.get? r

structure Input (ra x : BitVec 64) (k : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.FfsLoaded c.σ.mem
  registers : GHolds c.σ (entryRegs ra x)
  aligned : ra.toNat % 4 = 0
  outside : ra ≠ loopPc
  lowest : Lowest x k

theorem frame_step {before after start : Config} {bs : List BBlock} (written : ∀ n ∈ wrChain bs, n ∈ [10, 14, 15])
    (post : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ wrChain bs, (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r)
    (prior : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [10, 14, 15], (gprReg n == r) = false) → before.σ.regs.get? r = start.σ.regs.get? r) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [10, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = start.σ.regs.get? r :=
  fun r noise outside => (post r noise (fun n hn => outside n (written n hn))).trans (prior r noise outside)

/-- The head: `a4 = 0`, then the loop. -/
theorem head {ra x k c} (input : Input ra x k c) :
    FnSummary pc (fun d => d = c) (Active ra x k c) := by
  have nonzero : (x != 0#64) = true := by
    have b := input.lowest.set
    by_cases z : x = 0#64
    · subst z; simp at b
    · simpa using z
  have summary := block_summary headBlocks pc (entryRegs ra x) [] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [1, 10]; decide,
      chainPlan_facts (code_of input.code sub_head)
        (ChainAccess.cons ⟨by ffs_data, by
          change guardB bop.BNE (srcVal 10 _) (srcVal 0 _) = true
          rw [src10]; exact nonzero⟩ ChainAccess.nil),
      by change ChainOK pc [1, 10] headBlocks; decide, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have regs : GHolds after.σ (loopRegs ra x (BitVec.ofNat 64 0)) :=
    ⟨gholds_lookup _ post.regs (head_regs ra x).1, gholds_lookup _ post.regs (head_regs ra x).2.1,
      gholds_lookup _ post.regs (head_regs ra x).2.2, True.intro⟩
  refine ⟨⟨0, Nat.zero_le _, regs⟩, ?_, post.good, post.tick, post.minstret, ?_, post.output, ?_⟩
  · rw [PCAt, post.pc, head_pc]
  · rw [post.memory]; exact no_log _ _ rfl _
  · exact frame_step (by decide) post.frame (fun _ _ _ => rfl)

/-- The loop's rank: `64 - a4`. -/
def rank (c : Config) : Nat :=
  match gprGet c.σ 14 with
  | some v => 64 - v.toNat
  | none => 0

theorem rank_of {c : Config} {n : Nat} (h : gprGet c.σ 14 = some (BitVec.ofNat 64 n)) (small : n < 64) :
    rank c = 64 - n := by
  unfold rank; rw [h]; simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]

theorem iteration {ra x k start c} (code : Code.FfsLoaded start.σ.mem) (aligned : ra.toNat % 4 = 0)
    (lowest : Lowest x k) (active : Active ra x k start c) :
    ∃ after, Steps c after ∧ (Active ra x k start after ∨ Post ra k start after) ∧ rank after < rank c := by
  obtain ⟨i, le, regs⟩ := active.index
  have codeC : Code.FfsLoaded c.σ.mem := active.memory ▸ code
  have kSmall := lowest.small
  have small : i < 32 := by omega
  have keys : KeysOK (keysG (loopRegs ra x (BitVec.ofNat 64 i))) := by change KeysOK [1, 10, 14]; decide
  have rankC : rank c = 64 - i := rank_of (gholds_lookup _ regs rfl) (by omega)
  by_cases atK : i = k
  · -- bit `i` set: return `i + 1`
    subst atK
    have summary := block_summary exitA loopPc (loopRegs ra x (BitVec.ofNat 64 i)) [] c
      ⟨active.good, active.minstret, regs, keys,
        chainPlan_facts (code_of codeC sub_exitA)
          (ChainAccess.cons ⟨by ffs_data, by
            change guardB bop.BNE (srcVal 15 _) (srcVal 0 _) = true
            rw [src15A]; exact test_set small lowest.set⟩
            (ChainAccess.cons ⟨by ffs_data, ret_control ra aligned _ rfl⟩ ChainAccess.nil)),
        by change ChainOK loopPc [1, 10, 14] exitA; decide, active.tick⟩
    obtain ⟨after, run, post⟩ := summary.run c ⟨active.pc, rfl⟩
    have a4 : gprGet after.σ 14 = some (BitVec.ofNat 64 (i + 1)) := by
      rw [gholds_lookup _ post.regs (exitA_regs ra x _).2, bump_ofNat (by omega)]
    refine ⟨after, run, Or.inr ⟨?_, ?_, post.good, post.tick, post.minstret, ?_, ?_, ?_⟩, ?_⟩
    · rw [PCAt, post.pc, exitA_pc, ret_tgt ra aligned]
    · rw [gholds_lookup _ post.regs (exitA_regs ra x _).1, add_zero12, bump_ofNat (by omega)]
    · rw [post.memory, no_log _ _ rfl, active.memory]
    · rw [post.output, active.output]
    · exact frame_step (by decide) post.frame active.frame
    · rw [rank_of a4 (by omega), rankC]; omega
  · have lt : i < k := by omega
    have clear := lowest.below i lt
    by_cases atK1 : i + 1 = k
    · -- bit `i + 1` set: return `i + 2`
      have set : x.getLsbD (i + 1) = true := atK1 ▸ lowest.set
      have summary := block_summary exitB loopPc (loopRegs ra x (BitVec.ofNat 64 i)) [] c
        ⟨active.good, active.minstret, regs, keys,
          chainPlan_facts (code_of codeC sub_exitB)
            (ChainAccess.cons ⟨by ffs_data, by
              change guardB bop.BNE (srcVal 15 _) (srcVal 0 _) = false
              rw [src15A']; exact test_clear small clear⟩
              (ChainAccess.cons ⟨by ffs_data, by
                change guardB bop.BEQ (srcVal 15 _) (srcVal 0 _) = false
                rw [src15B', bump_ofNat (by omega)]; exact test_set_eq (by omega) set⟩
                (ChainAccess.cons ⟨by ffs_data, trivial⟩
                  (ChainAccess.cons ⟨by ffs_data, ret_control ra aligned _ rfl⟩ ChainAccess.nil)))),
          by change ChainOK loopPc [1, 10, 14] exitB; decide, active.tick⟩
      obtain ⟨after, run, post⟩ := summary.run c ⟨active.pc, rfl⟩
      have a4 : gprGet after.σ 14 = some (BitVec.ofNat 64 (i + 2)) := by
        rw [gholds_lookup _ post.regs (exitB_regs ra x _).2, bump_ofNat (by omega), bump_ofNat (by omega)]
      refine ⟨after, run, Or.inr ⟨?_, ?_, post.good, post.tick, post.minstret, ?_, ?_, ?_⟩, ?_⟩
      · rw [PCAt, post.pc, exitB_pc, ret_tgt ra aligned]
      · rw [gholds_lookup _ post.regs (exitB_regs ra x _).1, add_zero12, bump_ofNat (by omega), bump_ofNat (by omega), ← atK1]
      · rw [post.memory, no_log _ _ rfl, active.memory]
      · rw [post.output, active.output]
      · exact frame_step (by decide) post.frame active.frame
      · rw [rank_of a4 (by omega), rankC]; omega
    · -- bits `i`, `i + 1` clear: back with `i + 2`
      have clear1 := lowest.below (i + 1) (by omega)
      have summary := block_summary again loopPc (loopRegs ra x (BitVec.ofNat 64 i)) [] c
        ⟨active.good, active.minstret, regs, keys,
          chainPlan_facts (code_of codeC sub_again)
            (ChainAccess.cons ⟨by ffs_data, by
              change guardB bop.BNE (srcVal 15 _) (srcVal 0 _) = false
              rw [src15A']; exact test_clear small clear⟩
              (ChainAccess.cons ⟨by ffs_data, by
                change guardB bop.BEQ (srcVal 15 _) (srcVal 0 _) = true
                rw [src15B, bump_ofNat (by omega)]; exact test_clear_eq (by omega) clear1⟩ ChainAccess.nil)),
          by change ChainOK loopPc [1, 10, 14] again; decide, active.tick⟩
      obtain ⟨after, run, post⟩ := summary.run c ⟨active.pc, rfl⟩
      have a4 : gprGet after.σ 14 = some (BitVec.ofNat 64 (i + 2)) := by
        rw [gholds_lookup _ post.regs (again_regs ra x _).2.2, bump_ofNat (by omega), bump_ofNat (by omega)]
      have regs' : GHolds after.σ (loopRegs ra x (BitVec.ofNat 64 (i + 2))) :=
        ⟨gholds_lookup _ post.regs (again_regs ra x _).1, gholds_lookup _ post.regs (again_regs ra x _).2.1, a4, True.intro⟩
      refine ⟨after, run, Or.inl ⟨⟨i + 2, by omega, regs'⟩, ?_, post.good, post.tick, post.minstret, ?_, ?_, ?_⟩, ?_⟩
      · rw [PCAt, post.pc, again_pc]
      · rw [post.memory, no_log _ _ rfl, active.memory]
      · rw [post.output, active.output]
      · exact frame_step (by decide) post.frame active.frame
      · rw [rank_of a4 (by omega), rankC]; omega

/-- **`ffs` on a word with lowest set bit `k`** returns `k + 1`. -/
theorem nonzero {ra x k c} (input : Input ra x k c) : FnSummary pc (fun d => d = c) (Post ra k c) := by
  constructor
  apply Vsa.Logic.Triple.seq (head input).run
  intro middle active
  apply loop_to_exit (entry := loopPc) (active := Active ra x k c) (finished := Post ra k c) rank
    (fun _ a => a.pc) (fun _ p q => input.outside (Option.some.inj (p.pc.symm.trans q)))
    (fun d a => iteration input.code input.aligned input.lowest a) middle active

end OCaml.Vm.Gc.FfsLowest
