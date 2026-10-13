import OCaml.Vm.Boot.Startup.MemcmpEntryNormalized
import OCaml.Vm.Boot.Startup.MemcmpEntryImage
import OCaml.Vm.Boot.Startup.MemcmpTailNormalized
import OCaml.Vm.Boot.Startup.MemcmpTailImage
import OCaml.Vm.Boot.Startup.MemcmpBytesNormalized
import OCaml.Vm.Boot.Startup.MemcmpBytesImage
import OCaml.Vm.Boot.Startup.MemcmpLoopNormalized
import OCaml.Vm.Boot.Startup.MemcmpLoopImage
import OCaml.Vm.Boot.Startup.MemcmpEndNormalized
import OCaml.Vm.Boot.Startup.MemcmpEndImage
import OCaml.Vm.Boot.Startup.MemcmpEqualNormalized
import OCaml.Vm.Boot.Startup.MemcmpEqualImage
import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.NameByte
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! newlib's `memcmp` over a short (at most 7 bytes) equal range: the byte loop. -/

theorem memcmp_short_guard {n : Nat} (lo : 1 ≤ n) (hi : n ≤ 7) :
    guardB bop.BGEU (0#64 + Functions.sign_extend (m := 64) 7#12) (BitVec.ofNat 64 n) = true := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem memcmp_nonzero_guard {n : Nat} (lo : 1 ≤ n) (hi : n ≤ 7) :
    guardB bop.BNE (BitVec.ofNat 64 n) 0#64 = true := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Short length: compare the first byte pair. -/
theorem memcmp_front (c : Config) (ra p q : BitVec 64) (n : Nat) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, p), (11, q), (12, BitVec.ofNat 64 n)]) (lo : 1 ≤ n) (hi : n ≤ 7)
    (wp : ReadWindow p 1) (wq : ReadWindow q 1) (bp : (c.σ.mem[p.toNat]?).getD 0 = b)
    (bq : (c.σ.mem[q.toNat]?).getD 0 = b) :
    FnSummary 0x80040698#64 (fun d => d = c)
      (WriteRegistersPost [13, 12, 15, 14, 10, 11] [] c 0x800406bc#64 (nameCursor p 1)
        [(11, nameCursor q 1), (10, nameCursor p 1), (14, nameByteWord b), (15, nameByteWord b), (12, nameCursor p n),
          (13, 7#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (memcmpX0698TSeg ++ memcmpX06f8TSeg ++ memcmpX06acSeg ++
        memcmpX06c0TSeg) 0x80040698#64 [(10, p), (11, q), (12, BitVec.ofNat 64 n)] [[b], [b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 11, 12]; decide
      shape := by change ChainOK _ [10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have c1 := memcmpEntry_code leaf.image
        have c2 := memcmpTail_code leaf.image
        have c3 := memcmpBytes_code leaf.image
        have c4 := memcmpLoop_code leaf.image
        chain_facts c1 with "Vsa.Sim.Code.memcmp_at_"
        · change guardB bop.BGEU (0#64 + Functions.sign_extend (m := 64) 7#12) (BitVec.ofNat 64 n) = true
          exact memcmp_short_guard lo hi
        · change guardB bop.BNE (BitVec.ofNat 64 n) 0#64 = true
          exact memcmp_nonzero_guard lo hi
        · exact wp.lbu rfl (BitVec.add_zero p) bp
        · exact wq.lbu rfl (BitVec.add_zero q) bq
        · change guardB bop.BEQ (bytesVal .lbu [b]) (bytesVal .lbu [b]) = true
          simp [guardB] }))
  · rfl
  · rfl
  · simp only [memcmpX0698TSeg, memcmpX06f8TSeg, memcmpX06acSeg, memcmpX06c0TSeg, evalBlocks, evalBlock,
      SegEvalState.init, memcmpentry_line_80040698, memcmpbytes_line_800406ac, memcmpbytes_line_800406b0,
      memcmpbytes_line_800406b4, memcmploop_line_800406c0, memcmploop_line_800406c4, memcmploop_line_800406c8,
      memcmploop_line_800406cc, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
      show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide,
      show 0#64 + Functions.sign_extend (m := 64) 7#12 = 7#64 by decide, BitVec.add_assoc (BitVec.ofNat 64 n),
      show (-1#64 : BitVec 64) + 1#64 = 0#64 by decide, BitVec.add_zero, name_lbu_value]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Another equal byte pair. -/
theorem memcmp_step (c : Config) (ra p q : BitVec 64) (n k : Nat) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(12, nameCursor p n), (10, nameCursor p k), (11, nameCursor q k)])
    (differ : nameCursor p n ≠ nameCursor p k)
    (wp : ReadWindow (nameCursor p k) 1) (wq : ReadWindow (nameCursor q k) 1)
    (bp : (c.σ.mem[(nameCursor p k).toNat]?).getD 0 = b) (bq : (c.σ.mem[(nameCursor q k).toNat]?).getD 0 = b) :
    FnSummary 0x800406bc#64 (fun d => d = c)
      (WriteRegistersPost [15, 14, 10, 11] [] c 0x800406bc#64 (nameCursor p (k + 1))
        [(11, nameCursor q (k + 1)), (10, nameCursor p (k + 1)), (14, nameByteWord b), (15, nameByteWord b),
          (12, nameCursor p n)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (memcmpX06bcFSeg ++ memcmpX06c0TSeg) 0x800406bc#64
        [(12, nameCursor p n), (10, nameCursor p k), (11, nameCursor q k)] [[b], [b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [12, 10, 11]; decide
      shape := by change ChainOK _ [12, 10, 11] _; decide
      tick := leaf.tick
      facts := by
        have c1 := memcmpEnd_code leaf.image
        have c2 := memcmpLoop_code leaf.image
        chain_facts c1 with "Vsa.Sim.Code.memcmp_at_"
        · change guardB bop.BEQ (nameCursor p n) (nameCursor p k) = false
          exact beq_eq_false_iff_ne.mpr differ
        · exact wp.lbu rfl (BitVec.add_zero _) bp
        · exact wq.lbu rfl (BitVec.add_zero _) bq
        · change guardB bop.BEQ (bytesVal .lbu [b]) (bytesVal .lbu [b]) = true
          simp [guardB] }))
  · rfl
  · rfl
  · simp only [memcmpX06bcFSeg, memcmpX06c0TSeg, evalBlocks, evalBlock, SegEvalState.init,
      memcmploop_line_800406c0, memcmploop_line_800406c4, memcmploop_line_800406c8,
      memcmploop_line_800406cc, runGM, ldsRunM, wlogM, stepGM, stepLdsM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, nameCursor_next, nameCursor_next, name_lbu_value]
  · rfl
  · decide

/-- All `n` bytes compared equal: return 0. -/
theorem memcmp_done (c : Config) (ra p : BitVec 64) (n : Nat) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(12, nameCursor p n), (10, nameCursor p n), (1, ra)]) :
    FnSummary 0x800406bc#64 (fun d => d = c)
      (WriteRegistersPost [10] [] c ra 0#64 [(10, 0#64), (12, nameCursor p n), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (memcmpX06bcTSeg ++ memcmpX06fcSeg) 0x800406bc#64
        [(12, nameCursor p n), (10, nameCursor p n), (1, ra)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [12, 10, 1]; decide
      shape := by change ChainOK _ [12, 10, 1] _; decide
      tick := leaf.tick
      facts := by
        have c1 := memcmpEnd_code leaf.image
        have c2 := memcmpEqual_code leaf.image
        chain_facts c1 with "Vsa.Sim.Code.memcmp_at_"
        · change guardB bop.BEQ (nameCursor p n) (nameCursor p n) = true
          simp [guardB]
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · rfl
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    rw [ret_tgt ra leaf.aligned]
  · simp only [memcmpX06bcTSeg, memcmpX06fcSeg, evalBlocks, evalBlock, SegEvalState.init, memcmpequal_line_800406fc,
      runGM, ldsRunM, wlogM, stepGM, stepLdsM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.cons_append, List.nil_append]
    rw [show 0#64 + Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
