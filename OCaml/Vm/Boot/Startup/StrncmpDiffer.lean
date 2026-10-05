import OCaml.Vm.Boot.Startup.StrncmpDifferRows
import OCaml.Vm.Boot.Startup.StrncmpDiffReturnRows
import OCaml.Vm.Boot.Startup.StrncmpDispatch
import OCaml.Vm.Boot.Startup.StrncmpReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- strncmp's native result for differing bytes: `subw` of the zero-extended bytes. -/
def strncmpDiff (l r : BitVec 8) : BitVec 64 :=
  Functions.sign_extend (m := 64)
    (Sail.BitVec.extractLsb (nameByteWord l) 31 0 - Sail.BitVec.extractLsb (nameByteWord r) 31 0)

theorem strncmpDiff_ne {l r : BitVec 8} (ne : l ≠ r) : strncmpDiff l r ≠ 0#64 := by
  intro h
  apply ne
  unfold strncmpDiff nameByteWord at h
  simp only [Functions.sign_extend, Sail.BitVec.extractLsb, Sail.BitVec.signExtend] at h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_signExtend] at this
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.extractLsb_toNat, Nat.shiftRight_zero,
    BitVec.toNat_ofNat] at this
  have hl := l.isLt
  have hr := r.isLt
  split at this <;> omega

theorem nameByteWord_ne {l r : BitVec 8} (ne : l ≠ r) : nameByteWord l ≠ nameByteWord r := by
  intro h
  apply ne
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [nameByteWord, BitVec.toNat_setWidth] at this
  have hl := l.isLt
  have hr := r.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact this

def strncmpDifferBlocks : List BBlock := strncmpX0d3cFSeg ++ strncmpX0d50Seg ++ strncmpX0d78Seg
def strncmpDifferInput (p q n ra : BitVec 64) : GRegs := [(10, p), (11, q), (12, n), (1, ra)]
def strncmpDifferRegs (p q n ra : BitVec 64) (l r : BitVec 8) : GRegs :=
  [(10, strncmpDiff l r), (12, strncmpEnd p n), (14, nameByteWord r), (15, nameByteWord l), (11, q), (1, ra)]

theorem strncmpDiffer_input {p q n ra c} {l r : BitVec 8} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpDifferInput p q n ra)) (left : ReadWindow p 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[p.toNat]?).getD 0 = l) (pinR : (c.σ.mem[q.toNat]?).getD 0 = r) (ne : l ≠ r) :
    BlockInput strncmpDifferBlocks 0x80040d3c#64 (strncmpDifferInput p q n ra) [[l], [r]] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 11, 12, 1]; decide
  shape := by change ChainOK _ [10, 11, 12, 1] _; decide
  tick := leaf.tick
  facts := by
    have code := strncmpFirst_code leaf.image
    chain_facts code with "Vsa.Sim.Code.strncmp_at_"
    · exact left.lbu rfl (BitVec.add_zero p) pinL
    · exact right.lbu rfl (BitVec.add_zero q) pinR
    · change (bytesVal .lbu [l] == bytesVal .lbu [r]) = false
      rw [name_lbu_value, name_lbu_value]
      exact beq_eq_false_iff_ne.mpr (nameByteWord_ne ne)
    · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
      rw [ret_tgt ra leaf.aligned]
      exact leaf.aligned

/-- Bounded comparison whose first bytes differ: one byte step and the native
`subw` return. -/
theorem strncmp_differ (c : Config) (p q n ra : BitVec 64) (l r : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpDifferInput p q n ra)) (left : ReadWindow p 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[p.toNat]?).getD 0 = l) (pinR : (c.σ.mem[q.toNat]?).getD 0 = r) (ne : l ≠ r) :
    FnSummary 0x80040d3c#64 (fun d => d = c)
      (WriteRegistersPost [10, 15, 14, 12] [] c ra (strncmpDiff l r) (strncmpDifferRegs p q n ra l r)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (strncmpDiffer_input leaf regs left right pinL pinR ne))
  · rfl
  · exact ret_tgt ra leaf.aligned
  · change [(10, Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (bytesVal .lbu [l]) 31 0 -
        Sail.BitVec.extractLsb (bytesVal .lbu [r]) 31 0)), (12, p + (n + (-1#64))),
        (14, bytesVal .lbu [r]), (15, bytesVal .lbu [l]), (11, q), (1, ra)] = _
    rw [name_lbu_value, name_lbu_value]
    rfl
  · rfl
  · decide

/-- Complete strncmp for unaligned arguments whose first bytes differ. -/
theorem strncmp_mismatch (c : Config) (p q n ra : BitVec 64) (l r : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpDifferInput p q n ra)) (positive : n ≠ 0#64)
    (unaligned : strncmpAlignment p q ≠ 0#64) (left : ReadWindow p 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[p.toNat]?).getD 0 = l) (pinR : (c.σ.mem[q.toNat]?).getD 0 = r) (ne : l ≠ r) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [15, 10, 14, 12] [] c ra (strncmpDiff l r) (strncmpDifferRegs p q n ra l r)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, dispatched⟩ := (strncmp_dispatch c p q n ra leaf
    ⟨regs.1, regs.2.1, regs.2.2.1, trivial⟩ positive unaligned).run c ⟨pc, rfl⟩
  have leafA : LeafInput ra a := ⟨dispatched.good, dispatched.image, dispatched.minstret,
    (dispatched.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, dispatched.tick⟩
  have same : a.σ.mem = c.σ.mem := dispatched.memory
  have regsA : GHolds a.σ (strncmpDifferInput p q n ra) :=
    ⟨gholds_lookup (n := 10) _ dispatched.regs (by rfl), gholds_lookup (n := 11) _ dispatched.regs (by rfl),
      gholds_lookup (n := 12) _ dispatched.regs (by rfl), leafA.raReg, trivial⟩
  obtain ⟨after, run2, post⟩ := (strncmp_differ a p q n ra l r leafA regsA left right
    (by rw [same]; exact pinL) (by rw [same]; exact pinR) ne).run a ⟨dispatched.pc, rfl⟩
  have effects := (dispatched.toEffectPost.trans post.toEffectPost).widen
    (writes' := [15, 10, 14, 12]) (by decide)
  exact ⟨after, run1.trans run2, ⟨{ effects with memory := post.memory.trans same }, post.regs⟩⟩
end OCaml.Vm.Boot.Startup
