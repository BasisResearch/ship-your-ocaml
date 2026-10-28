import OCaml.Vm.Boot.Startup.StrncmpEqual
import OCaml.Vm.Boot.Startup.StrncmpDiffer
import OCaml.Vm.Boot.Startup.StrncmpWordSetupNormalized
import OCaml.Vm.Boot.Startup.StrncmpWordSetupImage
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.BlockCall

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- A four-byte comparison takes the byte path even when both pointers are aligned. -/
theorem strncmp_four_dispatch (c : Config) (p q ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q 4#64)) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [15,28] [] c 0x80040d3c#64 p
        ((15, strncmpAlignment p q) :: strncmpFirstInput p q 4#64)) := by
  by_cases aligned : strncmpAlignment p q = 0#64
  · have summary : FnSummary 0x80040cc8#64 (fun d => d = c)
        (WriteRegistersPost [15,28] [] c 0x80040d3c#64 p
          ((28,7#64) :: (15,strncmpAlignment p q) :: strncmpFirstInput p q 4#64)) := by
      apply registers_of_blocks leaf.image (by constructor <;> trivial)
        (block_summary _ _ _ _ _ (show BlockInput
            (strncmpX0cc8FSeg ++ strncmpX0cccFSeg ++ strncmpX0cd8TSeg) 0x80040cc8#64
            (strncmpFirstInput p q 4#64) [] c from {
          good := leaf.good
          minstret := leaf.minstret
          tick := leaf.tick
          regs := regs
          keys := by change KeysOK [10,11,12]; decide
          shape := by change ChainOK _ [10,11,12] _; decide
          facts := by
            have code := strncmpWordSetup_code leaf.image
            chain_facts code with "Vsa.Sim.Code.strncmp_at_"
            · change guardB bop.BEQ 4#64 0#64 = false
              decide
            · change guardB bop.BNE (strncmpAlignment p q) 0#64 = false
              rw [aligned]; decide
            · change guardB bop.BGEU 7#64 4#64 = true
              decide }))
      · rfl
      · rfl
      · change [(28,7#64),(15,strncmpAlignment p q),(10,p),(11,q),(12,4#64)] = _
        rfl
      · rfl
      · decide
    exact summary.weaken (fun _ h => h) (fun _ h => ⟨h.toEffectPost, h.regs.2⟩)
  · exact (strncmp_dispatch c p q 4 ra leaf regs (by decide) aligned).weaken
      (fun _ h => h) (fun _ h => ⟨h.toEffectPost.widen (by decide), h.regs⟩)

local macro "short_nf" : tactic => `(tactic| simp only [
  strncmpnext_line_80040d54, strncmpnext_line_80040d5c, strncmpnext_line_80040d60,
  runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
  strncmpNextInput, wvalM, wentryM, widthOfM, name_lbu_value,
  List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

/-- A mismatch after an equal byte uses the actual BNE and native subw return. -/
theorem strncmp_next_mismatch (c : Config) (p q stop ra : BitVec 64) (previous l r : BitVec 8)
    (leaf : LeafInput ra c)
    (regs : GHolds c.σ ((1,ra) :: strncmpNextInput p q stop previous))
    (nonzero : previous ≠ 0#8) (left : ReadWindow (p + 1#64) 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[(p + 1#64).toNat]?).getD 0 = l)
    (pinR : (c.σ.mem[q.toNat]?).getD 0 = r) (ne : l ≠ r) :
    FnSummary 0x80040d54#64 (fun d => d = c)
      (WriteRegistersPost [10,15,14] [] c ra (strncmpDiff l r)
        [(10,strncmpDiff l r),(14,nameByteWord r),(15,nameByteWord l),(1,ra),
          (11,q),(12,stop)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput
        (strncmpX0d54FSeg ++ strncmpX0d5cTSeg ++ strncmpX0d78Seg) 0x80040d54#64
        ((1,ra) :: strncmpNextInput p q stop previous) [[l],[r]] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [1,10,11,12,15]; decide
      shape := by change ChainOK _ [1,10,11,12,15] _; decide
      facts := by
        have code := strncmpNext_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strncmp_at_"
        · short_nf
          exact beq_eq_false_iff_ne.mpr (fun eq => nonzero ((nameByteWord_zero previous).mp eq))
        · exact left.lbu rfl (BitVec.add_zero _) pinL
        · exact right.lbu rfl (BitVec.add_zero q) pinR
        · short_nf
          exact bne_iff_ne.mpr (nameByteWord_ne ne)
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · rfl
  · exact ret_tgt ra leaf.aligned
  · change [(10,strncmpDiff l r),(14,bytesVal .lbu [r]),(15,bytesVal .lbu [l]),
      (1,ra),(11,q),(12,stop)] = _
    rw [name_lbu_value,name_lbu_value]
  · rfl
  · decide

/-- Two bytes of a bounded comparison with a shared nonzero first byte. -/
structure SecondMismatch (p q : BitVec 64) (b l r : BitVec 8) (c : Config) : Prop where
  left : ReadWindow p 4
  right : ReadWindow q 4
  leftFirst : (c.σ.mem[p.toNat]?).getD 0 = b
  rightFirst : (c.σ.mem[q.toNat]?).getD 0 = b
  leftSecond : (c.σ.mem[p.toNat + 1]?).getD 0 = l
  rightSecond : (c.σ.mem[q.toNat + 1]?).getD 0 = r
  nonzero : b ≠ 0#8
  different : l ≠ r

/-- Full four-byte call, returning at the actual second-byte mismatch. -/
theorem strncmp_four_second (c : Config) (p q ra : BitVec 64) (b l r : BitVec 8)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (strncmpFirstInput p q 4#64))
    (data : SecondMismatch p q b l r c) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [10,11,12,14,15,28] [] c ra (strncmpDiff l r)
        [(10,strncmpDiff l r),(1,ra)]) := by
  constructor
  rintro before ⟨pc,eq⟩
  subst before
  obtain ⟨a,runA,A⟩ := (strncmp_four_dispatch c p q ra leaf regs).run c ⟨pc,rfl⟩
  have aLeaf : LeafInput ra a := ⟨A.good,A.image,A.minstret,
    (GprsSame.of_post A (by decide)).get (by decide) (by decide) (by decide) leaf.raReg,
    leaf.aligned,A.tick⟩
  have oneP : ReadWindow p 1 := ⟨data.left.lower,by have := data.left.upper; omega,
    by rcases data.left.htif with h | h; exact Or.inl (by omega); exact Or.inr h⟩
  have oneQ : ReadWindow q 1 := ⟨data.right.lower,by have := data.right.upper; omega,
    by rcases data.right.htif with h | h; exact Or.inl (by omega); exact Or.inr h⟩
  obtain ⟨d,runD,D⟩ := (strncmp_first a p q 4#64 ra b aLeaf A.regs.2 oneP oneQ
    (by rw [show a.σ.mem = c.σ.mem from A.memory]; exact data.leftFirst)
    (by rw [show a.σ.mem = c.σ.mem from A.memory]; exact data.rightFirst)).run a ⟨A.pc,rfl⟩
  have dLeaf : LeafInput ra d := ⟨D.good,D.image,D.minstret,
    (GprsSame.of_post D (by decide)).get (by decide) (by decide) (by decide) aLeaf.raReg,
    leaf.aligned,D.tick⟩
  have stop : strncmpEnd p 4#64 = p + 3#64 := by rfl
  have notLast : p ≠ strncmpEnd p 4#64 := by
    rw [stop]; intro h
    have := congrArg BitVec.toNat h
    have := data.left.upper
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at *
    omega
  obtain ⟨e,runE,E⟩ := (strncmp_test d p q (strncmpEnd p 4#64) ra b false dLeaf
    ⟨D.result,gholds_lookup (n := 11) _ D.regs rfl,gholds_lookup (n := 12) _ D.regs rfl,
      gholds_lookup (n := 15) _ D.regs rfl,gholds_lookup (n := 14) _ D.regs rfl,trivial⟩
    (by simp [notLast])).run d ⟨D.pc,rfl⟩
  have eLeaf : LeafInput ra e := ⟨E.good,E.image,E.minstret,
    (GprsSame.of_post E (by decide)).get (by decide) (by decide) (by decide) dLeaf.raReg,
    leaf.aligned,E.tick⟩
  have nextP : (p + 1#64).toNat = p.toNat + 1 := by
    have := data.left.upper
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
  have nextQ : (q + 1#64).toNat = q.toNat + 1 := by
    have := data.right.upper
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
  have mem : e.σ.mem = c.σ.mem := E.memory.trans (D.memory.trans A.memory)
  obtain ⟨after,runF,F⟩ := (strncmp_next_mismatch e p (q + 1#64) (strncmpEnd p 4#64) ra b l r eLeaf
    ⟨eLeaf.raReg,E.result,gholds_lookup (n := 11) _ E.regs rfl,
      gholds_lookup (n := 12) _ E.regs rfl,gholds_lookup (n := 15) _ E.regs rfl,trivial⟩ data.nonzero
    (by simpa only [nameCursor,show BitVec.ofNat 64 1 = 1#64 from rfl] using
      name_window data.left (k := 1) (by decide))
    (by simpa only [nameCursor,show BitVec.ofNat 64 1 = 1#64 from rfl] using
      name_window data.right (k := 1) (by decide))
    (by rw [mem,nextP]; exact data.leftSecond) (by rw [mem,nextQ]; exact data.rightSecond)
    data.different).run e ⟨E.pc,rfl⟩
  have post := write_post_seq A (write_post_seq D (write_post_seq E F))
  exact ⟨after,runA.trans (runD.trans (runE.trans runF)),
    ⟨post.toEffectPost.widen (by decide),F.result,gholds_lookup (n := 1) _ F.regs rfl,trivial⟩⟩

/-- Four-byte dispatcher followed by the existing bounded equal-prefix loop. -/
theorem strncmp_four_equal (c : Config) (p q ra : BitVec 64) (byte : Nat → BitVec 8)
    (leaf : LeafInput ra c) (data : EqualPrefix p q 3 byte c)
    (regs : GHolds c.σ (strncmpFirstInput p q 4#64)) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [10,11,12,14,15,28] [] c ra 0#64 [(10,0#64),(1,ra)]) := by
  constructor
  rintro before ⟨pc,eq⟩
  subst before
  obtain ⟨d,runD,D⟩ := (strncmp_four_dispatch c p q ra leaf regs).run c ⟨pc,rfl⟩
  have dLeaf : LeafInput ra d := ⟨D.good,D.image,D.minstret,
    (GprsSame.of_post D (by decide)).get (by decide) (by decide) (by decide) leaf.raReg,
    leaf.aligned,D.tick⟩
  have dData : EqualPrefix p q 3 byte d := ⟨data.left,data.right,
    fun k hk => by rw [show d.σ.mem = c.σ.mem from D.memory]; exact data.leftByte k hk,
    fun k hk => by rw [show d.σ.mem = c.σ.mem from D.memory]; exact data.rightByte k hk,data.nonzero⟩
  obtain ⟨after,runE,E⟩ := (strncmp_bytes_equal d p q ra 3 byte dLeaf dData D.regs.2).run d ⟨D.pc,rfl⟩
  have post := write_post_seq D E
  exact ⟨after,runD.trans runE,⟨post.toEffectPost.widen (by decide),
    E.result,gholds_lookup (n := 1) _ E.regs rfl,trivial⟩⟩

/-- Four-byte comparison whose actual first bytes differ, regardless of alignment. -/
theorem strncmp_four_first (c : Config) (p q ra : BitVec 64) (l r : BitVec 8)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (strncmpFirstInput p q 4#64))
    (left : ReadWindow p 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[p.toNat]?).getD 0 = l) (pinR : (c.σ.mem[q.toNat]?).getD 0 = r)
    (ne : l ≠ r) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [10,11,12,14,15,28] [] c ra (strncmpDiff l r)
        [(10,strncmpDiff l r),(1,ra)]) := by
  constructor
  rintro before ⟨pc,eq⟩
  subst before
  obtain ⟨d,runD,D⟩ := (strncmp_four_dispatch c p q ra leaf regs).run c ⟨pc,rfl⟩
  have dLeaf : LeafInput ra d := ⟨D.good,D.image,D.minstret,
    (GprsSame.of_post D (by decide)).get (by decide) (by decide) (by decide) leaf.raReg,
    leaf.aligned,D.tick⟩
  obtain ⟨after,runE,E⟩ := (strncmp_differ d p q 4#64 ra l r dLeaf
    ⟨gholds_lookup (n := 10) _ D.regs rfl,gholds_lookup (n := 11) _ D.regs rfl,
      gholds_lookup (n := 12) _ D.regs rfl,dLeaf.raReg,trivial⟩ left right
    (by rw [show d.σ.mem = c.σ.mem from D.memory]; exact pinL)
    (by rw [show d.σ.mem = c.σ.mem from D.memory]; exact pinR) ne).run d ⟨D.pc,rfl⟩
  have post := write_post_seq D E
  exact ⟨after,runD.trans runE,⟨post.toEffectPost.widen (by decide),
    E.result,gholds_lookup (n := 1) _ E.regs rfl,trivial⟩⟩

end OCaml.Vm.Boot.Startup
