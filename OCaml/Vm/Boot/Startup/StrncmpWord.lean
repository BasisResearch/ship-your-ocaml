import OCaml.Vm.Boot.Startup.StrncmpEqual
import OCaml.Vm.Primitives.BlockPins
import OCaml.Vm.Boot.Startup.StrncmpDispatch
import OCaml.Vm.Boot.Startup.StrncmpWordSetupNormalized
import OCaml.Vm.Boot.Startup.StrncmpWordSetupImage
import OCaml.Vm.Boot.Startup.StrncmpWordNormalized
import OCaml.Vm.Boot.Startup.StrncmpWordImage
import OCaml.Vm.Boot.Startup.StrncmpWordNextNormalized
import OCaml.Vm.Boot.Startup.StrncmpWordNextImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! `strncmp(p, q, 12)` with `p`, `q` 8-aligned: one word compare, then the
byte loop over the last four bytes. -/

/-- "Caml1999", the exec magic's first word. -/
def magicWord : List (BitVec 8) := [67#8, 97#8, 109#8, 108#8, 49#8, 57#8, 57#8, 57#8]

/-- The registers after the word compare. -/
def strncmpWordRegs (p q : BitVec 64) : GRegs :=
  [(11, q + 8#64), (10, p + 8#64), (12, 4#64), (15, 0#64), (16, 0xc6c6c6ce93929ebc#64), (13, 0x393939316c6d6143#64),
    (14, 0x393939316c6d6143#64), (6, 0xfefefefefefefeff#64), (17, 0x8080808080808080#64), (28, 7#64)]

local macro "wsk" : tactic => `(tactic| simp only [strncmpdispatch_line_80040ccc, strncmpdispatch_line_80040cd0, strncmpwordsetup_line_80040cd8, strncmpwordsetup_line_80040ce0, strncmpwordsetup_line_80040ce4, strncmpwordsetup_line_80040ce8, strncmpwordsetup_line_80040cec, strncmpwordsetup_line_80040cf0, strncmpwordsetup_line_80040cf4, strncmpwordsetup_line_80040cf8, strncmpwordsetup_line_80040cfc, strncmpwordsetup_line_80040d00, strncmpword_line_80040d20, strncmpword_line_80040d24, strncmpword_line_80040d28, strncmpword_line_80040d2c, strncmpword_line_80040d30, strncmpword_line_80040d34, strncmpwordnext_line_80040d08, strncmpwordnext_line_80040d14, strncmpwordnext_line_80040d18, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons, strncmpFirstInput])

/-- `strncmp(p, q, 12)` on aligned strings whose first words are an equal
`magicWord`: on to the byte loop at `p + 8`, `q + 8`, 4. -/
theorem strncmp_word_front (c : Config) (p q ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q 12#64)) (aligned : strncmpAlignment p q = 0#64)
    (left : ReadWindow p 8) (right : ReadWindow q 8)
    (leftWord : read8 c.σ.mem p.toNat = magicWord) (rightWord : read8 c.σ.mem q.toNat = magicWord) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [11, 10, 12, 15, 16, 13, 14, 6, 17, 28] [] c 0x80040d3c#64 (p + 8#64) (strncmpWordRegs p q)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (strncmpX0cc8FSeg ++ strncmpX0cccFSeg ++ strncmpX0cd8FSeg ++ strncmpX0ce0Seg ++ strncmpX0d20TSeg ++ strncmpX0d08FSeg ++ strncmpX0d10FSeg ++ strncmpX0d14TSeg) 0x80040cc8#64
        (strncmpFirstInput p q 12#64) [magicWord, magicWord] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 11, 12]; decide
      shape := by change ChainOK _ [10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := strncmpWord_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strncmp_at_"
        · wsk; decide
        · change guardB bop.BNE (strncmpAlignment p q) 0#64 = false
          rw [aligned]; decide
        · wsk; decide
        · refine memFacts_writeLog (left.ld rfl ?_ (by rw [← leftWord]; exact read8_pins _ _))
            (fun _ => by wsk; simp only [wlogM]; trivial)
          wsk
          rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
        · refine memFacts_writeLog (right.ld rfl ?_ (by rw [← rightWord]; exact read8_pins _ _))
            (fun _ => by wsk; simp only [wlogM]; trivial)
          wsk
          rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
        · wsk; decide
        · wsk; decide
        · wsk; decide
        · wsk; decide }))
  · simp only [strncmpX0cc8FSeg, strncmpX0cccFSeg, strncmpX0cd8FSeg, strncmpX0ce0Seg, strncmpX0d20TSeg, strncmpX0d08FSeg, strncmpX0d10FSeg, strncmpX0d14TSeg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    wsk
    simp only [wlogM, List.nil_append]
  · rfl
  · simp only [strncmpX0cc8FSeg, strncmpX0cccFSeg, strncmpX0cd8FSeg, strncmpX0ce0Seg, strncmpX0d20TSeg, strncmpX0d08FSeg, strncmpX0d10FSeg, strncmpX0d14TSeg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    wsk
    rw [show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
    simp only [strncmpWordRegs, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    repeat (first | exact And.intro (by decide) ?_ | decide)
  · rfl
  · decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- "Caml1999X031", the 4.14 bytecode exec magic. -/
def execMagicByte : Nat → BitVec 8
  | 0 => 67#8 | 1 => 97#8 | 2 => 109#8 | 3 => 108#8 | 4 => 49#8 | 5 => 57#8 | 6 => 57#8 | 7 => 57#8
  | 8 => 88#8 | 9 => 48#8 | 10 => 51#8 | 11 => 49#8 | _ => 0#8

/-- A 12-byte copy of the exec magic at `p`. -/
structure MagicAt (m : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64) : Prop where
  region : ReadWindow p 12
  bytes : ∀ k, k < 12 → (m[p.toNat + k]?).getD 0 = execMagicByte k

theorem MagicAt.word {m p} (h : MagicAt m p) : Primitives.read8 m p.toNat = magicWord := by
  unfold Primitives.read8
  rw [show p.toNat = p.toNat + 0 from rfl, h.bytes 0 (by decide), h.bytes 1 (by decide), h.bytes 2 (by decide),
    h.bytes 3 (by decide), h.bytes 4 (by decide), h.bytes 5 (by decide), h.bytes 6 (by decide), h.bytes 7 (by decide)]
  rfl

theorem MagicAt.window {m p} (h : MagicAt m p) {w : Nat} (hw : w ≤ 12) : ReadWindow p w := by
  refine ⟨h.region.lower, by have := h.region.upper; omega, ?_⟩
  rcases h.region.htif with l | r
  · exact Or.inl (by omega)
  · exact Or.inr r

theorem MagicAt.eight {m p} (h : MagicAt m p) : (p + 8#64).toNat = p.toNat + 8 := by
  have := h.region.upper
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

theorem MagicAt.tail_window {m p} (h : MagicAt m p) : ReadWindow (p + 8#64) (3 + 1) := by
  have r := h.region
  refine ⟨by rw [h.eight]; exact Nat.le_trans r.lower (by omega), by rw [h.eight]; have := r.upper; omega, ?_⟩
  rw [h.eight]; rcases r.htif with l | t
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem magic_tail {c : Config} {p q : BitVec 64} (hp : MagicAt c.σ.mem p) (hq : MagicAt c.σ.mem q) :
    EqualPrefix (p + 8#64) (q + 8#64) 3 (fun k => execMagicByte (k + 8)) c where
  left := hp.tail_window
  right := hq.tail_window
  leftByte := fun k hk => by
    rw [hp.eight, show p.toNat + 8 + k = p.toNat + (k + 8) by omega]; exact hp.bytes _ (by omega)
  rightByte := fun k hk => by
    rw [hq.eight, show q.toNat + 8 + k = q.toNat + (k + 8) by omega]; exact hq.bytes _ (by omega)
  nonzero := fun k hk => by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- `strncmp(p, q, 12)` on two 8-aligned copies of the exec magic returns 0. -/
theorem strncmp_magic (c : Config) (p q ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q 12#64)) (aligned : strncmpAlignment p q = 0#64)
    (hp : MagicAt c.σ.mem p) (hq : MagicAt c.σ.mem q) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [11, 10, 12, 15, 16, 13, 14, 6, 17, 28] [] c ra 0#64
        [(10, 0#64), (1, ra)]) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨d, run1, F⟩ := (strncmp_word_front c p q ra leaf regs aligned (hp.window (by decide)) (hq.window (by decide))
    hp.word hq.word).run c ⟨pc, rfl⟩
  have leafD : LeafInput ra d := ⟨F.good, F.image, F.minstret,
    (F.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, F.tick⟩
  have memD : d.σ.mem = c.σ.mem := F.memory
  have data : EqualPrefix (p + 8#64) (q + 8#64) 3 (fun k => execMagicByte (k + 8)) d := by
    have := magic_tail hp hq
    exact ⟨this.left, this.right, fun k hk => by rw [memD]; exact this.leftByte k hk,
      fun k hk => by rw [memD]; exact this.rightByte k hk, this.nonzero⟩
  obtain ⟨e, run2, B⟩ := (strncmp_bytes_equal d (p + 8#64) (q + 8#64) ra 3 _ leafD data
    ⟨gholds_lookup (n := 10) _ F.regs rfl, gholds_lookup (n := 11) _ F.regs rfl,
      gholds_lookup (n := 12) _ F.regs rfl, trivial⟩).run d ⟨F.pc, rfl⟩
  refine ⟨e, run1.trans run2, ⟨⟨B.good, B.image, B.minstret, B.tick, B.pc, B.result,
    B.memory.trans F.memory, B.output.trans F.output, ?_, F.kept.trans B.kept⟩, ?_⟩⟩
  · intro r outside noise
    exact (B.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega))
      noise).trans (F.frame r outside noise)
  · exact ⟨B.result, gholds_lookup (n := 1) _ B.regs rfl, trivial⟩
end OCaml.Vm.Boot.Startup
