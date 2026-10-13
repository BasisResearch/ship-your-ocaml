import OCaml.Vm.Boot.Startup.AttemptFailSteps
import OCaml.Vm.Boot.Startup.AttemptOpenSeekNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenSeekImage
import OCaml.Vm.Boot.Startup.AttemptOpenSeekCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenReadNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenReadImage
import OCaml.Vm.Boot.Startup.AttemptOpenReadCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenTrailerNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenTrailerImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicStrNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicStrImage
import OCaml.Vm.Boot.Startup.AttemptOpenQuietNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenQuietImage
import OCaml.Vm.Boot.Startup.LseekFileSteps
import OCaml.Vm.Boot.Startup.SearchTableReset
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic VsaIris.Inst OCaml.Vm.Primitives LeanRV64DExecutable

/-! caml_attempt_open after `open` returned a descriptor: seek to the
trailer, read it, check the magic, and return the descriptor. -/

local macro "aok" : tactic => `(tactic| simp only [attemptopenfailtest_line_80004924,
  attemptopenfailtest_line_80004928, attemptopenseek_line_80004934, attemptopenseek_line_80004938,
  attemptopenseek_line_8000493c, attemptopenread_line_80004944, attemptopenread_line_8000494c,
  attemptopenread_line_80004950, attemptopenread_line_80004954, eaddrM, srcVal, lookupG, runGM, stepGM,
  eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM,
  List.headD_cons, List.tail_cons])

def attemptSeekRegs (fd flag : BitVec 64) : GRegs :=
  [(10, fd), (11, -16#64), (12, 2#64), (9, fd), (15, -1#64), (20, flag)]

/-- The descriptor is not -1 and `do_open_script` is set: `lseek(fd, -16, SEEK_END)`. -/
theorem attempt_seek_front (c : Config) (ra fd flag : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (20, flag)]) (ok : fd ≠ -1#64) (script : flag ≠ 0#64) :
    FnSummary 0x80004924#64 (fun d => d = c) (WriteRegistersPost [10, 11, 12, 9, 15] [] c jal_80004940_call.pc fd (attemptSeekRegs fd flag)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_attempt_openX4924FSeg ++ caml_attempt_openX4930FSeg ++
        caml_attempt_openX4934Seg) 0x80004924#64 [(10, fd), (20, flag)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 20]; decide
      shape := by change ChainOK _ [10, 20] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenSeek_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · change guardB bop.BEQ fd (0#64 + Functions.sign_extend (m := 64) 4095#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
          exact beq_eq_false_iff_ne.mpr ok
        · change guardB bop.BEQ flag 0#64 = false
          exact beq_eq_false_iff_ne.mpr script }))
  · rfl
  · rfl
  · simp only [caml_attempt_openX4924FSeg, caml_attempt_openX4930FSeg, caml_attempt_openX4934Seg, evalBlocks,
      evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    aok
    simp only [attemptSeekRegs, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    exact ⟨by decide, by decide, by decide⟩
  · rfl
  · decide

theorem attempt_seek_call (c : Config) (ra fd flag : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (20, flag)]) (ok : fd ≠ -1#64) (script : flag ≠ 0#64) :
    FnSummary 0x80004924#64 (fun d => d = c)
      (WriteRegistersPost ([10, 11, 12, 9, 15] ++ [1]) [] c jal_80004940_call.target fd
        ((1, jal_80004940_call.link) :: attemptSeekRegs fd flag)) :=
  block_then_call c jal_80004940_call_shape jal_80004940_call_decode (fun _ h => jal_80004940_call_pins h)
    (attempt_seek_front c ra fd flag leaf regs ok script) (by simp only [attemptSeekRegs, keysG]; decide)
    (by simp only [attemptSeekRegs, KeysAvoidRa, keysG]; decide) rfl

def attemptReadRegs (fd buf : BitVec 64) : GRegs :=
  [(10, fd), (11, buf), (12, 16#64), (15, -1#64), (8, buf), (9, fd)]

/-- `lseek` succeeded: `read(fd, trail, 16)`. -/
theorem attempt_read_front (c : Config) (ra v fd buf : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, v), (8, buf), (9, fd)]) (ok : v ≠ -1#64) :
    FnSummary 0x80004944#64 (fun d => d = c)
      (WriteRegistersPost [15, 12, 11, 10] [] c jal_80004958_call.pc fd (attemptReadRegs fd buf)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_attempt_openX4944FSeg ++ caml_attempt_openX494cSeg) 0x80004944#64
        [(10, v), (8, buf), (9, fd)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 8, 9]; decide
      shape := by change ChainOK _ [10, 8, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenRead_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · change guardB bop.BEQ v (0#64 + Functions.sign_extend (m := 64) 4095#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
          exact beq_eq_false_iff_ne.mpr ok }))
  · rfl
  · rfl
  · simp only [caml_attempt_openX4944FSeg, caml_attempt_openX494cSeg, evalBlocks, evalBlock, SegEvalState.init,
      List.cons_append, List.nil_append]
    aok
    simp only [attemptReadRegs, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    exact ⟨by decide, by decide⟩
  · rfl
  · decide

theorem attempt_read_call (c : Config) (ra v fd buf : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, v), (8, buf), (9, fd)]) (ok : v ≠ -1#64) :
    FnSummary 0x80004944#64 (fun d => d = c)
      (WriteRegistersPost ([15, 12, 11, 10] ++ [1]) [] c jal_80004958_call.target fd
        ((1, jal_80004958_call.link) :: attemptReadRegs fd buf)) :=
  block_then_call c jal_80004958_call_shape jal_80004958_call_decode (fun _ h => jal_80004958_call_pins h)
    (attempt_read_front c ra v fd buf leaf regs ok) (by simp only [attemptReadRegs, keysG]; decide)
    (by simp only [attemptReadRegs, KeysAvoidRa, keysG]; decide) rfl

local macro "tsk" : tactic => `(tactic| simp only [attemptopentrailer_line_8000495c, attemptopentrailer_line_80004964, attemptopentrailer_line_80004968, attemptopentrailer_line_8000496c, attemptopentrailer_line_80004970, attemptopentrailer_line_80004974, attemptopentrailer_line_80004978, attemptopentrailer_line_8000497c, attemptopentrailer_line_80004980, attemptopentrailer_line_80004984, attemptopentrailer_line_80004988, attemptopentrailer_line_8000498c, attemptopentrailer_line_80004990, attemptopentrailer_line_80004994, attemptopentrailer_line_80004998, attemptopentrailer_line_8000499c, attemptopentrailer_line_800049a0, attemptopentrailer_line_800049a4, attemptopentrailer_line_800049a8, attemptopentrailer_line_800049ac, attemptopenmagicstr_line_800049b0, attemptopenmagicstr_line_800049b4, attemptopenmagicstr_line_800049b8, attemptopenmagicstr_line_800049bc, attemptopenmagicstr_line_800049c0, attemptopenmagicstr_line_800049c4, attemptopenmagicstr_line_800049c8, attemptopenmagicstr_line_800049cc, attemptopenmagicstr_line_800049d0, attemptopenmagicstr_line_800049d4, attemptopenmagicstr_line_800049d8, attemptopenmagicstr_line_800049dc, attemptopenmagicstr_line_800049e0, attemptopenmagicstr_line_800049e4, attemptopenmagicstr_line_800049e8, attemptopenmagicstr_line_800049ec, attemptopenmagicstr_line_800049f0, attemptopenmagicstr_line_800049f4, attemptopenquiet_line_800049f8, attemptopenquiet_line_800049fc, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The bytes `caml_attempt_open` reads from the trailer, in its order. -/
def trailerLoads (T : Nat → BitVec 8) (m : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [[T 3], [T 0], [T 1], [T 2], [T 10], [T 4], [T 14], [T 5], [T 6], [T 7], [T 8], [T 9], [T 11], [T 12], [T 13]]

/-- A loaded byte. -/
abbrev lbuWord (b : BitVec 8) : BitVec 64 := bytesVal .lbu [b]

/-- The section count's bytes reversed in place. -/
def trailerSwapLog (T : Nat → BitVec 8) : List WEntry :=
  [(WhileMinElfParse.trailSlot.toNat + 0, 1, lbuWord (T 3)), (WhileMinElfParse.trailSlot.toNat + 3, 1, lbuWord (T 0)),
    (WhileMinElfParse.trailSlot.toNat + 2, 1, lbuWord (T 1)), (WhileMinElfParse.trailSlot.toNat + 1, 1, lbuWord (T 2))]

/-- The magic's bytes, in registers. -/
def trailerSwapRegs (T : Nat → BitVec 8) : GRegs :=
  [(13, lbuWord (T 13)), (12, lbuWord (T 12)), (11, lbuWord (T 11)), (16, lbuWord (T 9)), (17, lbuWord (T 8)),
    (6, lbuWord (T 7)), (28, lbuWord (T 6)), (29, lbuWord (T 5)), (14, lbuWord (T 14)), (30, lbuWord (T 4)),
    (10, lbuWord (T 10)), (15, lbuWord (T 2)), (8, WhileMinElfParse.trailSlot)]

/-- 16 bytes read into the trailer slot: fix the section count's byte order in
place and load the magic's bytes. -/
theorem attempt_swap (c : Config) (ra : BitVec 64) (T : Nat → BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 16#64), (8, WhileMinElfParse.trailSlot)])
    (trail : ∀ k, k < 16 → (c.σ.mem[WhileMinElfParse.trailSlot.toNat + k]?).getD 0 = T k) :
    FnSummary 0x8000495c#64 (fun d => d = c)
      (WriteRegistersPost [13, 12, 11, 16, 17, 6, 28, 29, 14, 30, 10, 15] (trailerSwapLog T) c 0x800049b0#64
        (lbuWord (T 10)) (trailerSwapRegs T)) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [trailerSwapLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput (caml_attempt_openX495cFSeg ++ caml_attempt_openX4964Seg) 0x8000495c#64 [(10, 16#64), (8, WhileMinElfParse.trailSlot)]
        (trailerLoads T c.σ.mem) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 8]; decide
      shape := by change ChainOK _ [10, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenTrailer_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · tsk; decide
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 3)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 3)).toNat =
              WhileMinElfParse.trailSlot.toNat + 3 by decide]; exact trail 3 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 0)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 0)).toNat =
              WhileMinElfParse.trailSlot.toNat + 0 by decide]; exact trail 0 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 1)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 1)).toNat =
              WhileMinElfParse.trailSlot.toNat + 1 by decide]; exact trail 1 (by decide))
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 0)) (by constructor <;> decide) rfl (by tsk; decide)
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 2)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 2)).toNat =
              WhileMinElfParse.trailSlot.toNat + 2 by decide]; exact trail 2 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 10)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 10)).toNat =
              WhileMinElfParse.trailSlot.toNat + 10 by decide]; exact trail 10 (by decide))
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 3)) (by constructor <;> decide) rfl (by tsk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 2)) (by constructor <;> decide) rfl (by tsk; decide)
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 4)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 4)).toNat =
              WhileMinElfParse.trailSlot.toNat + 4 by decide]; exact trail 4 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 14)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 14)).toNat =
              WhileMinElfParse.trailSlot.toNat + 14 by decide]; exact trail 14 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 5)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 5)).toNat =
              WhileMinElfParse.trailSlot.toNat + 5 by decide]; exact trail 5 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 6)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 6)).toNat =
              WhileMinElfParse.trailSlot.toNat + 6 by decide]; exact trail 6 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 7)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 7)).toNat =
              WhileMinElfParse.trailSlot.toNat + 7 by decide]; exact trail 7 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 8)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 8)).toNat =
              WhileMinElfParse.trailSlot.toNat + 8 by decide]; exact trail 8 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 9)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 9)).toNat =
              WhileMinElfParse.trailSlot.toNat + 9 by decide]; exact trail 9 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 11)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 11)).toNat =
              WhileMinElfParse.trailSlot.toNat + 11 by decide]; exact trail 11 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 12)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 12)).toNat =
              WhileMinElfParse.trailSlot.toNat + 12 by decide]; exact trail 12 (by decide))
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ | refine memFacts_stepMem_store rfl ?_ (fun _ => by
            (try tsk) <;> (try simp only [wentryM, widthOfM, OutLRange, and_true]) <;> (try tsk) <;> decide))
          repeat refine memFacts_writeLog ?_ (fun _ => by
            (try tsk) <;> (try simp only [wlogM, wentryM, widthOfM, OutLRange, and_true, List.nil_append,
              List.cons_append]) <;> (try tsk) <;> first | trivial | decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 13)) (by constructor <;> decide) rfl
            (by tsk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 13)).toNat =
              WhileMinElfParse.trailSlot.toNat + 13 by decide]; exact trail 13 (by decide))
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 1)) (by constructor <;> decide) rfl (by tsk; decide) }))
  · simp only [caml_attempt_openX495cFSeg, caml_attempt_openX4964Seg, evalBlocks,
      evalBlock, SegEvalState.init, List.cons_append, List.nil_append, trailerLoads]
    tsk
    simp only [wlogM, wentryM, widthOfM]
    tsk
    rw [show (WhileMinElfParse.trailSlot + Functions.sign_extend (m := 64) 0#12).toNat =
        WhileMinElfParse.trailSlot.toNat + 0 by decide,
      show (WhileMinElfParse.trailSlot + Functions.sign_extend (m := 64) 3#12).toNat =
        WhileMinElfParse.trailSlot.toNat + 3 by decide,
      show (WhileMinElfParse.trailSlot + Functions.sign_extend (m := 64) 2#12).toNat =
        WhileMinElfParse.trailSlot.toNat + 2 by decide,
      show (WhileMinElfParse.trailSlot + Functions.sign_extend (m := 64) 1#12).toNat =
        WhileMinElfParse.trailSlot.toNat + 1 by decide]
    rfl
  · rfl
  · simp only [caml_attempt_openX495cFSeg, caml_attempt_openX4964Seg, evalBlocks,
      evalBlock, SegEvalState.init, List.cons_append, List.nil_append, trailerLoads]
    tsk
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
