import OCaml.Vm.Boot.Startup.AttemptFailSteps
import OCaml.Vm.Boot.Startup.AttemptOpenSeekNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenSeekImage
import OCaml.Vm.Boot.Startup.AttemptOpenSeekCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenReadNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenReadImage
import OCaml.Vm.Boot.Startup.AttemptOpenReadCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenTrailerNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenTrailerImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicPtrNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicPtrImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicStrNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicStrImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicMidNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicMidImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicEndNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicEndImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicNulNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicNulImage
import OCaml.Vm.Boot.Startup.AttemptOpenQuietNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenQuietImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMagicImage
import OCaml.Vm.Boot.Startup.AttemptOpenMagicCallInterface
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

local macro "tsk" : tactic => `(tactic| simp only [attemptopentrailer_line_8000495c, attemptopentrailer_line_80004964, attemptopentrailer_line_80004968, attemptopentrailer_line_8000496c, attemptopentrailer_line_80004970, attemptopentrailer_line_80004974, attemptopentrailer_line_80004978, attemptopentrailer_line_8000497c, attemptopentrailer_line_80004980, attemptopentrailer_line_80004984, attemptopentrailer_line_80004988, attemptopentrailer_line_8000498c, attemptopentrailer_line_80004990, attemptopentrailer_line_80004994, attemptopentrailer_line_80004998, attemptopentrailer_line_8000499c, attemptopentrailer_line_800049a0, attemptopentrailer_line_800049a4, attemptopentrailer_line_800049a8, attemptopentrailer_line_800049ac, attemptopenquiet_line_800049f8, attemptopenquiet_line_800049fc, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

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


open Sail in
theorem magic_ptr_auipc : 2147502512#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 403351#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2328#12 = BitVec.ofNat 64 Layout.sym_magicstr := by decide

open Sail in
theorem magic_nul_auipc : 2147502576#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 403223#32 +++ 0#12) =
    0x800669f0#64 := by decide

theorem magic_addr (k : Nat) (hk : k < 13) :
    (BitVec.ofNat 64 Layout.sym_magicstr + Functions.sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat =
      Layout.sym_magicstr + k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11 ∨ k = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

local macro "msk" : tactic => `(tactic| simp only [attemptopenmagicptr_line_800049b0, attemptopenmagicptr_line_800049b4, attemptopenmagicstr_line_800049b8, attemptopenmagicstr_line_800049bc, attemptopenmagicstr_line_800049c0, attemptopenmagicstr_line_800049c4, attemptopenmagicmid_line_800049c8, attemptopenmagicmid_line_800049cc, attemptopenmagicmid_line_800049d0, attemptopenmagicmid_line_800049d4, attemptopenmagicmid_line_800049d8, attemptopenmagicmid_line_800049dc, attemptopenmagicend_line_800049e0, attemptopenmagicend_line_800049e4, attemptopenmagicend_line_800049e8, attemptopenmagicend_line_800049ec, attemptopenmagicnul_line_800049f0, attemptopenmagicnul_line_800049f4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

def magicPtrLog (T : Nat → BitVec 8) : List WEntry :=
  []

/-- `magicstr`'s address. -/
theorem magicPtr (c : Config) (ra : BitVec 64) (T : Nat → BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, lbuWord (T 10))]) :
    FnSummary 0x800049b0#64 (fun d => d = c) (WriteRegistersPost [15] (magicPtrLog T) c 0x800049b8#64 (lbuWord (T 10))
      [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10))]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [magicPtrLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX49b0Seg 0x800049b0#64 [(10, lbuWord (T 10))] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagicPtr_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · simp only [caml_attempt_openX49b0Seg, evalBlocks, evalBlock, SegEvalState.init]
    rfl
  · rfl
  · simp only [caml_attempt_openX49b0Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    rw [magic_ptr_auipc]
  · rfl
  · decide

def magicALog (T : Nat → BitVec 8) : List WEntry :=
  [(Layout.sym_magicstr + 6, 1, lbuWord (T 10)), (Layout.sym_magicstr + 0, 1, lbuWord (T 4)),
    (Layout.sym_magicstr + 1, 1, lbuWord (T 5)), (Layout.sym_magicstr + 2, 1, lbuWord (T 6))]

/-- The first four `magicstr` stores. -/
theorem magicA (c : Config) (ra : BitVec 64) (T : Nat → BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10)), (30, lbuWord (T 4)), (29, lbuWord (T 5)), (28, lbuWord (T 6))]) :
    FnSummary 0x800049b8#64 (fun d => d = c) (WriteRegistersPost [] (magicALog T) c 0x800049c8#64 (lbuWord (T 10))
      [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10)), (30, lbuWord (T 4)), (29, lbuWord (T 5)), (28, lbuWord (T 6))]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [magicALog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX49b8Seg 0x800049b8#64 [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10)), (30, lbuWord (T 4)), (29, lbuWord (T 5)), (28, lbuWord (T 6))] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 10, 30, 29, 28]; decide
      shape := by change ChainOK _ [15, 10, 30, 29, 28] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagicStr_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 6)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 0)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 1)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 2)) (by constructor <;> decide) rfl (by msk; decide) }))
  · simp only [caml_attempt_openX49b8Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    simp only [wlogM, wentryM, widthOfM]
    msk
    rw [magic_addr 6 (by decide), magic_addr 0 (by decide), magic_addr 1 (by decide), magic_addr 2 (by decide)]
    rfl
  · rfl
  · simp only [caml_attempt_openX49b8Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
  · rfl
  · decide

def magicBLog (T : Nat → BitVec 8) : List WEntry :=
  [(Layout.sym_magicstr + 3, 1, lbuWord (T 7)), (Layout.sym_magicstr + 4, 1, lbuWord (T 8)),
    (Layout.sym_magicstr + 5, 1, lbuWord (T 9)), (Layout.sym_magicstr + 7, 1, lbuWord (T 11)),
    (Layout.sym_magicstr + 8, 1, lbuWord (T 12)), (Layout.sym_magicstr + 9, 1, lbuWord (T 13))]

/-- Six more `magicstr` stores. -/
theorem magicB (c : Config) (ra : BitVec 64) (T : Nat → BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10)), (6, lbuWord (T 7)), (17, lbuWord (T 8)), (16, lbuWord (T 9)), (11, lbuWord (T 11)), (12, lbuWord (T 12)), (13, lbuWord (T 13))]) :
    FnSummary 0x800049c8#64 (fun d => d = c) (WriteRegistersPost [] (magicBLog T) c 0x800049e0#64 (lbuWord (T 10))
      [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10)), (6, lbuWord (T 7)), (17, lbuWord (T 8)), (16, lbuWord (T 9)), (11, lbuWord (T 11)), (12, lbuWord (T 12)), (13, lbuWord (T 13))]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [magicBLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX49c8Seg 0x800049c8#64 [(15, BitVec.ofNat 64 Layout.sym_magicstr), (10, lbuWord (T 10)), (6, lbuWord (T 7)), (17, lbuWord (T 8)), (16, lbuWord (T 9)), (11, lbuWord (T 11)), (12, lbuWord (T 12)), (13, lbuWord (T 13))] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 10, 6, 17, 16, 11, 12, 13]; decide
      shape := by change ChainOK _ [15, 10, 6, 17, 16, 11, 12, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagicMid_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 3)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 4)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 5)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 7)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 8)) (by constructor <;> decide) rfl (by msk; decide)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 9)) (by constructor <;> decide) rfl (by msk; decide) }))
  · simp only [caml_attempt_openX49c8Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    simp only [wlogM, wentryM, widthOfM]
    msk
    rw [magic_addr 3 (by decide), magic_addr 4 (by decide), magic_addr 5 (by decide), magic_addr 7 (by decide), magic_addr 8 (by decide), magic_addr 9 (by decide)]
    rfl
  · rfl
  · simp only [caml_attempt_openX49c8Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
  · rfl
  · decide

def magicCLog (T : Nat → BitVec 8) : List WEntry :=
  [(Layout.sym_magicstr + 10, 1, lbuWord (T 14)), (Layout.sym_magicstr + 11, 1, lbuWord (T 15))]

/-- The last magic byte. -/
theorem magicC (c : Config) (ra : BitVec 64) (T : Nat → BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, BitVec.ofNat 64 Layout.sym_magicstr), (14, lbuWord (T 14)), (8, WhileMinElfParse.trailSlot)])
    (b15 : (c.σ.mem[WhileMinElfParse.trailSlot.toNat + 15]?).getD 0 = T 15) :
    FnSummary 0x800049e0#64 (fun d => d = c) (WriteRegistersPost [10, 14] (magicCLog T) c 0x800049f0#64 (WhileMinElfParse.trailSlot + 4#64)
      [(10, WhileMinElfParse.trailSlot + 4#64), (14, lbuWord (T 15)), (15, BitVec.ofNat 64 Layout.sym_magicstr), (8, WhileMinElfParse.trailSlot)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [magicCLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX49e0Seg 0x800049e0#64 [(15, BitVec.ofNat 64 Layout.sym_magicstr), (14, lbuWord (T 14)), (8, WhileMinElfParse.trailSlot)] [[T 15]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 14, 8]; decide
      shape := by change ChainOK _ [15, 14, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagicEnd_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 10)) (by constructor <;> decide) rfl (by msk; decide)
        · refine memFacts_stepMem_store rfl ?_ (fun _ => by
            msk; simp only [wentryM, widthOfM, OutLRange, and_true]; msk; decide)
          exact ReadWindow.lbu (x := BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 15)) (by constructor <;> decide) rfl
            (by msk; decide) (by rw [show (BitVec.ofNat 64 (WhileMinElfParse.trailSlot.toNat + 15)).toNat =
              WhileMinElfParse.trailSlot.toNat + 15 by decide]; exact b15)
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 11)) (by constructor <;> decide) rfl (by msk; decide) }))
  · simp only [caml_attempt_openX49e0Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    simp only [wlogM, wentryM, widthOfM]
    msk
    rw [magic_addr 10 (by decide), magic_addr 11 (by decide)]
    rfl
  · rfl
  · simp only [caml_attempt_openX49e0Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    rw [show Functions.sign_extend (m := 64) 4#12 = 4#64 by decide]
  · rfl
  · decide

def magicNulLog (T : Nat → BitVec 8) : List WEntry :=
  [(Layout.sym_magicstr + 12, 1, 0#64)]

/-- `magicstr`'s terminator. -/
theorem magicNul (c : Config) (ra : BitVec 64) (T : Nat → BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, WhileMinElfParse.trailSlot + 4#64)]) :
    FnSummary 0x800049f0#64 (fun d => d = c) (WriteRegistersPost [14] (magicNulLog T) c 0x800049f8#64 (WhileMinElfParse.trailSlot + 4#64)
      [(14, 0x800669f0#64), (10, WhileMinElfParse.trailSlot + 4#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [magicNulLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX49f0Seg 0x800049f0#64 [(10, WhileMinElfParse.trailSlot + 4#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagicNul_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact WriteWindow.sb (x := BitVec.ofNat 64 (Layout.sym_magicstr + 12)) (by constructor <;> decide) rfl (by msk; decide) }))
  · simp only [caml_attempt_openX49f0Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    simp only [wlogM, wentryM, widthOfM]
    msk
    rw [magic_nul_auipc, show (0x800669f0#64 + Functions.sign_extend (m := 64) 2276#12).toNat =
      Layout.sym_magicstr + 12 by decide]
    rfl
  · rfl
  · simp only [caml_attempt_openX49f0Seg, evalBlocks, evalBlock, SegEvalState.init]
    msk
    rw [magic_nul_auipc]
  · rfl
  · decide

local macro "qsk" : tactic => `(tactic| simp only [attemptopenquiet_line_800049f8, attemptopenquiet_line_800049fc, attemptopenmagic_line_80004a04, attemptopenmagic_line_80004a08, attemptopenmagic_line_80004a0c, attemptopenmagic_line_80004a18, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

open Sail in
theorem print_magic_auipc : 2147502584#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 393495#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 4024#12 = BitVec.ofNat 64 Layout.sym_print_magic := by decide

/-- `print_magic` is clear: on to the magic test. -/
theorem attempt_quiet (c : Config) (ra a0 : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, a0)])
    (quiet : read4 c.σ.mem Layout.sym_print_magic = [0#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x800049f8#64 (fun d => d = c) (WriteRegistersPost [14] [] c 0x80004a04#64 a0 [(14, 0#64), (10, a0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX49f8FSeg 0x800049f8#64 [(10, a0)]
        [read4 c.σ.mem Layout.sym_print_magic] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenQuiet_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_print_magic) 4 by constructor <;> decide).lw rfl
            (by qsk; exact print_magic_auipc) (read4_pins _ _)
        · change guardB bop.BNE (bytesVal .lw (read4 c.σ.mem Layout.sym_print_magic)) 0#64 = false
          rw [quiet]; decide }))
  · rfl
  · rfl
  · simp only [caml_attempt_openX49f8FSeg, evalBlocks, evalBlock, SegEvalState.init]
    qsk
    rw [quiet]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    decide
  · rfl
  · decide

open Sail in
theorem exec_magic_auipc : 2147502600#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 333207#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 3560#12 = 0x800557f0#64 := by decide

/-- `strncmp(trail + 4, EXEC_MAGIC, 12)`. -/
theorem attempt_magic_front (c : Config) (ra p : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, p)]) :
    FnSummary 0x80004a04#64 (fun d => d = c)
      (WriteRegistersPost [12, 11] [] c jal_80004a10_call.pc p [(11, 0x800557f0#64), (12, 12#64), (10, p)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX4a04Seg 0x80004a04#64 [(10, p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagic_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · simp only [caml_attempt_openX4a04Seg, evalBlocks, evalBlock, SegEvalState.init]
    qsk
    rw [exec_magic_auipc, show 0#64 + Functions.sign_extend (m := 64) 12#12 = 12#64 by decide]
  · rfl
  · decide

theorem attempt_magic_call (c : Config) (ra p : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, p)]) :
    FnSummary 0x80004a04#64 (fun d => d = c)
      (WriteRegistersPost ([12, 11] ++ [1]) [] c jal_80004a10_call.target p
        ((1, jal_80004a10_call.link) :: [(11, 0x800557f0#64), (12, 12#64), (10, p)])) :=
  block_then_call c jal_80004a10_call_shape jal_80004a10_call_decode (fun _ h => jal_80004a10_call_pins h)
    (attempt_magic_front c ra p leaf regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- The magic matched: `*name = truename`. -/
theorem attempt_name_store (c : Config) (ra name : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 0#64), (18, name), (19, WhileMinElfParse.exeNameSlot)]) :
    FnSummary 0x80004a14#64 (fun d => d = c)
      (WriteRegistersPost [] [(WhileMinElfParse.exeNameSlot.toNat, 8, name)] c 0x80004a1c#64 0#64
        [(10, 0#64), (18, name), (19, WhileMinElfParse.exeNameSlot)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput (caml_attempt_openX4a14FSeg ++ caml_attempt_openX4a18Seg) 0x80004a14#64
        [(10, 0#64), (18, name), (19, WhileMinElfParse.exeNameSlot)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 18, 19]; decide
      shape := by change ChainOK _ [10, 18, 19] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMagic_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · qsk; decide
        · exact (show WriteWindow WhileMinElfParse.exeNameSlot 8 by constructor <;> decide).sd rfl
            (by qsk; rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) }))
  · simp only [caml_attempt_openX4a14FSeg, caml_attempt_openX4a18Seg, evalBlocks, evalBlock, SegEvalState.init,
      List.cons_append, List.nil_append]
    qsk
    simp only [wlogM, wentryM, widthOfM]
    qsk
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
    rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
