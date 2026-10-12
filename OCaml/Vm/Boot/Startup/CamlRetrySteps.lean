import OCaml.Vm.Boot.Startup.CamlAttemptTestNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptTestImage
import OCaml.Vm.Boot.Startup.CamlAttemptExeNameNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptExeNameCallInterface
import OCaml.Vm.Boot.Startup.CamlAttemptExeLeafNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptExeLeafImage
import OCaml.Vm.Boot.Startup.CamlAttemptExeTestNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptExeTestImage
import OCaml.Vm.Boot.Startup.CamlAttemptArgv1Normalized
import OCaml.Vm.Boot.Startup.CamlAttemptArgv1Image
import OCaml.Vm.Boot.Startup.CamlAttemptDashNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptDashImage
import OCaml.Vm.Boot.Startup.CamlAttemptConfigNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptConfigImage
import OCaml.Vm.Boot.Startup.CamlAttemptProgNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptProgCallInterface
import OCaml.Vm.Boot.Startup.CamlAttemptProgImage
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.Argv0Name
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! caml_main after the first caml_attempt_open fails: `caml_executable_name()`
is NULL, `argv[1]` ("/prog") is not an option, `print_config` is clear, and
caml_attempt_open(&exe_name, &trail, 1) is called on `argv[1]`. -/

def argvPtr : BitVec 64 := BitVec.ofNat 64 WhileMinImage.argvArray
def argv1Ptr : BitVec 64 := BitVec.ofNat 64 WhileMinImage.argv1

/-- `argv[1]`'s entry and first byte, from any state keeping the embedded image. -/
theorem argv1_entry {c : Config} (h : EmbedImage c) : bytesT c.σ.mem (argvPtr + 8#64).toNat 8 = argv1Ptr := by
  rw [show (argvPtr + 8#64).toNat = WhileMinImage.argvArray + 8 * 1 from by decide,
    h.argv_word 1 (by decide), show WhileMinImage.argvArray + 8 * 1 = WhileMinImage.argvArray + 8 from rfl,
    WhileMinImage.argv_entry1]
  rfl

theorem argv1_byte {c : Config} (h : EmbedImage c) (k : Nat) (hk : k ≤ 5) :
    (c.σ.mem[argv1Ptr.toNat + k]?).getD 0 = BitVec.ofNat 8 (byteVal WhileMinImage.argv1Chars k) := by
  have inside : EmbedByte (WhileMinImage.argv1 + k) := by
    constructor
    · unfold WhileMinImage.argv1 Vsa.Sim.DlHeap.heapEnd; omega
    · unfold WhileMinImage.argv1 embedLimit Layout.sym_stack_top Layout.sym_stack_size; omega
  rw [show argv1Ptr.toNat = WhileMinImage.argv1 from by decide, h.byte _ inside]
  exact cstr_getD_le WhileMinImage.argv1_string k hk

/-- `fd < 0`: s0 = fd, s4 = 0, try the executable's own name. -/
theorem caml_retry_test (c : Config) (ra fd : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, fd)])
    (negative : fd = -1#64 ∨ fd = -4#64) :
    FnSummary 0x80004dfc#64 (fun d => d = c)
      (WriteRegistersPost [8, 20] [] c 0x80005024#64 fd [(20, 0#64), (8, fd), (10, fd)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX4dfcTSeg 0x80004dfc#64 [(10, fd)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        change guardB bop.BLT fd 0#64 = true
        rcases negative with rfl | rfl <;> decide }))
  · rfl
  · rfl
  · simp only [caml_mainX4dfcTSeg, evalBlocks, evalBlock, SegEvalState.init, camlattempttest_line_80004dfc,
      camlattempttest_line_80004e00, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
    simp only [BitVec.add_zero]
  · rfl
  · decide

/-- `caml_executable_name()` is NULL on this platform. -/
theorem caml_executable_name_null (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(1, ra)]) :
    FnSummary 0x800256dc#64 (fun e => e = c) (WriteRegistersPost [10] [] c ra 0#64 [(10, 0#64), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_executable_nameX56dcSeg 0x800256dc#64 [(1, ra)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [1]; decide
      shape := by change ChainOK _ [1] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptExeLeaf_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_executable_name_at_"
        change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
        rw [ret_tgt ra leaf.aligned]
        exact leaf.aligned }))
  · rfl
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    rw [ret_tgt ra leaf.aligned]
  · simp only [caml_executable_nameX56dcSeg, evalBlocks, evalBlock, SegEvalState.init, camlattemptexeleaf_line_800256dc,
      runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM,
      List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show 0#64 + Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
  · rfl
  · decide

/-- No executable name: fall back to `argv[1]`. -/
theorem caml_retry_noname (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, 0#64)]) :
    FnSummary 0x80005028#64 (fun d => d = c) (WriteRegistersPost [] [] c 0x80005048#64 0#64 [(10, 0#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX5028TSeg 0x80005028#64 [(10, 0#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptExeTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        change guardB bop.BEQ 0#64 0#64 = true
        decide }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- `s0 = argv[1]` (non-NULL), `s4 = 1`. -/
theorem caml_retry_argv1 (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (image : EmbedImage c)
    (regs : GHolds c.σ [(9, argvPtr), (10, 0#64)]) :
    FnSummary 0x80005048#64 (fun d => d = c)
      (WriteRegistersPost [8, 20] [] c 0x80005054#64 0#64 [(20, 1#64), (8, argv1Ptr), (9, argvPtr), (10, 0#64)]) := by
  have entry : bytesVal .ld (read8 c.σ.mem (argvPtr + 8#64).toNat) = argv1Ptr := by
    rw [read8_value]; exact argv1_entry image
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX5048FSeg 0x80005048#64 [(9, argvPtr), (10, 0#64)]
        [read8 c.σ.mem (argvPtr + 8#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 10]; decide
      shape := by change ChainOK _ [9, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptArgv1_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact (show ReadWindow (argvPtr + 8#64) 8 by constructor <;> decide).ld rfl
            (by change argvPtr + Functions.sign_extend (m := 64) 8#12 = argvPtr + 8#64; rfl) (read8_pins _ _)
        · change guardB bop.BEQ (bytesVal .ld (read8 c.σ.mem (argvPtr + 8#64).toNat)) 0#64 = false
          rw [entry]
          decide }))
  · rfl
  · rfl
  · simp only [caml_mainX5048FSeg, evalBlocks, evalBlock, SegEvalState.init, camlattemptargv1_line_80005048,
      camlattemptargv1_line_8000504c, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show 0#64 + Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, entry]
  · rfl
  · decide

/-- `argv[1][0]` is '/', not '-'. -/
theorem caml_retry_dash (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (image : EmbedImage c)
    (regs : GHolds c.σ [(8, argv1Ptr), (10, 0#64)]) :
    FnSummary 0x80005054#64 (fun d => d = c)
      (WriteRegistersPost [15, 14] [] c 0x800050fc#64 0#64 [(14, 45#64), (15, 47#64), (8, argv1Ptr), (10, 0#64)]) := by
  have slash : bytesVal .lbu [(c.σ.mem[argv1Ptr.toNat]?).getD 0] = 47#64 := by
    have := argv1_byte image 0 (by decide)
    rw [Nat.add_zero] at this
    rw [this]; decide
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX5054TSeg 0x80005054#64 [(8, argv1Ptr), (10, 0#64)]
        [[(c.σ.mem[argv1Ptr.toNat]?).getD 0]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 10]; decide
      shape := by change ChainOK _ [8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptDash_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact (show ReadWindow argv1Ptr 1 by constructor <;> decide).lbu rfl
            (by change argv1Ptr + Functions.sign_extend (m := 64) 0#12 = argv1Ptr; decide) rfl
        · change guardB bop.BNE (bytesVal .lbu [(c.σ.mem[argv1Ptr.toNat]?).getD 0])
            (0#64 + Functions.sign_extend (m := 64) 45#12) = true
          rw [slash]
          decide }))
  · rfl
  · rfl
  · simp only [caml_mainX5054TSeg, evalBlocks, evalBlock, SegEvalState.init, camlattemptdash_line_80005054,
      camlattemptdash_line_80005058, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show 0#64 + Functions.sign_extend (m := 64) 45#12 = 45#64 by decide, slash]
  · rfl
  · decide

theorem print_config_auipc : 2147504380#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 395159#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2224#12 = BitVec.ofNat 64 Layout.sym_print_config := by decide

/-- `print_config` is clear. -/
theorem caml_retry_config (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (flags : read4 c.σ.mem Layout.sym_print_config = [0#8, 0#8, 0#8, 0#8]) (regs : GHolds c.σ [(10, 0#64)]) :
    FnSummary 0x800050fc#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x80005108#64 0#64 [(15, 0#64), (10, 0#64)]) := by
  have word : bytesVal .lw (read4 c.σ.mem Layout.sym_print_config) = 0#64 := by rw [flags]; decide
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX50fcFSeg 0x800050fc#64 [(10, 0#64)]
        [read4 c.σ.mem Layout.sym_print_config] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptConfig_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_print_config) 4 by constructor <;> decide).lw rfl
            (by simp only [camlattemptconfig_line_800050fc, camlattemptconfig_line_80005100, eaddrM, srcVal, lookupG,
                  runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact print_config_auipc) (read4_pins _ _)
        · change guardB bop.BNE (bytesVal .lw (read4 c.σ.mem Layout.sym_print_config)) 0#64 = false
          rw [word]
          decide }))
  · rfl
  · rfl
  · simp only [caml_mainX50fcFSeg, evalBlocks, evalBlock, SegEvalState.init, camlattemptconfig_line_800050fc,
      camlattemptconfig_line_80005100, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [word]
  · rfl
  · decide

/-- `argv[s4]` with `s4 = 1` is non-NULL. -/
theorem caml_retry_prog_test (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (image : EmbedImage c)
    (regs : GHolds c.σ [(20, 1#64), (9, argvPtr), (10, 0#64)]) :
    FnSummary 0x80005108#64 (fun d => d = c)
      (WriteRegistersPost [15, 14] [] c 0x80005118#64 0#64
        [(14, argv1Ptr), (15, argvPtr + 8#64), (20, 1#64), (9, argvPtr), (10, 0#64)]) := by
  have entry : bytesVal .ld (read8 c.σ.mem (argvPtr + 8#64).toNat) = argv1Ptr := by
    rw [read8_value]; exact argv1_entry image
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX5108FSeg 0x80005108#64 [(20, 1#64), (9, argvPtr), (10, 0#64)]
        [read8 c.σ.mem (argvPtr + 8#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [20, 9, 10]; decide
      shape := by change ChainOK _ [20, 9, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptProg_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact (show ReadWindow (argvPtr + 8#64) 8 by constructor <;> decide).ld rfl
            (by simp only [camlattemptprog_line_80005108, camlattemptprog_line_8000510c, camlattemptprog_line_80005110,
                  eaddrM, srcVal, lookupG, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
                  Nat.reduceEqDiff, List.headD_cons]
                decide) (read8_pins _ _)
        · change guardB bop.BEQ (bytesVal .ld (read8 c.σ.mem (argvPtr + 8#64).toNat)) 0#64 = false
          rw [entry]
          decide }))
  · rfl
  · rfl
  · simp only [caml_mainX5108FSeg, evalBlocks, evalBlock, SegEvalState.init, camlattemptprog_line_80005108,
      camlattemptprog_line_8000510c, camlattemptprog_line_80005110, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM,
      srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some,
      Nat.reduceEqDiff, ite_true, ite_false]
    rw [entry, show Sail.shift_bits_left (1#64) (Sail.BitVec.extractLsb (shamtOf
      { pc := 2147504392#64, word := 3807123#32, b0 := 147#8, b1 := 23#8, b2 := 58#8, b3 := 0#8,
        kind := MKind.slli, rd := 15, rs1 := 20, rs2 := 0, imm := 3#12 }) 5 0) = 8#64 by decide]
  · rfl
  · decide

/-- `exe_name = argv[1]` and the argv cursor are stored in caml_main's frame. -/
def camlRetryLog (sp : BitVec 64) : List WEntry :=
  [((sp + 32#64).toNat, 8, argv1Ptr), ((sp + 24#64).toNat, 8, argvPtr + 8#64)]

/-- `caml_attempt_open(&exe_name, &trail, 1)` on `argv[1]`. -/
theorem caml_retry_prog_call (c : Config) (ra sp : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, sp), (14, argv1Ptr), (15, argvPtr + 8#64)])
    (slot32 : WriteWindow (sp + 32#64) 8) (slot24 : WriteWindow (sp + 24#64) 8)
    (outside : ImageOutside (camlRetryLog sp)) :
    FnSummary 0x80005118#64 (fun d => d = c)
      (WriteRegistersPost ([11, 12, 10] ++ [1]) (camlRetryLog sp) c jal_8000512c_call.target (sp + 32#64)
        ((1, jal_8000512c_call.link) :: [(11, sp + 40#64), (12, 1#64), (10, sp + 32#64), (2, sp), (14, argv1Ptr),
          (15, argvPtr + 8#64)])) := by
  apply block_then_call c jal_8000512c_call_shape jal_8000512c_call_decode (fun _ h => jal_8000512c_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput camlAttemptProgSave 0x80005118#64
        [(2, sp), (14, argv1Ptr), (15, argvPtr + 8#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 14, 15]; decide
      shape := by change ChainOK _ [2, 14, 15] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptProg_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · exact slot32.sd rfl rfl
        · exact slot24.sd rfl rfl }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
