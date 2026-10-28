import OCaml.Vm.Boot.Startup.InterpreterFrameNormalized
import OCaml.Vm.Boot.Startup.InterpreterFrameImage
import OCaml.Vm.Boot.Startup.InterpreterInitNormalized
import OCaml.Vm.Boot.Startup.InterpreterInitImage
import OCaml.Vm.Boot.Startup.InterpreterSaveTailNormalized
import OCaml.Vm.Boot.Startup.InterpreterSaveTailImage
import OCaml.Vm.Boot.Startup.InterpreterUnitNormalized
import OCaml.Vm.Boot.Startup.InterpreterUnitImage
import OCaml.Vm.Boot.Startup.CamlInterpreterInitNormalized
import OCaml.Vm.Boot.Startup.CamlInterpreterInitCallInterface
import OCaml.Vm.Boot.Startup.CamlDebuggerInitCallInterface
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Boot.Startup.MainArgv
import OCaml.Vm.Sim.InterpReturn

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Actual register bank saved by the initialization call. -/
def interpreterInitBankAt (sp : BitVec 64) (saved : Nat → BitVec 64) : GRegs :=
  [(2,sp),(1,saved 1),(8,saved 8),(9,saved 9),(18,saved 18),(19,saved 19),(20,saved 20),
   (21,saved 21),(22,saved 22),(23,saved 23),(24,saved 24),(25,saved 25),(26,saved 26),(27,saved 27),(10,0)]

def interpreterInitBank (saved : Nat → BitVec 64) : GRegs := interpreterInitBankAt parameterStack saved

def interpreterInitSlots (saved : Nat → BitVec 64) : List (Nat × BitVec 64) :=
  Layout.interpSavedRegs.map fun r => (Layout.interpSaveOffset r, saved r)

def interpreterInitLog (saved : Nat → BitVec 64) : List WEntry :=
  nativeWordLog parameterStack Layout.interpFrameBytes (interpreterInitSlots saved)

def interpreterPrefixLog (saved : Nat → BitVec 64) : List WEntry :=
  nativeWordLog parameterStack Layout.interpFrameBytes ((interpreterInitSlots saved).take 6)

def interpreterTailLog (saved : Nat → BitVec 64) : List WEntry :=
  nativeWordLog parameterStack Layout.interpFrameBytes ((interpreterInitSlots saved).drop 6)

theorem interpreterInit_log_parts (saved : Nat → BitVec 64) :
    interpreterPrefixLog saved ++ interpreterTailLog saved = interpreterInitLog saved := by
  simp only [interpreterPrefixLog, interpreterTailLog, interpreterInitLog, nativeWordLog,
    ← List.map_append, List.take_append_drop]

theorem interpreterInit_frame : NativeFrame parameterStack Layout.interpFrameBytes := by
  constructor <;> decide

theorem interpreterInit_slots_bound (saved : Nat → BitVec 64) :
    ∀ off value, (off, value) ∈ interpreterInitSlots saved → off + 8 ≤ Layout.interpFrameBytes := by
  intro off value member
  simp only [interpreterInitSlots, Layout.interpSavedRegs, List.map, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, Layout.interpSaveOffset] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rcases h with ⟨rfl, _⟩ <;> decide

theorem interpreterInit_inside (saved : Nat → BitVec 64) :
    LogInW [⟨nativeFrameBase parameterStack Layout.interpFrameBytes, parameterStack.toNat⟩]
      (interpreterInitLog saved) :=
  interpreterInit_frame.word_log_inside (interpreterInit_slots_bound saved)

local macro "ini_nf" : tactic => `(tactic| simp only [
  interpreterframe_line_80001df8, interpreterinit_line_80001dfc,
  interpreterinit_line_80001e00, interpreterinit_line_80001e04, interpreterinit_line_80001e08,
  interpreterinit_line_80001e0c, interpreterinit_line_80001e10, interpretersavetail_line_80001e14,
  interpretersavetail_line_80001e18, interpretersavetail_line_80001e1c, interpretersavetail_line_80001e20,
  interpretersavetail_line_80001e24, interpretersavetail_line_80001e28, interpretersavetail_line_80001e2c,
  runGM, stepGM, eraseG, wvalM, srcVal, lookupG, eaddrM, imm20Of,
  ldsRunM, stepLdsM, List.headD_cons, List.tail_cons,
  Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff])

/-- Both interpreter arguments are zero at the actual JAL, with its real link. -/
theorem caml_interpreter_init_call (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) :
    FnSummary 0x80004e84#64 (fun d => d = c)
      (WriteRegistersPost ([11,10] ++ [1]) [] c jal_80004e8c_call.target 0
        [(1,jal_80004e8c_call.link),(10,0),(11,0)]) := by
  apply block_then_call c jal_80004e8c_call_shape jal_80004e8c_call_decode
    (fun _ h => jal_80004e8c_call_pins h) ?_ (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_mainX4e84Seg 0x80004e84#64 [] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := trivial
      keys := by change KeysOK []; decide
      shape := by change ChainOK _ [] _; decide
      facts := by
        have code := camlInterpreterInit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- Open the 528-byte native frame, before any memory stores. -/
theorem interpreter_open_frame (c : Config) (saved : Nat → BitVec 64) (leaf : LeafInput (saved 1) c)
    (regs : GHolds c.σ (interpreterInitBank saved)) :
    FnSummary 0x80001df8#64 (fun d => d = c)
      (WriteRegistersPost [2] [] c 0x80001dfc#64 0
        (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_interpreteX1df8Seg 0x80001df8#64
        (interpreterInitBank saved) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,1,8,9,18,19,20,21,22,23,24,25,26,27,10]; decide
      shape := by change ChainOK _ [2,1,8,9,18,19,20,21,22,23,24,25,26,27,10] _; decide
      facts := by
        have code := interpreterFrame_code leaf.image
        chain_facts code with "Vsa.Sim.Code.startup_interpreter_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- First bounded saving region: six stores on the already adjusted stack. -/
theorem interpreter_init_prefix_stores (c : Config) (saved : Nat → BitVec 64) (leaf : LeafInput (saved 1) c)
    (regs : GHolds c.σ (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved)) :
    FnSummary 0x80001dfc#64 (fun d => d = c)
      (WriteRegistersPost [] (interpreterPrefixLog saved) c 0x80001e14#64 0
        (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved)) := by
  have inside : LogInW [⟨nativeFrameBase parameterStack Layout.interpFrameBytes, parameterStack.toNat⟩]
      (interpreterPrefixLog saved) := interpreterInit_frame.word_log_inside fun off value hm =>
    interpreterInit_slots_bound saved off value (List.mem_of_mem_take hm)
  apply registers_of_blocks leaf.image (interpreterInit_frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_interpreteX1dfcSeg 0x80001dfc#64
        (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,1,8,9,18,19,20,21,22,23,24,25,26,27,10]; decide
      shape := by change ChainOK _ [2,1,8,9,18,19,20,21,22,23,24,25,26,27,10] _; decide
      facts := by
        have code := interpreterInit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.startup_interpreter_at_"
        all_goals simp only [interpreterInitBankAt]
        all_goals ini_nf
        all_goals apply WriteWindow.sd (show WriteWindow _ 8 by constructor <;> (ini_nf; decide)) rfl rfl }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- The frame adjustment and six-store region retain their complete register bank. -/
theorem interpreter_init_prefix (c : Config) (saved : Nat → BitVec 64) (leaf : LeafInput (saved 1) c)
    (regs : GHolds c.σ (interpreterInitBank saved)) :
    FnSummary 0x80001df8#64 (fun d => d = c)
      (WriteRegistersPost [2] (interpreterPrefixLog saved) c 0x80001e14#64 0
        (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved)) := by
  apply blocks_then c (interpreter_open_frame c saved leaf regs)
  intro d P
  exact interpreter_init_prefix_stores d saved
    ⟨P.good,P.image,P.minstret,gholds_lookup (n := 1) _ P.regs rfl,leaf.aligned,P.tick⟩ P.regs

/-- Second bounded saving region: save seven registers and take the NULL branch. -/
theorem interpreter_init_tail (c : Config) (saved : Nat → BitVec 64) (leaf : LeafInput (saved 1) c)
    (regs : GHolds c.σ (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved)) :
    FnSummary 0x80001e14#64 (fun d => d = c)
      (WriteRegistersPost [] (interpreterTailLog saved) c 0x80001e34#64 0
        [(2,nativeStack parameterStack Layout.interpFrameBytes),(10,0)]) := by
  have inside : LogInW [⟨nativeFrameBase parameterStack Layout.interpFrameBytes, parameterStack.toNat⟩]
      (interpreterTailLog saved) := interpreterInit_frame.word_log_inside fun off value hm =>
    interpreterInit_slots_bound saved off value (List.mem_of_mem_drop hm)
  apply registers_of_blocks' leaf.image (interpreterInit_frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_interpreteX1e14FSeg 0x80001e14#64
        (interpreterInitBankAt (nativeStack parameterStack Layout.interpFrameBytes) saved) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,1,8,9,18,19,20,21,22,23,24,25,26,27,10]; decide
      shape := by change ChainOK _ [2,1,8,9,18,19,20,21,22,23,24,25,26,27,10] _; decide
      facts := by
        have code := interpreterSaveTail_code leaf.image
        chain_facts code with "Vsa.Sim.Code.startup_interpreter_at_"
        all_goals simp only [interpreterInitBankAt]
        all_goals ini_nf
        all_goals first
          | exact (show guardB bop.BNE 0#64 0#64 = false by decide)
          | (apply WriteWindow.sd (show WriteWindow _ 8 by constructor <;> (ini_nf; decide)) rfl rfl) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_interpreteX1e14FSeg, interpreterInitBankAt, evalBlocks, evalBlock,
      SegEvalState.init] at pins
    exact ⟨gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- Compose the bounded saves into the exact thirteen-store prologue log. -/
theorem interpreter_init_save (c : Config) (saved : Nat → BitVec 64) (leaf : LeafInput (saved 1) c)
    (regs : GHolds c.σ (interpreterInitBank saved)) :
    FnSummary 0x80001df8#64 (fun d => d = c)
      (WriteRegistersPost [2] (interpreterInitLog saved) c 0x80001e34#64 0
        [(2,nativeStack parameterStack Layout.interpFrameBytes),(10,0)]) := by
  constructor
  rintro before ⟨pc,eq⟩
  subst before
  obtain ⟨mid,run1,P⟩ := (interpreter_init_prefix c saved leaf regs).run c ⟨pc,rfl⟩
  have midLeaf : LeafInput (saved 1) mid :=
    ⟨P.good,P.image,P.minstret,gholds_lookup (n := 1) _ P.regs rfl,leaf.aligned,P.tick⟩
  obtain ⟨after,run2,Q⟩ := (interpreter_init_tail mid saved midLeaf P.regs).run mid ⟨P.pc,rfl⟩
  have post := write_post_seq P Q
  rw [interpreterInit_log_parts] at post
  exact ⟨after,run1.trans run2,post⟩

/-- The NULL-program jump has no memory or register effects. -/
theorem interpreter_init_jump (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (arg : gprGet c.σ 10 = some 0) :
    FnSummary 0x80001e34#64 (fun d => d = c)
      (WriteRegistersPost [] [] c 0x800035e0#64 0 [(10,0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_interpreteX1e34Seg 0x80001e34#64 [(10,0)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := ⟨arg,trivial⟩
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      facts := by
        have code := interpreterInit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.startup_interpreter_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- The pinned ELF's entire initialization body sets tagged unit and enters the epilogue. -/
theorem interpreter_init_unit (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (arg : gprGet c.σ 10 = some 0) :
    FnSummary 0x800035e0#64 (fun d => d = c)
      (WriteRegistersPost [21] [] c 0x8000331c#64 0 [(21,1),(10,0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_interpreteX35e0Seg 0x800035e0#64 [(10,0)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := ⟨arg,trivial⟩
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      facts := by
        have code := interpreterUnit_code leaf.image
        chain_facts code with "Vsa.Sim.Code.startup_interpreter_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- Read the saved bank from the actual thirteen stores, independently of register clobbers. -/
theorem interpreter_init_saved {c after : Config} (saved : Nat → BitVec 64)
    (memory : after.σ.mem = writeLog c.σ.mem (interpreterInitLog saved)) :
    OCaml.Vm.Sim.InterpSavedFrame (nativeFrameBase parameterStack Layout.interpFrameBytes) saved after := by
  constructor
  · intro r hr
    have member : (Layout.interpSaveOffset r, saved r) ∈ interpreterInitSlots saved :=
      List.mem_map.mpr ⟨r,hr,rfl⟩
    unfold OCaml.Vm.word
    rw [memory]
    exact interpreterInit_frame.word_log_read (interpreterInit_slots_bound saved)
      ((List.pairwise_map (l := interpreterInitSlots saved) (f := Prod.fst)
        (R := fun a b => a + 8 ≤ b ∨ b + 8 ≤ a)).mp (by
          simp only [interpreterInitSlots, Layout.interpSavedRegs, List.map, Layout.interpSaveOffset]
          decide)) c.σ.mem member
  · intro r hr
    have bounds : ∀ r ∈ Layout.interpSavedRegs, Layout.interpSaveOffset r + 8 ≤ Layout.interpFrameBytes := by decide
    have bound := bounds r hr
    have low : 0x80000000 ≤ nativeFrameBase parameterStack Layout.interpFrameBytes := by decide
    have high : nativeFrameBase parameterStack Layout.interpFrameBytes + Layout.interpFrameBytes ≤ 0x100000000 := by decide
    have htif : Layout.sym_tohost + 8 ≤ nativeFrameBase parameterStack Layout.interpFrameBytes := by decide
    constructor <;> omega

end OCaml.Vm.Boot.Startup
