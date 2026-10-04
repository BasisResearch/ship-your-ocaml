import OCaml.Vm.Boot.Startup.StartupAuxNormalized
import OCaml.Vm.Boot.Startup.StartupAuxImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Primitives.Word32Access
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def startupAuxBlocks : List BBlock := caml_startup_auxX4760FSeg ++ caml_startup_auxX4778FSeg ++
  caml_startup_auxX4794FSeg ++ caml_startup_auxX4798Seg ++ caml_startup_auxX479cSeg

def startupAuxInput (sp ra : BitVec 64) : GRegs := [(2, sp), (1, ra), (10, 0#64)]
def startupAuxSave (sp ra : BitVec 64) : List WEntry := nativeWordLog sp 16 [(8, ra)]
def startupAuxLog (sp ra : BitVec 64) : List WEntry :=
  startupAuxSave sp ra ++ [(Layout.sym_startup_count, 4, 1#64)]
def startupAuxLoads (c : Config) (sp ra : BitVec 64) : List (List (BitVec 8)) :=
  [List.replicate 4 0#8, List.replicate 4 0#8,
    read8 (writeLog c.σ.mem (startupAuxLog sp ra)) (nativeFrameBase sp 16 + 8)]
def startupAuxRegs (sp ra : BitVec 64) : GRegs :=
  [(2, sp), (10, 1#64), (1, ra), (13, 1#64), (12, BitVec.ofNat 64 Layout.sym_startup_count - 516#64), (15, 1#64), (14, 1#64)]

structure StartupAuxInput (sp ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 16
  regs : GHolds c.σ (startupAuxInput sp ra)
  shutdown : LPins4 c.σ.mem Layout.sym_shutdown_happened (List.replicate 4 0#8)
  count : LPins4 c.σ.mem Layout.sym_startup_count (List.replicate 4 0#8)

theorem startupAux_lw_zero : bytesVal .lw (List.replicate 4 0#8) = 0#64 := by rfl

local macro "startup_aux_nf" : tactic =>
  `(tactic| simp only [startupaux_line_80004760, startupaux_line_80004764,
    startupaux_line_80004768, startupaux_line_8000476c, startupaux_line_80004770,
    startupaux_line_80004778, startupaux_line_8000477c, startupaux_line_80004780,
    startupaux_line_80004784, startupaux_line_80004788, startupaux_line_8000478c,
    startupaux_line_80004798, startupaux_line_8000479c, startupaux_line_800047a0, startupaux_line_800047a4,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    startupAuxInput, startupAuxLoads, startupAux_lw_zero, wvalM, wentryM, widthOfM, imm20Of,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])
/-- The caller return word survives the separate startup counter store. -/
theorem startupAux_saved {sp ra} (frame : NativeFrame sp 16) (c : Config) :
    bytesT (writeLog c.σ.mem (startupAuxLog sp ra)) (nativeFrameBase sp 16 + 8) 8 = ra := by
  rw [startupAuxLog, writeLog_append, bytesT_writeLog_out _ (show OutLRange
    [(Layout.sym_startup_count, 4, 1#64)] (nativeFrameBase sp 16 + 8) 8 from ?_)]
  · apply frame.word_log_read (slots := [(8, ra)])
    · intro off value member
      have eq := List.mem_singleton.mp member
      cases eq
      decide
    · simp
    · simp
  · have lower := frame.lower
    have bound : Layout.sym_startup_count + 4 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
    exact ⟨Or.inr (by dsimp only; unfold nativeFrameBase; omega), trivial⟩

theorem startupAux_image_outside {sp ra} (frame : NativeFrame sp 16) : ImageOutside (startupAuxLog sp ra) := by
  have slot : (nativeStack sp 16 + 8#64).toNat = nativeFrameBase sp 16 + 8 := by
    rw [nativeStack, frame.address 8 (by decide), frame.slot_nat (off := 8) (by decide)]
  have lower := frame.lower
  have geometry : Image.textBase + Image.textSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.rodataBase + Image.rodataSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.textBase + Image.textSize ≤ Layout.sym_startup_count ∧
      Image.rodataBase + Image.rodataSize ≤ Layout.sym_startup_count := by decide
  constructor
  all_goals simp only [startupAuxLog, startupAuxSave, nativeWordLog, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, OutLRange, slot]
  all_goals exact ⟨Or.inl (by unfold nativeFrameBase; omega), Or.inl (by omega), trivial⟩

theorem startupAux_input {sp ra c} (h : StartupAuxInput sp ra c) :
    BlockInput startupAuxBlocks 0x80004760#64 (startupAuxInput sp ra) (startupAuxLoads c sp ra) c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by change KeysOK [2, 1, 10]; decide
  shape := by change ChainOK _ [2, 1, 10] _; decide
  tick := h.tick
  facts := by
    have code := startupAux_code h.image
    have saved := startupAux_saved (ra := ra) h.frame c
    chain_facts code with "Vsa.Sim.Code.caml_startup_aux_at_"
    · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_shutdown_happened) 4 from by constructor <;> decide).lw rfl rfl h.shutdown
    · have slot : WriteWindow (nativeStack sp 16 + 8#64) 8 := by
        rw [nativeStack, h.frame.address 8 (by decide)]
        exact h.frame.word (by decide) (by decide)
      exact slot.sd rfl rfl
    · startup_aux_nf
      rfl
    · apply (show ReadWindow (BitVec.ofNat 64 Layout.sym_startup_count) 4 from by constructor <;> decide).lw rfl rfl
      apply lpins4_writeLog h.count
      have lower := h.frame.lower
      have bound : Layout.sym_startup_count + 4 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
      change (Layout.sym_startup_count + 4 ≤ (nativeStack sp 16 + 8#64).toNat ∨ _) ∧ True
      rw [nativeStack, h.frame.address 8 (by decide), h.frame.slot_nat (off := 8) (by decide)]
      exact ⟨Or.inl (by unfold nativeFrameBase; omega), trivial⟩
    · exact (show WriteWindow (BitVec.ofNat 64 Layout.sym_startup_count) 4 from by constructor <;> decide).sw rfl rfl
    · startup_aux_nf
      rfl
    · startup_aux_nf
      rfl
    · startup_aux_nf
      simp only [show ∀ m, writeLog m [] = m from fun _ => rfl, ← writeLog_append]
      apply (h.frame.read_slot (off := 8) (by decide) (by decide)).ld rfl
      · startup_aux_nf
        rfl
      · rw [nativeStack, h.frame.address 8 (by decide), h.frame.slot_nat (off := 8) (by decide)]
        exact read8_pins _ _
    · startup_aux_nf
      rw [read8_value, saved, ret_tgt ra h.aligned]
      exact h.aligned

/-- First startup, with shutdown clear and pooling disabled, records one caller
and returns success along the complete native function path. -/
theorem startup_aux (c : Config) (sp ra : BitVec 64) (h : StartupAuxInput sp ra c) :
    FnSummary 0x80004760#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 10, 12, 13, 14, 15] (startupAuxLog sp ra) c ra 1#64 (startupAuxRegs sp ra)) := by
  apply registers_of_blocks h.image (startupAux_image_outside h.frame)
    (block_summary _ _ _ _ _ (startupAux_input h))
  · simp only [startupAuxBlocks, caml_startup_auxX4760FSeg, caml_startup_auxX4778FSeg,
      caml_startup_auxX4794FSeg, caml_startup_auxX4798Seg, caml_startup_auxX479cSeg,
      evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    startup_aux_nf
    rfl
  · change Sail.BitVec.update (bytesVal .ld
      (read8 (writeLog c.σ.mem (startupAuxLog sp ra)) (nativeFrameBase sp 16 + 8)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    rw [read8_value, startupAux_saved h.frame c, ret_tgt ra h.aligned]
  · simp only [startupAuxBlocks, caml_startup_auxX4760FSeg, caml_startup_auxX4778FSeg,
      caml_startup_auxX4794FSeg, caml_startup_auxX4798Seg, caml_startup_auxX479cSeg,
      evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    startup_aux_nf
    rw [read8_value, startupAux_saved h.frame c]
    change [(2, nativeStack sp 16 + 16#64), (10, 1#64), (1, ra), (13, 1#64),
      (12, BitVec.ofNat 64 Layout.sym_startup_count - 516#64), (15, 1#64), (14, 1#64)] = _
    rw [nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
