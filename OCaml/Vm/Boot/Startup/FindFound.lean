import OCaml.Vm.Boot.Startup.FindFoundNormalized
import OCaml.Vm.Boot.Startup.FindFoundCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findFoundInput (sp env reent pointer offset : BitVec 64) : GRegs :=
  [(19, BitVec.ofNat 64 Layout.sym_environ), (21, reent), (15, pointer), (9, env),
   (22, offset), (2, nativeStack sp 80)]
def findFoundLog (sp pointer offset : BitVec 64) : List WEntry :=
  [((nativeStack sp 80 + 8#64).toNat, 8, pointer), (offset.toNat, 4, 0#64)]
def findFoundRegs (sp env reent pointer offset : BitVec 64) : GRegs :=
  [(9, 0#64), (10, reent), (14, env), (19, BitVec.ofNat 64 Layout.sym_environ),
   (21, reent), (15, pointer), (22, offset), (2, nativeStack sp 80)]

local macro "find_found_nf" : tactic =>
  `(tactic| simp only [findfound_line_80037520, findfound_line_80037524, findfound_line_80037528,
    findfound_line_8003752c, findfound_line_80037530, findfound_line_80037534,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findFoundInput, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findFound_input {sp env reent pointer offset ra c} (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findFoundInput sp env reent pointer offset))
    (environment : bytesT c.σ.mem Layout.sym_environ 8 = env) (slot : WriteWindow offset 4) :
    BlockInput findenv_rX7520Seg 0x80037520#64 (findFoundInput sp env reent pointer offset)
      [read8 c.σ.mem Layout.sym_environ] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [19, 21, 15, 9, 22, 2]; decide
  shape := by change ChainOK _ [19, 21, 15, 9, 22, 2] _; decide
  tick := leaf.tick
  facts := by
    have code := findFound_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_environ) 8 from by constructor <;> decide).ld rfl rfl (read8_pins _ _)
    · have saved : WriteWindow (nativeStack sp 80 + 8#64) 8 := by
        rw [nativeStack, frame.address 8 (by decide)]
        exact frame.word (by decide) (by decide)
      exact saved.sd rfl rfl
    · change MemFacts _ _ _ _
      simp only [MemFacts]
      find_found_nf
      change 0x80000000 ≤ (offset + 0#64).toNat ∧ (offset + 0#64).toNat + 4 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ (offset + 0#64).toNat ∧ (offset + 0#64).toNat % 4 = 0
      rw [BitVec.add_zero]
      exact ⟨slot.lower, slot.upper, by simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using slot.htif, slot.aligned⟩

/-- Matching the first environment entry records index zero in the caller's
output slot and saves the value delimiter before the unlock call. The caller
supplies the output-slot window and the combined log's image separation. -/
theorem find_found (c : Config) (sp env reent pointer offset ra : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findFoundInput sp env reent pointer offset))
    (environment : bytesT c.σ.mem Layout.sym_environ 8 = env) (slot : WriteWindow offset 4)
    (outside : ImageOutside (findFoundLog sp pointer offset)) :
    FnSummary 0x80037520#64 (fun d => d = c)
      (WriteRegistersPost [14, 10, 9] (findFoundLog sp pointer offset) c jal_80037538_call.pc reent
        (findFoundRegs sp env reent pointer offset)) := by
  apply registers_of_blocks leaf.image outside
    (block_summary _ _ _ _ _ (findFound_input leaf frame regs environment slot))
  · simp only [findenv_rX7520Seg, evalBlocks, evalBlock, SegEvalState.init]
    find_found_nf
    rw [read8_value, environment, BitVec.sub_self]
    change [((nativeStack sp 80 + 8#64).toNat, 8, pointer), ((offset + 0#64).toNat, 4, 0#64)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · simp only [findenv_rX7520Seg, evalBlocks, evalBlock, SegEvalState.init]
    find_found_nf
    rw [read8_value, environment, BitVec.sub_self]
    change [(9, 0#64), (10, reent + 0#64), (14, env), (19, BitVec.ofNat 64 Layout.sym_environ),
      (21, reent), (15, pointer), (22, offset), (2, nativeStack sp 80)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
