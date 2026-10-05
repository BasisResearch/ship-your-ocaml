import OCaml.Vm.Boot.Startup.StatCheckedReturnNormalized
import OCaml.Vm.Boot.Startup.StatCheckedReturnImage
import OCaml.Vm.Boot.Startup.CustomReturnNormalized
import OCaml.Vm.Boot.Startup.ExtTableReturnNormalized
import OCaml.Vm.Boot.Startup.ExtTableReturnImage
import OCaml.Vm.Boot.Startup.CustomReturnImage
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Generated epilogues restoring the caller link and s0 from a native frame. -/
inductive NativePairKind where
  | checked | custom | extTable
  deriving DecidableEq

def NativePairKind.size : NativePairKind → Nat
  | .checked => 32
  | .custom | .extTable => 16

def NativePairKind.raOffset : NativePairKind → Nat
  | .checked => 24
  | .custom | .extTable => 8

def NativePairKind.s0Offset : NativePairKind → Nat
  | .checked => 16
  | .custom | .extTable => 0

def NativePairKind.entry : NativePairKind → BitVec 64
  | .checked => 0x8000bb78#64
  | .custom => 0x80024ac0#64
  | .extTable => 0x80003ddc#64

def NativePairKind.blocks : NativePairKind → List BBlock
  | .checked => caml_stat_allocXbb78Seg
  | .custom => caml_init_custom_operationsX4ac0Seg
  | .extTable => caml_ext_table_initX3ddcSeg

def nativePairInput (kind : NativePairKind) (sp p : BitVec 64) : GRegs :=
  [(2, nativeStack sp kind.size), (10, p)]
def nativePairLoads (kind : NativePairKind) (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp kind.size + kind.raOffset),
   read8 c.σ.mem (nativeFrameBase sp kind.size + kind.s0Offset)]
def nativePairRegs (sp ra s0 p : BitVec 64) : GRegs := [(2, sp), (8, s0), (1, ra), (10, p)]

structure NativePairInput (kind : NativePairKind) (sp ra s0 p oldra : BitVec 64) (c : Config) : Prop extends LeafInput oldra c where
  frame : NativeFrame sp kind.size
  regs : GHolds c.σ (nativePairInput kind sp p)
  savedRa : bytesT c.σ.mem (nativeFrameBase sp kind.size + kind.raOffset) 8 = ra
  savedS0 : bytesT c.σ.mem (nativeFrameBase sp kind.size + kind.s0Offset) 8 = s0
  returnAligned : ra.toNat % 4 = 0

local macro "native_pair_nf" : tactic =>
  `(tactic| simp only [statcheckedreturn_line_8000bb78, statcheckedreturn_line_8000bb7c,
    statcheckedreturn_line_8000bb80, customreturn_line_80024ac0, customreturn_line_80024ac4,
    customreturn_line_80024ac8, exttablereturn_line_80003ddc, exttablereturn_line_80003de0,
    exttablereturn_line_80003de4, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, nativePairInput, nativePairLoads,
    wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some,
    Nat.reduceEqDiff, ite_true, ite_false])

theorem nativePair_input {kind sp ra s0 p oldra c} (h : NativePairInput kind sp ra s0 p oldra c) :
    BlockInput kind.blocks kind.entry (nativePairInput kind sp p) (nativePairLoads kind sp c) c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by change KeysOK [2, 10]; decide
  shape := by cases kind <;> change ChainOK _ [2, 10] _ <;> decide
  tick := h.tick
  facts := by
    have first := h.frame.read_slot (off := kind.raOffset) (by cases kind <;> decide) (by cases kind <;> decide)
    have second := h.frame.read_slot (off := kind.s0Offset) (by cases kind <;> decide) (by cases kind <;> decide)
    have firstPins := h.frame.pins_slot c (off := kind.raOffset) (by cases kind <;> decide)
    have secondPins := h.frame.pins_slot c (off := kind.s0Offset) (by cases kind <;> decide)
    have checked := statCheckedReturn_code h.image
    have custom := customReturn_code h.image
    have extTable := extTableReturn_code h.image
    cases kind
    all_goals first
      | (guard_hyp h : NativePairInput .checked sp ra s0 p oldra c
         chain_facts checked with "Vsa.Sim.Code.caml_stat_alloc_at_")
      | (guard_hyp h : NativePairInput .custom sp ra s0 p oldra c
         chain_facts custom with "Vsa.Sim.Code.caml_init_custom_operations_at_")
      | chain_facts extTable with "Vsa.Sim.Code.caml_ext_table_init_at_"
    all_goals first
      | (change MemFacts _ _ _ ⟨_, _, _, _, _, _, .ld, 1, _, _, _⟩
         exact first.ld rfl rfl firstPins)
      | (change MemFacts _ _ _ ⟨_, _, _, _, _, _, .ld, 8, _, _, _⟩
         native_pair_nf
         exact second.ld rfl rfl secondPins)
      | (native_pair_nf; rw [read8_value, h.savedRa, ret_tgt ra h.returnAligned]; exact h.returnAligned)

/-- Shared native caller restoration over generated two-register epilogues. -/
theorem native_return_pair (c : Config) (kind : NativePairKind) (sp ra s0 p oldra : BitVec 64)
    (h : NativePairInput kind sp ra s0 p oldra c) :
    FnSummary kind.entry (fun d => d = c)
      (WriteRegistersPost [1, 8, 2] [] c ra p (nativePairRegs sp ra s0 p)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (nativePair_input h))
  · cases kind <;> rfl
  · cases kind
    all_goals change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem _) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    all_goals rw [read8_value, h.savedRa]
    all_goals exact ret_tgt ra h.returnAligned
  · cases kind
    all_goals change [(2, nativeStack sp _ + BitVec.ofNat 64 _),
      (8, bytesVal .ld (read8 c.σ.mem _)), (1, bytesVal .ld (read8 c.σ.mem _)), (10, p)] = _
    all_goals rw [read8_value, read8_value, h.savedRa, h.savedS0]
    all_goals simp only [statcheckedreturn_line_8000bb80, customreturn_line_80024ac8, exttablereturn_line_80003de4, NativePairKind.size, BitVec.toNat_ofNat, Nat.reduceMod]
    all_goals rw [nativeStack_restore]
    all_goals rfl
  · rfl
  · cases kind <;> decide
end OCaml.Vm.Boot.Startup
