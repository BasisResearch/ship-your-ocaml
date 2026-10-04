import OCaml.Vm.Boot.Startup.CustomPublish0Normalized
import OCaml.Vm.Boot.Startup.CustomPublish1Normalized
import OCaml.Vm.Boot.Startup.CustomPublish2Normalized
import OCaml.Vm.Boot.Startup.CustomPublish3Normalized
import OCaml.Vm.Boot.Startup.CustomPublish0Image
import OCaml.Vm.Boot.Startup.MemsetGeometry
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives

/-- The four source custom-operation registrations share a two-word prepend. -/
inductive CustomKind where
  | int32 | nativeint | int64 | bigarray
  deriving DecidableEq

def CustomKind.ops : CustomKind → Nat
  | .int32 => Layout.sym_caml_int32_ops
  | .nativeint => Layout.sym_caml_nativeint_ops
  | .int64 => Layout.sym_caml_int64_ops
  | .bigarray => Layout.sym_caml_ba_ops

def CustomKind.entry : CustomKind → BitVec 64
  | .int32 => 0x80024a40#64
  | .nativeint => 0x80024a68#64
  | .int64 => 0x80024a88#64
  | .bigarray => 0x80024aa8#64

def CustomKind.exit : CustomKind → BitVec 64
  | .int32 => 0x80024a60#64
  | .nativeint => 0x80024a80#64
  | .int64 => 0x80024aa0#64
  | .bigarray => 0x80024ac0#64

def CustomKind.blocks : CustomKind → List BBlock
  | .int32 => customPublish0Save
  | .nativeint => customPublish1Save
  | .int64 => customPublish2Save
  | .bigarray => customPublish3Save

def customTable : BitVec 64 := BitVec.ofNat 64 Layout.sym_custom_ops_table

def customPublishInput (kind : CustomKind) (p : BitVec 64) : GRegs :=
  match kind with
  | .int32 => [(10, p)]
  | _ => [(8, customTable), (10, p)]
def customPublishLoads (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem Layout.sym_custom_ops_table]
def customPublishLog (kind : CustomKind) (p head : BitVec 64) : List WEntry :=
  [(p.toNat, 8, BitVec.ofNat 64 kind.ops), ((p + 8#64).toNat, 8, head),
    (Layout.sym_custom_ops_table, 8, p)]
def customPublishRegs (kind : CustomKind) (p head : BitVec 64) : GRegs :=
  [(14, BitVec.ofNat 64 kind.ops), (15, head), (8, customTable), (10, p)]

structure CustomPublishInput (kind : CustomKind) (p head ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  regs : GHolds c.σ (customPublishInput kind p)
  region : ZeroPairRegion p.toNat 1
  headWord : bytesT c.σ.mem Layout.sym_custom_ops_table 8 = head

local macro "custom_publish_nf" : tactic =>
  `(tactic| simp only [custompublish0_line_80024a40,
    custompublish0_line_80024a44,
    custompublish0_line_80024a48,
    custompublish0_line_80024a4c,
    custompublish0_line_80024a50,
    custompublish0_line_80024a54,
    custompublish0_line_80024a58,
    custompublish0_line_80024a5c,
    custompublish1_line_80024a68,
    custompublish1_line_80024a6c,
    custompublish1_line_80024a70,
    custompublish1_line_80024a74,
    custompublish1_line_80024a78,
    custompublish1_line_80024a7c,
    custompublish2_line_80024a88,
    custompublish2_line_80024a8c,
    custompublish2_line_80024a90,
    custompublish2_line_80024a94,
    custompublish2_line_80024a98,
    custompublish2_line_80024a9c,
    custompublish3_line_80024aa8,
    custompublish3_line_80024aac,
    custompublish3_line_80024ab0,
    custompublish3_line_80024ab4,
    custompublish3_line_80024ab8,
    custompublish3_line_80024abc,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    customPublishInput, customPublishLoads, wvalM, wentryM, widthOfM, imm20Of,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem customPublish_input (kind : CustomKind) {p head ra c} (h : CustomPublishInput kind p head ra c) :
    BlockInput kind.blocks kind.entry (customPublishInput kind p) (customPublishLoads c) c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by cases kind <;> simp only [customPublishInput, keysG] <;> decide
  shape := by cases kind <;> simp only [customPublishInput, keysG] <;> decide
  tick := h.tick
  facts := by
    have code := customPublish0_code h.image
    have first : WriteWindow p 8 := by
      simpa only [pairCursor, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        h.region.window0 (k := 0) (by decide)
    have second : WriteWindow (p + 8#64) 8 := by
      simpa only [pairCursor, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        h.region.window8 (k := 0) (by decide)
    have table : WriteWindow customTable 8 := by constructor <;> decide
    cases kind <;> chain_facts code with "Vsa.Sim.Code.caml_init_custom_operations_at_"
    all_goals try custom_publish_nf
    all_goals first
      | (apply table.read.ld rfl; rfl; exact read8_pins _ _)
      | (apply first.sd rfl; change p + 0#64 = p; exact BitVec.add_zero p)
      | exact second.sd rfl rfl
      | exact table.sd rfl rfl

theorem customPublish_second {p : BitVec 64} (region : ZeroPairRegion p.toNat 1) :
    (p + 8#64).toNat = p.toNat + 8 := by
  rw [BitVec.toNat_add]
  have upper := region.upper
  unfold heapEnd at upper
  simp only [BitVec.toNat_ofNat]
  omega

theorem customPublish_outside (kind : CustomKind) {p head : BitVec 64}
    (region : ZeroPairRegion p.toNat 1) : ImageOutside (customPublishLog kind p head) := by
  have lower := region.lower
  have geometry : Image.textBase + Image.textSize ≤ heapStart ∧
      Image.rodataBase + Image.rodataSize ≤ heapStart ∧
      Image.textBase + Image.textSize ≤ Layout.sym_custom_ops_table ∧
      Image.rodataBase + Image.rodataSize ≤ Layout.sym_custom_ops_table := by decide
  constructor <;> simp only [customPublishLog, OutLRange, customPublish_second region]
  all_goals exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), trivial⟩

/-- Any of the four registrations fills its fresh node and publishes it at the
same custom-operations head, with all three stores captured exactly. -/
theorem custom_publish (c : Config) (kind : CustomKind) (p head ra : BitVec 64)
    (h : CustomPublishInput kind p head ra c) :
    FnSummary kind.entry (fun d => d = c)
      (WriteRegistersPost [8, 15, 14] (customPublishLog kind p head) c kind.exit p
        (customPublishRegs kind p head)) := by
  apply registers_of_blocks h.image (customPublish_outside kind h.region)
    (block_summary _ _ _ _ _ (customPublish_input kind h))
  · cases kind <;> simp only [CustomKind.blocks, customPublish0Save,
      customPublish1Save, customPublish2Save,
      customPublish3Save, evalBlocks, evalBlock, SegEvalState.init]
    all_goals custom_publish_nf
    all_goals rw [read8_value, h.headWord]
    all_goals simp only [show Functions.sign_extend (m := 64) 0#12 = 0#64 from rfl, BitVec.add_zero]
    all_goals rfl
  · cases kind <;> rfl
  · cases kind <;> simp only [CustomKind.blocks, customPublish0Save,
      customPublish1Save, customPublish2Save,
      customPublish3Save, evalBlocks, evalBlock, SegEvalState.init]
    all_goals custom_publish_nf
    all_goals rw [read8_value, h.headWord]
    all_goals rfl
  · rfl
  · cases kind <;> decide

end OCaml.Vm.Boot.Startup
