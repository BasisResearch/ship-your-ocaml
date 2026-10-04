import OCaml.Vm.Boot.Startup.CustomPublish
import OCaml.Vm.Boot.Startup.CustomRequest1Normalized
import OCaml.Vm.Boot.Startup.CustomRequest2Normalized
import OCaml.Vm.Boot.Startup.CustomRequest3Normalized
import OCaml.Vm.Boot.Startup.CustomRequest1CallInterface
import OCaml.Vm.Boot.Startup.CustomRequest2CallInterface
import OCaml.Vm.Boot.Startup.CustomRequest3CallInterface
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

inductive CustomLater where
  | nativeint | int64 | bigarray
  deriving DecidableEq

def CustomLater.kind : CustomLater → CustomKind
  | .nativeint => .nativeint
  | .int64 => .int64
  | .bigarray => .bigarray

def CustomLater.entry : CustomLater → BitVec 64
  | .nativeint => 0x80024a60#64
  | .int64 => 0x80024a80#64
  | .bigarray => 0x80024aa0#64

def CustomLater.blocks : CustomLater → List BBlock
  | .nativeint => customRequest1Save
  | .int64 => customRequest2Save
  | .bigarray => customRequest3Save

def CustomLater.call : CustomLater → CallInstr
  | .nativeint => jal_80024a64_call
  | .int64 => jal_80024a84_call
  | .bigarray => jal_80024aa4_call

theorem CustomLater.shape (kind : CustomLater) : CallShape kind.call := by
  cases kind
  · exact jal_80024a64_call_shape
  · exact jal_80024a84_call_shape
  · exact jal_80024aa4_call_shape

theorem CustomLater.decode (kind : CustomLater) : CallDecode kind.call := by
  cases kind
  · exact jal_80024a64_call_decode
  · exact jal_80024a84_call_decode
  · exact jal_80024aa4_call_decode

theorem CustomLater.pins (kind : CustomLater) {c : Config} (image : ExecutableImage c) : CallPins kind.call c := by
  cases kind
  · exact jal_80024a64_call_pins image
  · exact jal_80024a84_call_pins image
  · exact jal_80024aa4_call_pins image

def customParked (sp : BitVec 64) : GRegs := [(2, sp), (8, customTable)]
def customRequestRegs (sp : BitVec 64) : GRegs := (10, 16#64) :: customParked sp

theorem customRequest_input (kind : CustomLater) {sp ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (customParked sp)) :
    BlockInput kind.blocks kind.entry (customParked sp) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 8]; decide
  shape := by cases kind <;> change ChainOK _ [2, 8] _ <;> decide
  tick := leaf.tick
  facts := by
    have code := customRequest1_code leaf.image
    cases kind <;> chain_facts code with "Vsa.Sim.Code.caml_init_custom_operations_at_"

/-- All later registrations request the same node size through their actual JAL. -/
theorem custom_request (c : Config) (kind : CustomLater) (sp ra : BitVec 64)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (customParked sp)) :
    FnSummary kind.entry (fun d => d = c)
      (WriteRegistersPost [10, 1] [] c kind.call.target 16#64
        ((1, kind.call.link) :: customRequestRegs sp)) := by
  have front : FnSummary kind.entry (fun d => d = c)
      (WriteRegistersPost [10] [] c kind.call.pc 16#64 (customRequestRegs sp)) := by
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (customRequest_input kind leaf regs))
    · cases kind <;> rfl
    · cases kind <;> rfl
    · cases kind <;> rfl
    · rfl
    · cases kind <;> decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨saved, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary kind.shape kind.decode saved
    (kind.pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [10, 2, 8]; decide)
    (by simp only [KeysAvoidRa, customRequestRegs, customParked, keysG]; decide) (by rfl)).run saved ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
