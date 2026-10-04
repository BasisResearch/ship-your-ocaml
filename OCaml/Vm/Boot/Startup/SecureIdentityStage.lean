import OCaml.Vm.Boot.Startup.SecureUserCallInterface
import OCaml.Vm.Boot.Startup.SecureUserRows
import OCaml.Vm.Boot.Startup.SecureGroupCallInterface
import OCaml.Vm.Boot.Startup.SecureGroupRows
import OCaml.Vm.Boot.Startup.SecureGetenvPrefix
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def secureStageCall (group : Bool) : CallInstr := if group then jal_80025710_call else jal_80025700_call
def secureStageKind (group : Bool) : IdentityKind := if group then .group else .user
def secureStageEntry (group : Bool) : BitVec 64 := if group then 0x8002570c#64 else 0x800256fc#64
def secureStageBlocks (group : Bool) : List BBlock := if group then caml_secure_getenvX570cSeg else caml_secure_getenvX56fcSeg

def secureStageInput (stack name : BitVec 64) : GRegs := [(10, 0#64), (9, name), (2, stack)]
def secureStageRegs (stack name : BitVec 64) : GRegs := (8, 0#64) :: secureStageInput stack name

theorem secureStage_input (group : Bool) {stack name ra c} (h : LeafInput ra c)
    (regs : GHolds c.σ (secureStageInput stack name)) :
    BlockInput (secureStageBlocks group) (secureStageEntry group) (secureStageInput stack name) [] c where
  good := h.good
  minstret := h.minstret
  regs := regs
  keys := by change KeysOK [10, 9, 2]; decide
  shape := by change ChainOK _ [10, 9, 2] _; cases group <;> decide
  tick := h.tick
  facts := by
    have code := secureGetenv_code h.image
    cases group <;> chain_facts code with "Vsa.Sim.Code.caml_secure_getenv_at_"

theorem secure_stage_prefix (group : Bool) (c : Config) (stack name ra : BitVec 64) (h : LeafInput ra c)
    (regs : GHolds c.σ (secureStageInput stack name)) :
    FnSummary (secureStageEntry group) (fun d => d = c)
      (WriteRegistersPost [8] [] c (secureStageCall group).pc 0#64 (secureStageRegs stack name)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (secureStage_input group h regs))
  · cases group <;> rfl
  · cases group <;> rfl
  · cases group <;> rfl
  · rfl
  · cases group <;> decide

theorem secureStage_shape (group : Bool) : CallShape (secureStageCall group) := by
  cases group
  · exact jal_80025700_call_shape
  · exact jal_80025710_call_shape

theorem secureStage_decode (group : Bool) : CallDecode (secureStageCall group) := by
  cases group
  · exact jal_80025700_call_decode
  · exact jal_80025710_call_decode

theorem secureStage_pins (group : Bool) {c : Config} (image : ExecutableImage c) : CallPins (secureStageCall group) c := by
  cases group
  · exact jal_80025700_call_pins image
  · exact jal_80025710_call_pins image

/-- The user and group comparisons share the same move-and-query stage. -/
theorem secure_identity_stage (group : Bool) (c : Config) (stack name ra : BitVec 64) (h : LeafInput ra c)
    (regs : GHolds c.σ (secureStageInput stack name)) :
    FnSummary (secureStageEntry group) (fun d => d = c)
      (WriteRegistersPost [8, 1, 10] [] c (secureStageCall group).link 0#64
        [(10, 0#64), (1, (secureStageCall group).link), (9, name), (2, stack), (8, 0#64)]) := by
  apply summary_bind (secure_stage_prefix group c stack name ra h regs) (fun _ post => post.pc)
  intro mid prepared
  have leaf : LeafInput ra mid :=
    ⟨prepared.good, prepared.image, prepared.minstret,
      (prepared.frame .x1 (by decide) (by decide)).trans h.raReg, h.aligned, prepared.tick⟩
  have holds : GHolds mid.σ [(10, 0#64), (9, name), (2, stack), (8, 0#64)] :=
    holds_project prepared.regs (by simp [secureStageRegs, secureStageInput, lookupG])
  have call := identity_call (secureStageKind group) (secureStageCall group) (secureStage_shape group) (secureStage_decode group)
    (by cases group <;> rfl) mid ra 0#64 leaf (secureStage_pins group prepared.image) [(9, name), (2, stack), (8, 0#64)] holds
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by simp only [keysG]; decide) (by simp only [keysG]; decide) (by cases group <;> decide)
  apply call.weaken (fun _ eq => eq)
  intro after returned
  exact prefix_readonly_post prepared returned
end OCaml.Vm.Boot.Startup
