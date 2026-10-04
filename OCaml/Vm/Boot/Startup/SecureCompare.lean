import OCaml.Vm.Boot.Startup.SecureUserCompareRows
import OCaml.Vm.Boot.Startup.SecureGroupCompareRows
import OCaml.Vm.Boot.Startup.SecureEffectiveGroupCallInterface
import OCaml.Vm.Boot.Startup.SecureIdentityStage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def secureCompareEntry (group : Bool) : BitVec 64 := if group then 0x80025714#64 else 0x80025704#64
def secureCompareExit (group : Bool) : BitVec 64 := if group then 0x80025730#64 else 0x80025708#64
def secureCompareBlocks (group : Bool) : List BBlock := if group then caml_secure_getenvX5714TSeg else caml_secure_getenvX5704FSeg

def secureCompareRegs (stack name : BitVec 64) : GRegs := [(10, 0#64), (8, 0#64), (9, name), (2, stack)]

theorem secureCompare_input (group : Bool) {stack name ra c} (h : LeafInput ra c)
    (regs : GHolds c.σ (secureCompareRegs stack name)) :
    BlockInput (secureCompareBlocks group) (secureCompareEntry group) (secureCompareRegs stack name) [] c where
  good := h.good
  minstret := h.minstret
  regs := regs
  keys := by change KeysOK [10, 8, 9, 2]; decide
  shape := by change ChainOK _ [10, 8, 9, 2] _; cases group <;> decide
  tick := h.tick
  facts := by
    have code := secureGetenv_code h.image
    cases group <;> chain_facts code with "Vsa.Sim.Code.caml_secure_getenv_at_"
    all_goals change guardB _ 0#64 0#64 = _
    all_goals decide

/-- Equal real/effective identities select the ordinary getenv path. -/
theorem secure_compare (group : Bool) (c : Config) (stack name ra : BitVec 64) (h : LeafInput ra c)
    (regs : GHolds c.σ (secureCompareRegs stack name)) :
    FnSummary (secureCompareEntry group) (fun d => d = c)
      (WriteRegistersPost [] [] c (secureCompareExit group) 0#64 (secureCompareRegs stack name)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (secureCompare_input group h regs))
  · cases group <;> rfl
  · cases group <;> rfl
  · cases group <;> rfl
  · rfl
  · cases group <;> decide

/-- The successful user-ID comparison is followed by the effective-group query. -/
theorem secure_effective_group (c : Config) (stack name ra : BitVec 64) (h : LeafInput ra c)
    (regs : GHolds c.σ (secureCompareRegs stack name)) :
    FnSummary (secureCompareEntry false) (fun d => d = c)
      (WriteRegistersPost [1, 10] [] c jal_80025708_call.link 0#64
        [(10, 0#64), (1, jal_80025708_call.link), (9, name), (2, stack), (8, 0#64)]) := by
  apply summary_bind (secure_compare false c stack name ra h regs) (fun _ post => post.pc)
  intro mid prepared
  have leaf : LeafInput ra mid :=
    ⟨prepared.good, prepared.image, prepared.minstret,
      (prepared.frame .x1 (by decide) (by decide)).trans h.raReg, h.aligned, prepared.tick⟩
  have holds : GHolds mid.σ [(10, 0#64), (9, name), (2, stack), (8, 0#64)] :=
    holds_project prepared.regs (by simp [secureCompareRegs, lookupG])
  have call := identity_call .effectiveGroup jal_80025708_call jal_80025708_call_shape jal_80025708_call_decode
    rfl mid ra 0#64 leaf (jal_80025708_call_pins prepared.image) [(9, name), (2, stack), (8, 0#64)] holds
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by simp only [keysG]; decide) (by simp only [keysG]; decide) (by decide)
  apply call.weaken (fun _ eq => eq)
  intro after returned
  exact prefix_readonly_post prepared returned
end OCaml.Vm.Boot.Startup
