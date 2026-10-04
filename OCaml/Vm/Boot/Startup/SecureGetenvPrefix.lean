import OCaml.Vm.Boot.Startup.SecureGetenvNormalized
import OCaml.Vm.Boot.Startup.SecureGetenvCallInterface
import OCaml.Vm.Boot.Startup.IdentityCall
import OCaml.Vm.Primitives.AccessPlan
import OCaml.Vm.Primitives.Write
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def secureStack (sp : BitVec 64) : BitVec 64 := sp + (-32#64)
def secureInput (sp name ra s0 s1 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (9, s1), (1, ra), (10, name)]
def secureLog (sp ra s0 s1 : BitVec 64) : List WEntry :=
  [((secureStack sp + 16#64).toNat, 8, s0), ((secureStack sp + 8#64).toNat, 8, s1),
   ((secureStack sp + 24#64).toNat, 8, ra)]
def securePrefixRegs (sp name ra s0 : BitVec 64) : GRegs :=
  [(9, name), (2, secureStack sp), (8, s0), (1, ra), (10, name)]

structure SecureGetenvInput (sp name ra s0 s1 : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  registers : GHolds c.σ (secureInput sp name ra s0 s1)
  windows : ∀ off ∈ [16, 8, 24], WriteWindow (secureStack sp + BitVec.ofNat 64 off) 8
  outside : ImageOutside (secureLog sp ra s0 s1)

local macro "secure_prefix_nf" : tactic =>
  `(tactic| simp only [MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, secureInput, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

def secureBody : List MInstr := (secureGetenvSave.headD ⟨[], none⟩).body

theorem securePrefix_code {c : Config} (image : ExecutableImage c) : CodeFacts c.σ.mem secureBody := by
  have code := secureGetenv_code image
  simp only [secureBody, secureGetenvSave, List.headD_cons, CodeFacts]
  chain_facts code with "Vsa.Sim.Code.caml_secure_getenv_at_"

theorem securePrefix_access {sp name ra s0 s1 c} (h : SecureGetenvInput sp name ra s0 s1 c) :
    AccessPlan c.σ.mem (secureInput sp name ra s0 s1) [] secureBody := by
  simp only [secureBody, secureGetenvSave, List.headD_cons, AccessPlan]
  chain_facts True.intro
  all_goals secure_prefix_nf
  · exact ⟨(h.windows 16 (by simp)).lower, (h.windows 16 (by simp)).upper, (h.windows 16 (by simp)).htif, (h.windows 16 (by simp)).aligned⟩
  · exact ⟨(h.windows 8 (by simp)).lower, (h.windows 8 (by simp)).upper, (h.windows 8 (by simp)).htif, (h.windows 8 (by simp)).aligned⟩
  · exact ⟨(h.windows 24 (by simp)).lower, (h.windows 24 (by simp)).upper, (h.windows 24 (by simp)).htif, (h.windows 24 (by simp)).aligned⟩

theorem securePrefix_input {sp name ra s0 s1 c} (h : SecureGetenvInput sp name ra s0 s1 c) :
    BlockInput caml_secure_getenvX56e4Seg 0x800256e4#64 (secureInput sp name ra s0 s1) [] c where
  good := h.good
  minstret := h.minstret
  regs := h.registers
  keys := by change KeysOK [2, 8, 9, 1, 10]; decide
  shape := by change ChainOK _ [2, 8, 9, 1, 10] _; decide
  tick := h.tick
  facts := by
    rw [← secureGetenvSave_eq]
    exact singleton_chain_facts (accessPlan_facts (securePrefix_code h.image) (securePrefix_access h)) trivial trivial

/-- Save the secure-getenv caller frame and retain the requested variable name. -/
theorem secure_getenv_prefix (c : Config) (sp name ra s0 s1 : BitVec 64) (h : SecureGetenvInput sp name ra s0 s1 c) :
    FnSummary 0x800256e4#64 (fun d => d = c)
      (WriteRegistersPost [2, 9] (secureLog sp ra s0 s1) c jal_800256f8_call.pc name (securePrefixRegs sp name ra s0)) := by
  apply registers_of_blocks h.image h.outside (block_summary _ _ _ _ _ (securePrefix_input h))
  · rw [← secureGetenvSave_eq]
    simp only [secureGetenvSave, evalBlocks, evalBlock, SegEvalState.init]
    secure_prefix_nf
    rfl
  · rfl
  · rw [← secureGetenvSave_eq]
    simp only [secureGetenvSave, evalBlocks, evalBlock, SegEvalState.init]
    secure_prefix_nf
    change [(9, name + 0#64), (2, secureStack sp), (8, s0), (1, ra), (10, name)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def secureParked (sp name s0 : BitVec 64) : GRegs := [(9, name), (2, secureStack sp), (8, s0)]

/-- The complete saving prologue and first successful identity query. -/
theorem secure_getenv_first_identity (c : Config) (sp name ra s0 s1 : BitVec 64) (h : SecureGetenvInput sp name ra s0 s1 c) :
    FnSummary 0x800256e4#64 (fun d => d = c)
      (WriteRegistersPost [2, 9, 1, 10] (secureLog sp ra s0 s1) c jal_800256f8_call.link 0#64
        ((10, 0#64) :: (1, jal_800256f8_call.link) :: secureParked sp name s0)) := by
  apply summary_bind (secure_getenv_prefix c sp name ra s0 s1 h) (fun _ post => post.pc)
  intro mid prepared
  have leaf : LeafInput ra mid :=
    ⟨prepared.good, prepared.image, prepared.minstret,
      (prepared.frame .x1 (by decide) (by decide)).trans h.raReg, h.aligned, prepared.tick⟩
  have holds : GHolds mid.σ ((10, name) :: secureParked sp name s0) :=
    holds_project prepared.regs (by simp [secureParked, securePrefixRegs, lookupG])
  have call := identity_call .effectiveUser jal_800256f8_call jal_800256f8_call_shape jal_800256f8_call_decode
    rfl mid ra name leaf (jal_800256f8_call_pins prepared.image) (secureParked sp name s0) holds
    (by simp only [secureParked, keysG]; decide)
    (by simp only [KeysAvoidRa, secureParked, keysG]; decide)
    (by simp only [secureParked, keysG]; decide)
    (by simp only [secureParked, keysG]; decide) (by decide)
  apply call.weaken (fun _ eq => eq)
  intro after returned
  exact prefix_readonly_post prepared returned
end OCaml.Vm.Boot.Startup
