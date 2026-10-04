import OCaml.Vm.Boot.Startup.SecureCompare
import OCaml.Vm.Boot.Startup.SecureGetenvTail
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The complete native secure-getenv wrapper reaches getenv with the original
name, caller link, stack and saved registers. Bare-metal identity checks always
succeed; no execution of getenv itself is assumed here. -/
theorem secure_getenv_to_getenv (c : Config) (sp name ra s0 s1 : BitVec 64)
    (h : LeafInput ra c) (regs : GHolds c.σ (secureInput sp name ra s0 s1)) (frame : NativeFrame sp 32) :
    FnSummary 0x800256e4#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10] (secureLog sp ra s0 s1) c 0x80037410#64 name (secureTailRegs sp name ra s0 s1)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨effectiveUser, run1, first⟩ :=
    (secure_getenv_first_identity c sp name ra s0 s1 (secure_getenv_input h regs frame)).run c ⟨pc, rfl⟩
  have firstLeaf := first.leaf (by rfl) (by decide : jal_800256f8_call.link.toNat % 4 = 0)
  obtain ⟨user, run2, second⟩ :=
    (secure_identity_stage false effectiveUser (secureStack sp) name _ firstLeaf
      (holds_project first.regs (by simp [secureStageInput, secureParked, lookupG]))).run effectiveUser ⟨first.pc, rfl⟩
  have secondLeaf := second.leaf (by rfl) (by decide : (secureStageCall false).link.toNat % 4 = 0)
  obtain ⟨effectiveGroup, run3, third⟩ :=
    (secure_effective_group user (secureStack sp) name _ secondLeaf
      (holds_project second.regs (by simp [secureCompareRegs, lookupG]))).run user ⟨second.pc, rfl⟩
  have thirdLeaf := third.leaf (by rfl) (by decide : jal_80025708_call.link.toNat % 4 = 0)
  obtain ⟨group, run4, fourth⟩ :=
    (secure_identity_stage true effectiveGroup (secureStack sp) name _ thirdLeaf
      (holds_project third.regs (by simp [secureStageInput, lookupG]))).run effectiveGroup ⟨third.pc, rfl⟩
  have fourthLeaf := fourth.leaf (by rfl) (by decide : (secureStageCall true).link.toNat % 4 = 0)
  obtain ⟨atTail, run5, fifth⟩ :=
    (secure_compare true group (secureStack sp) name _ fourthLeaf
      (holds_project fourth.regs (by simp [secureCompareRegs, lookupG]))).run group ⟨fourth.pc, rfl⟩
  have tailLeaf : LeafInput (secureStageCall true).link atTail :=
    ⟨fifth.good, fifth.image, fifth.minstret,
      (fifth.frame .x1 (by decide) (by decide)).trans fourthLeaf.raReg, fourthLeaf.aligned, fifth.tick⟩
  have saved := (secure_saved_after_prefix frame first.memory).transport
    (fifth.memory.trans (fourth.memory.trans (third.memory.trans second.memory)))
  obtain ⟨after, run6, tail⟩ :=
    (secure_getenv_tail atTail sp name ra s0 s1 _ tailLeaf frame
      (holds_project fifth.regs (by simp [secureTailInput, secureCompareRegs, lookupG])) saved).run atTail ⟨fifth.pc, rfl⟩
  have composed := prefix_readonly_post (prefix_readonly_post (prefix_readonly_post
    (prefix_readonly_post (prefix_readonly_post first second) third) fourth) fifth) tail
  exact ⟨after, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))),
    composed.toEffectPost.widen (by decide), tail.regs⟩
end OCaml.Vm.Boot.Startup
