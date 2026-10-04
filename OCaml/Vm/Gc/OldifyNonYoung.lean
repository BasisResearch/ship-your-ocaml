import OCaml.Vm.Gc.OldifyYoung
import OCaml.Vm.Gc.Generated.OldifyNonYoung

namespace OCaml.Vm.Gc.OldifyYoung
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def passesUpper (value domain : BitVec 64) (c : Config) : Bool :=
  decide (value.toNat < (Young.upperWord domain c).toNat)

theorem upper_reject_control {value domain c}
    (bound : (Young.upperWord domain c).toNat ≤ value.toNat) :
    TermFactsO (runGM upperReject.body (regs value) (Young.loads domain c)) upperReject.term := by
  rw [upperReject_body,upper_regs]
  simpa [upperReject,caml_oldify_oneX9accTSeg,TermFactsO,TermFactsT,afterUpper,
    Young.loads,Young.upperWord,Young.lowerWord,word,srcVal,lookupG,read8_value,guardB,Functions.zopz0zKzJ_u,Sail.BitVec.toNatInt] using bound

theorem lower_reject_control {value domain hi c}
    (bound : value.toNat ≤ (Young.lowerWord domain c).toNat) :
    TermFactsO (runGM lowerReject.body (afterUpper value domain hi) (Young.loads domain c).tail.tail)
      lowerReject.term := by
  rw [lowerReject_body,lower_regs]
  simpa [lowerReject,caml_oldify_oneX9adcTSeg,TermFactsO,TermFactsT,afterLower,
    Young.loads,Young.upperWord,Young.lowerWord,word,srcVal,lookupG,read8_value,guardB,Functions.zopz0zKzJ_u,Sail.BitVec.toNatInt] using bound

/-- An actual word outside the strict nursery interval selects one of the
rejection edges; all scalar accesses are shared with the accepted path. -/
theorem reject_access {value domain c} (input : ReadInput value domain c)
    (outside : ¬ ((Young.lowerWord domain c).toNat < value.toNat ∧ value.toNat < (Young.upperWord domain c).toNat)) :
    ChainAccess c.σ.mem (regs value) (Young.loads domain c) (rejectBlocks (passesUpper value domain c)) := by
  generalize selected : passesUpper value domain c = chosen
  cases chosen
  · have bound : (Young.upperWord domain c).toNat ≤ value.toNat := by
      have no : ¬ value.toNat < (Young.upperWord domain c).toNat := of_decide_eq_false selected
      omega
    apply ChainAccess.cons ⟨?_,upper_reject_control bound⟩ ChainAccess.nil
    rw [upperReject_body]
    exact upper_access input.root input.windows
  · have upper : value.toNat < (Young.upperWord domain c).toNat := of_decide_eq_true selected
    have lower : value.toNat ≤ (Young.lowerWord domain c).toNat := by omega
    apply ChainAccess.cons ⟨upper_access input.root input.windows,upper_control upper⟩
    rw [upper_log,upper_regs,upper_loads]
    have rootBytes : bytesVal .ld ((Young.loads domain c).headD []) = domain := by
      change bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = _
      rw [read8_value]
      exact input.root
    rw [rootBytes]
    apply ChainAccess.cons ⟨?_,lower_reject_control lower⟩ ChainAccess.nil
    rw [lowerReject_body]
    exact lower_access value domain _ c input.windows

structure Rejected (value domain : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (rejectBlocks (passesUpper value domain before)) pc (regs value)
    (Young.loads domain before) before after
  pc : PCAt rejectPc after
  value : gprGet after.σ 8 = some value
  memory : after.σ.mem = before.σ.mem
  code : Code.Caml_oldify_oneLoaded after.σ.mem

/-- Actual nursery classification of a non-young child reaches the native
store/return path, preserving its value and all untouched registers. -/
theorem nonYoung_machine {value domain c} (input : ReadInput value domain c)
    (outside : ¬ ((Young.lowerWord domain c).toNat < value.toNat ∧ value.toNat < (Young.upperWord domain c).toNat)) :
    FnSummary pc (fun d => d = c) (Rejected value domain c) := by
  have summary := block_summary (rejectBlocks (passesUpper value domain c)) pc (regs value)
    (Young.loads domain c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [18,8]; decide,
      chainPlan_facts (reject_code input.code _) (reject_access input outside),reject_chain_ok _,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory,reject_no_stores]; rfl
  have value : gprGet after.σ 8 = gprGet c.σ 8 :=
    post.frame_subset (reject_written _) Register.x8 (by decide) (by decide)
  refine ⟨post,?_,value.trans (gholds_lookup _ input.registers rfl),memory,memory ▸ input.code⟩
  rw [PCAt,post.pc,reject_endpoint]

end OCaml.Vm.Gc.OldifyYoung
