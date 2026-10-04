import OCaml.Vm.Gc.Generated.OldifyYoung
import OCaml.Vm.Gc.YoungAccess

namespace OCaml.Vm.Gc.OldifyYoung
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem upper_access {value domain c} (root : word c Layout.sym_Caml_state = domain)
    (windows : Young.Windows domain) :
    AccessPlan c.σ.mem (regs value) (Young.loads domain c) upperBlock.body := by
  have rootBytes : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = domain := by
    rw [read8_value]; exact root
  simp only [upperBlock, caml_oldify_oneX9accFSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  · apply Young.domain_window.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, regs, Young.loads, srcVal, lookupG,
      Functions.sign_extend, Sail.BitVec.signExtend]
  · apply windows.upper.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, regs, Young.loads, srcVal, lookupG, eraseG,
      stepGM, stepLdsM, wvalM, rootBytes, Layout.off_young_end,
      Functions.sign_extend, Sail.BitVec.signExtend]

theorem lower_access (value domain hi : BitVec 64) (c : Config)
    (windows : Young.Windows domain) :
    AccessPlan c.σ.mem (afterUpper value domain hi) (Young.loads domain c).tail.tail lowerBlock.body := by
  simp only [lowerBlock, caml_oldify_oneX9adcFSeg, List.getD_cons_zero, AccessPlan]
  chain_facts True.intro
  apply windows.lower.ld rfl ?_ (read8_pins _ _)
  simp [eaddrM, mkLine, decodeM, afterUpper, srcVal, lookupG,
    Layout.off_young_start, Functions.sign_extend, Sail.BitVec.signExtend]

theorem upper_control {value domain c} (bound : value.toNat < (Young.upperWord domain c).toNat) :
    TermFactsO (runGM upperBlock.body (regs value) (Young.loads domain c)) upperBlock.term := by
  rw [upper_regs]
  simp [upperBlock, caml_oldify_oneX9accFSeg, TermFactsO, TermFactsT, afterUpper,
    Young.loads, srcVal, lookupG, read8_value, guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
  exact bound

theorem lower_control {value domain hi c} (bound : (Young.lowerWord domain c).toNat < value.toNat) :
    TermFactsO (runGM lowerBlock.body (afterUpper value domain hi) (Young.loads domain c).tail.tail)
      lowerBlock.term := by
  rw [lower_regs]
  simp [lowerBlock, caml_oldify_oneX9adcFSeg, TermFactsO, TermFactsT, afterLower,
    Young.loads, srcVal, lookupG, read8_value, guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt]
  exact bound

structure ReadInput (value domain : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs value)
  root : word c Layout.sym_Caml_state = domain
  windows : Young.Windows domain

structure Input (value domain : BitVec 64) (c : Config) : Prop extends ReadInput value domain c where
  lower : (Young.lowerWord domain c).toNat < value.toNat
  upper : value.toNat < (Young.upperWord domain c).toNat

theorem access {value domain c} (input : Input value domain c) :
    ChainAccess c.σ.mem (regs value) (Young.loads domain c) blocks := by
  rw [blocks_eq]
  apply ChainAccess.cons ⟨upper_access input.root input.windows, upper_control input.upper⟩
  rw [upper_log, upper_regs, upper_loads]
  have rootBytes : bytesVal .ld ((Young.loads domain c).headD []) = domain := by
    change bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = _
    rw [read8_value]; exact input.root
  rw [rootBytes]
  exact ChainAccess.cons ⟨lower_access value domain _ c input.windows, lower_control input.lower⟩ ChainAccess.nil

structure Post (value domain : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs value) (Young.loads domain before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt exitPc after
  registers : GHolds after.σ (afterLower value (Young.lowerWord domain before) (Young.upperWord domain before))
  code : Code.Caml_oldify_oneLoaded after.σ.mem

theorem young_machine {value domain c} (input : Input value domain c) :
    FnSummary pc (fun d => d = c) (Post value domain c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs value) (Young.loads domain c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [18,8]; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, no_stores]; rfl
  refine ⟨post, memory, ?_, ?_, memory ▸ input.code⟩
  · rw [PCAt, post.pc, endpoint]
  · simpa only [OldifyYoung.registers, Young.loads, List.tail_cons, List.headD_cons,
      read8_value, Young.lowerWord, Young.upperWord, word] using post.regs

end OCaml.Vm.Gc.OldifyYoung
