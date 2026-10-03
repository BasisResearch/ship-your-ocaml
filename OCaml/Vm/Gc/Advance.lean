import OCaml.Vm.Gc.FieldCopyAccess

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives

def advanceLoads (target : BitVec 64) (c : Config) := [read8 c.σ.mem (target - 8#64).toNat]

def advanceAgain (target index : BitVec 64) (c : Config) : Bool :=
  guardB .BLTU (index + 1#64) (word c (target - 8#64).toNat >>> (10 : Nat))

theorem advance_access (slot delta target index : BitVec 64) (c : Config)
    (window : ReadWindow (target - 8#64) 8) :
    ChainAccess c.σ.mem (regs slot delta target index) (advanceLoads target c)
      (advanceBlocks (advanceAgain target index c)) := by
  refine ChainAccess.cons ⟨tail_access_bytes _ _ _ target _ rfl window (read8_pins _ _), ?_⟩ ChainAccess.nil
  apply (tail_control_iff _ _ _).mpr
  simp only [advanceLoads, List.headD_cons, read8_value, advanceAgain, word]
  rfl

/-- Mopup advance after either a copy store or a returned oldify call. The
header is read from the current memory; no synthetic previous store is used. -/
structure AdvanceInput (slot delta target index : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? LeanRV64DExecutable.Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (regs slot delta target index)
  header : ReadWindow (target - 8#64) 8

structure AdvancePost (slot delta target index : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (advanceBlocks (advanceAgain target index before)) advancePc
    (regs slot delta target index) (advanceLoads target before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (if advanceAgain target index before then pc else exitPc) after
  registers : GHolds after.σ (regs (slot + 8#64) delta target (index + 1#64))
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem advance_machine {slot delta target index c} (input : AdvanceInput slot delta target index c) :
    FnSummary advancePc (fun d => d = c) (AdvancePost slot delta target index c) := by
  have facts := chainPlan_facts (advance_code _ input.code)
    (advance_access slot delta target index c input.header)
  have summary := block_summary (advanceBlocks (advanceAgain target index c)) advancePc
    (regs slot delta target index) (advanceLoads target c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [8,18,19,9]; decide,
      facts, advance_ok _, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, advance_log]; rfl
  refine ⟨post, memory, ?_, advance_regs (segmentPost_of_block post), memory ▸ input.code⟩
  · rw [PCAt, post.pc, advance_pc]

end OCaml.Vm.Gc.FieldCopy
