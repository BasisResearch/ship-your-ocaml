import OCaml.Vm.Boot.Startup.ParameterValue
import OCaml.Vm.Boot.Startup.ParameterValueReturn
import Vsa.Sim.GRegsFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Saved-word readback for the present-value parser path. -/
theorem parameterValue_saved {sp s1 s2 s3} {before after : Config} (frame : NativeFrame sp 64)
    (memory : after.σ.mem = writeLog before.σ.mem (parameterValueLog sp s1 s2 s3)) :
    bytesT after.σ.mem (nativeFrameBase sp 64 + 40) 8 = s1 ∧
    bytesT after.σ.mem (nativeFrameBase sp 64 + 32) 8 = s2 ∧
    bytesT after.σ.mem (nativeFrameBase sp 64 + 24) 8 = s3 := by
  have read (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(40, s1), (32, s2), (24, s3)]) :
      bytesT after.σ.mem (nativeFrameBase sp 64 + off) 8 = value := by
    rw [memory]
    apply frame.word_log_read (slots := [(40, s1), (32, s2), (24, s3)])
    · intro i v hm
      have choices : (i, v) = (40, s1) ∨ (i, v) = (32, s2) ∨ (i, v) = (24, s3) := by simpa using hm
      rcases choices with eq | eq | eq <;> cases eq <;> decide
    · simp [List.pairwise_cons]
    · exact member
  exact ⟨read 40 s1 (by simp), read 32 s2 (by simp), read 24 s3 (by simp)⟩

/-- The extra saves are below both original caller slots. -/
theorem parameterValue_original {sp s1 s2 s3} {before after : Config} (frame : NativeFrame sp 64)
    (memory : after.σ.mem = writeLog before.σ.mem (parameterValueLog sp s1 s2 s3))
    {off : Nat} (high : 48 ≤ off) :
    bytesT after.σ.mem (nativeFrameBase sp 64 + off) 8 = bytesT before.σ.mem (nativeFrameBase sp 64 + off) 8 := by
  rw [memory]
  apply bytesT_writeLog_out
  rw [parameterValueLog, frame.word_log_slots (by
    intro i v hm
    have choices : (i, v) = (40, s1) ∨ (i, v) = (32, s2) ∨ (i, v) = (24, s3) := by simpa using hm
    rcases choices with eq | eq | eq <;> cases eq <;> decide)]
  change ( _ ≤ _ ∨ _ ≤ _) ∧ (_ ≤ _ ∨ _ ≤ _) ∧ (_ ≤ _ ∨ _ ≤ _) ∧ True
  exact ⟨Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), trivial⟩

/-- Complete the parser after a successful query returning an empty string.
The caller slots are supplied by the earlier parser prefix and query frame. -/
theorem parameter_value_done (c : Config) (sp ra oldra s0 s1 s2 s3 value : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (parameterValueInput sp s1 s2 s3 value)) (nonnull : value ≠ 0#64)
    (window : ReadWindow value 1)
    (pin : ((writeLog c.σ.mem (parameterValueLog sp s1 s2 s3))[value.toNat]?).getD 0 = 0#8)
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 64 + 56) 8 = ra)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 64 + 48) 8 = s0) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80004534#64 (fun d => d = c)
      (WriteRegistersPost [8, 19, 18, 9, 15, 1, 2] (parameterValueLog sp s1 s2 s3) c ra value
        (parameterValueReturnRegs sp ra s0 s1 s2 s3 value ++ [(15, 0#64)])) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨middle, front, post⟩ := (parameter_value_empty c sp s1 s2 s3 value oldra leaf frame regs nonnull window pin).run c ⟨pc, rfl⟩
  obtain ⟨saved1, saved2, saved3⟩ := parameterValue_saved frame post.memory
  have caller := (parameterValue_original frame post.memory (off := 56) (by decide)).trans savedRa
  have original := (parameterValue_original frame post.memory (off := 48) (by decide)).trans saved0
  have midLeaf : LeafInput oldra middle := ⟨post.good, post.image, post.minstret,
    (post.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, post.tick⟩
  have midRegs : GHolds middle.σ (parameterValueReturnInput sp value) :=
    ⟨gholds_lookup (n := 2) _ post.regs (by rfl), post.result, trivial⟩
  have zero := gholds_lookup (n := 15) _ post.regs (show lookupG 15 (parameterValueRegs sp s1 s2 s3 value) = some 0#64 from rfl)
  obtain ⟨after, back, returned⟩ := (parameter_value_return middle sp ra s0 s1 s2 s3 value oldra midLeaf frame midRegs caller saved1 saved2 saved3 original aligned).run middle ⟨post.pc, rfl⟩
  have effects := (prefix_readonly_post post returned).toEffectPost.widen
    (writes' := [8, 19, 18, 9, 15, 1, 2]) (by decide)
  exact ⟨after, front.trans back, ⟨effects, (gholds_append _ _).mpr ⟨returned.regs,
    (returned.frame .x15 (by decide) (by decide)).trans zero, trivial⟩⟩⟩
end OCaml.Vm.Boot.Startup
