import OCaml.Vm.Boot.Startup.ParameterPresentQuery
import OCaml.Vm.Boot.Startup.ParameterPrefix
import OCaml.Vm.Boot.Startup.ParameterValueDone
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def parameterPresentQueryLog (sp entry s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  securePresentLog (nativeStack sp 64) (parameterCall false).link s0 s1 s2 s3 s4 s5 s6
    (nameCursor entry (parameterChars false).length)
def parameterPresentPrefixLog (sp entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  parameterLog sp ra s0 ++ parameterPresentQueryLog sp entry s0 s1 s2 s3 s4 s5 s6

def parameterPresentLog (sp entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  parameterPresentPrefixLog sp entry ra s0 s1 s2 s3 s4 s5 s6 ++ parameterValueLog sp s1 s2 s3

theorem parameterPresentPrefixLog_inside {sp entry ra s0 s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 176) :
    LogInW [⟨nativeFrameBase sp 176, sp.toNat⟩] (parameterPresentPrefixLog sp entry ra s0 s1 s2 s3 s4 s5 s6) := by
  apply log_in_append
  · apply log_in_larger_window (parameterLog_inside (frame.resize (small := 64) (by decide) (by decide)))
    · change nativeFrameBase sp 176 ≤ nativeFrameBase sp 64
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  · apply log_in_larger_window (securePresentLog_inside (frame.nested (front := 64) (size := 112) (by decide)))
    · change nativeFrameBase sp 176 ≤ nativeFrameBase (nativeStack sp 64) 112
      rw [frame.nested_base (front := 64) (size := 112) (by decide)]
      exact Nat.le_refl _
    · change (nativeStack sp 64).toNat ≤ sp.toNat
      rw [(frame.resize (small := 64) (by decide) (by decide)).stack_nat]
      unfold nativeFrameBase
      omega

theorem parameterPresentLog_inside {sp entry ra s0 s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 176) :
    LogInW [⟨nativeFrameBase sp 176, sp.toNat⟩] (parameterPresentLog sp entry ra s0 s1 s2 s3 s4 s5 s6) := by
  apply log_in_append (parameterPresentPrefixLog_inside frame)
  apply log_in_larger_window (parameterValueLog_inside (frame.resize (small := 64) (by decide) (by decide)))
  · change nativeFrameBase sp 176 ≤ nativeFrameBase sp 64
    unfold nativeFrameBase
    omega
  · exact Nat.le_refl _

/-- Successful lookup preserves both original parser caller slots. -/
theorem parameter_present_saved {sp entry ra s0 s1 s2 s3 s4 s5 s6} {before after : Config}
    (frame : NativeFrame sp 176)
    (memory : after.σ.mem = writeLog before.σ.mem (parameterPresentPrefixLog sp entry ra s0 s1 s2 s3 s4 s5 s6)) :
    bytesT after.σ.mem (nativeFrameBase sp 64 + 56) 8 = ra ∧
      bytesT after.σ.mem (nativeFrameBase sp 64 + 48) 8 = s0 := by
  have outer := frame.resize (small := 64) (by decide) (by decide)
  have read (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(56, ra), (48, s0)]) :
      bytesT after.σ.mem (nativeFrameBase sp 64 + off) 8 = value := by
    rw [memory, parameterPresentPrefixLog, writeLog_append, parameterPresentQueryLog]
    rw [bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows
      (securePresentLog_inside (frame.nested (front := 64) (size := 112) (by decide))) ?_)]
    · apply outer.word_log_read (slots := [(56, ra), (48, s0)])
      · intro i v hm
        have choices : (i, v) = (56, ra) ∨ (i, v) = (48, s0) := by simpa using hm
        rcases choices with eq | eq <;> cases eq <;> decide
      · simp [List.pairwise_cons]
      · exact member
    · refine ⟨Or.inr ?_, trivial⟩
      change (nativeStack sp 64).toNat ≤ nativeFrameBase sp 64 + off
      rw [outer.stack_nat]
      omega
  exact ⟨read 56 ra (by simp), read 48 s0 (by simp)⟩
end OCaml.Vm.Boot.Startup
