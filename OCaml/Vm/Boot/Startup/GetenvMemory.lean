import OCaml.Vm.Boot.Startup.GetenvCall
import OCaml.Vm.Boot.Startup.FindSaved
import OCaml.Vm.Boot.Startup.FrameWindows
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def getenvFullLog (sp ra s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  getenvLog sp ra ++ findLog (nativeStack sp 32) jal_80037428_call.link s1 s2 s3 s4 s5 s6

theorem getenvFullLog_inside {sp ra s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (getenvFullLog sp ra s1 s2 s3 s4 s5 s6) := by
  have outer := frame.resize (small := 32) (by decide) (by decide)
  have inner := frame.nested (front := 32) (size := 80) (by decide)
  have innerBase := frame.nested_base (front := 32) (size := 80) (by decide)
  apply log_in_append
  · apply log_in_larger_window (getenvLog_inside outer)
    · change nativeFrameBase sp 112 ≤ nativeFrameBase sp 32
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  · apply log_in_larger_window (findLog_inside inner)
    · change nativeFrameBase sp 112 ≤ nativeFrameBase (nativeStack sp 32) 80
      rw [innerBase]
      exact Nat.le_refl _
    · change (nativeStack sp 32).toNat ≤ sp.toNat
      rw [outer.stack_nat]
      unfold nativeFrameBase
      omega

/-- The nested search frame cannot overwrite getenv's saved caller link. -/
theorem getenv_saved {sp ra s1 s2 s3 s4 s5 s6} {before after : Config} (frame : NativeFrame sp 112)
    (memory : after.σ.mem = writeLog before.σ.mem (getenvFullLog sp ra s1 s2 s3 s4 s5 s6)) :
    bytesT after.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra := by
  have outer := frame.resize (small := 32) (by decide) (by decide)
  have inner := frame.nested (front := 32) (size := 80) (by decide)
  rw [memory, getenvFullLog, writeLog_append]
  rw [bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (findLog_inside inner) ?_)]
  · apply outer.word_log_read (slots := [(24, ra)])
    · intro off value member
      have eq : (off, value) = (24, ra) := List.mem_singleton.mp member
      cases eq
      decide
    · simp
    · simp
  · refine ⟨Or.inr ?_, trivial⟩
    change (nativeStack sp 32).toNat ≤ nativeFrameBase sp 32 + 24
    rw [outer.stack_nat]
    omega
end OCaml.Vm.Boot.Startup
