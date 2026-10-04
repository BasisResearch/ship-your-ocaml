import OCaml.Vm.Boot.Startup.FindPresent
import OCaml.Vm.Boot.Startup.GetenvMemory
import OCaml.Vm.Boot.Startup.NativeWord32
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def getenvPresentLog (sp ra s0 s1 s2 s3 s4 s5 s6 pointer : BitVec 64) : List WEntry :=
  getenvLog sp ra ++ findPresentLog (nativeStack sp 32) jal_80037428_call.link s0 s1 s2 s3 s4 s5 s6 pointer (nativeStack sp 32 + 12#64)

/-- Both successful search stores lie inside getenv's combined native frame. -/
theorem getenv_found_below_caller {sp pointer} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, nativeFrameBase sp 32 + 16⟩]
      (findFoundLog (nativeStack sp 32) pointer (nativeStack sp 32 + 12#64)) := by
  have outer := frame.resize (small := 32) (by decide) (by decide)
  have inner := frame.nested (front := 32) (size := 80) (by decide)
  have innerBase := frame.nested_base (front := 32) (size := 80) (by decide)
  have pointerAddr : (nativeStack (nativeStack sp 32) 80 + 8#64).toNat = nativeFrameBase sp 112 + 8 := by
    rw [nativeStack, inner.address 8 (by decide), inner.slot_nat (by decide), innerBase]
  have offsetAddr : (nativeStack sp 32 + 12#64).toNat = nativeFrameBase sp 32 + 12 := by
    rw [nativeStack, outer.address 12 (by decide), outer.slot_nat (by decide)]
  unfold findFoundLog
  rw [pointerAddr, offsetAddr]
  change ((_ ≤ _ ∧ _ ≤ _) ∨ False) ∧ ((_ ≤ _ ∧ _ ≤ _) ∨ False) ∧ True
  have lower := frame.lower
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩
  all_goals dsimp only; unfold nativeFrameBase; omega

theorem getenv_found_inside {sp pointer} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩]
      (findFoundLog (nativeStack sp 32) pointer (nativeStack sp 32 + 12#64)) := by
  apply log_in_larger_window (getenv_found_below_caller frame)
  · exact Nat.le_refl _
  · change nativeFrameBase sp 32 + 16 ≤ sp.toNat
    have lower := frame.lower
    unfold nativeFrameBase
    omega

theorem getenv_search_below_caller {sp s0 s1 s2 s3 s4 s5 s6 pointer} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, nativeFrameBase sp 32 + 16⟩]
      (findPresentLog (nativeStack sp 32) jal_80037428_call.link s0 s1 s2 s3 s4 s5 s6 pointer (nativeStack sp 32 + 12#64)) := by
  apply log_in_append _ (getenv_found_below_caller frame)
  have inner := frame.nested (front := 32) (size := 80) (by decide)
  apply log_in_larger_window (findSearchLog_inside inner)
  · change nativeFrameBase sp 112 ≤ nativeFrameBase (nativeStack sp 32) 80
    rw [frame.nested_base (front := 32) (size := 80) (by decide)]
    exact Nat.le_refl _
  · change (nativeStack sp 32).toNat ≤ nativeFrameBase sp 32 + 16
    rw [(frame.resize (small := 32) (by decide) (by decide)).stack_nat]
    omega

/-- The whole successful native search fits in its caller's reserved 112 bytes. -/
theorem getenv_search_inside {sp s0 s1 s2 s3 s4 s5 s6 pointer} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩]
      (findPresentLog (nativeStack sp 32) jal_80037428_call.link s0 s1 s2 s3 s4 s5 s6 pointer (nativeStack sp 32 + 12#64)) := by
  apply log_in_append _ (getenv_found_inside frame)
  have inner := frame.nested (front := 32) (size := 80) (by decide)
  apply log_in_larger_window (findSearchLog_inside inner)
  · change nativeFrameBase sp 112 ≤ nativeFrameBase (nativeStack sp 32) 80
    rw [frame.nested_base (front := 32) (size := 80) (by decide)]
    exact Nat.le_refl _
  · change (nativeStack sp 32).toNat ≤ sp.toNat
    rw [(frame.resize (small := 32) (by decide) (by decide)).stack_nat]
    unfold nativeFrameBase
    omega

theorem getenvPresentLog_inside {sp ra s0 s1 s2 s3 s4 s5 s6 pointer} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (getenvPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 pointer) := by
  apply log_in_append _ (getenv_search_inside frame)
  apply log_in_larger_window (getenvLog_inside (frame.resize (small := 32) (by decide) (by decide)))
  · change nativeFrameBase sp 112 ≤ nativeFrameBase sp 32
    unfold nativeFrameBase
    omega
  · exact Nat.le_refl _
/-- The successful search, including its caller index store, cannot overwrite
getenv's saved return address in the upper part of the outer frame. -/
theorem getenv_present_saved {sp ra s0 s1 s2 s3 s4 s5 s6 pointer} {before after : Config}
    (frame : NativeFrame sp 112)
    (memory : after.σ.mem = writeLog before.σ.mem (getenvPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 pointer)) :
    bytesT after.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra := by
  rw [memory, getenvPresentLog, writeLog_append,
    bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows (getenv_search_below_caller frame) ?_)]
  · exact (frame.resize (small := 32) (by decide) (by decide)).word_log_read
      (slots := [(24, ra)]) (by intro off value member; cases List.mem_singleton.mp member; decide)
      (by simp) before.σ.mem (by simp)
  · exact ⟨Or.inr (by dsimp only; omega), trivial⟩

end OCaml.Vm.Boot.Startup
