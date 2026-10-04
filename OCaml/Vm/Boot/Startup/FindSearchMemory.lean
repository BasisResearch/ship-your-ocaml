import OCaml.Vm.Boot.Startup.FindMatched
import OCaml.Vm.Boot.Startup.FindSaved
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def findSearchSlots (ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List (Nat × BitVec 64) :=
  [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra), (32, s4), (64, s0)]
def findSearchLog (sp ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  nativeWordLog sp 80 (findSearchSlots ra s0 s1 s2 s3 s4 s5 s6)

theorem findSearchLog_eq (sp ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) :
    findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6 =
      findLog sp ra s1 s2 s3 s4 s5 s6 ++ findCompareLog sp s0 := rfl

theorem findSearchSlots_bounds {ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64} {off value}
    (member : (off, value) ∈ findSearchSlots ra s0 s1 s2 s3 s4 s5 s6) : off + 8 ≤ 80 := by
  simp only [findSearchSlots, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h | h | h
  all_goals first | contradiction | (obtain ⟨rfl, _⟩ := h; decide)

theorem findSearchLog_inside {sp ra s0 s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6) :=
  frame.word_log_inside (fun _ _ member => findSearchSlots_bounds member)

/-- All eight saved registers follow from the complete search-prefix log. -/
theorem findSearch_saved {sp ra s0 s1 s2 s3 s4 s5 s6} {before after : Config} (frame : NativeFrame sp 80)
    (memory : after.σ.mem = writeLog before.σ.mem (findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6)) :
    FindReturnSaved sp ra s1 s2 s3 s5 s6 after ∧
      bytesT after.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4 ∧
      bytesT after.σ.mem (nativeFrameBase sp 80 + 64) 8 = s0 := by
  have read (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ findSearchSlots ra s0 s1 s2 s3 s4 s5 s6) :
      bytesT after.σ.mem (nativeFrameBase sp 80 + off) 8 = value := by
    rw [memory]
    exact frame.word_log_read (fun _ _ hm => findSearchSlots_bounds hm)
      (by simp [findSearchSlots, List.pairwise_cons]) before.σ.mem member
  exact ⟨⟨read 72 ra (by simp [findSearchSlots]), read 56 s1 (by simp [findSearchSlots]),
    read 48 s2 (by simp [findSearchSlots]), read 40 s3 (by simp [findSearchSlots]),
    read 24 s5 (by simp [findSearchSlots]), read 16 s6 (by simp [findSearchSlots])⟩,
    read 32 s4 (by simp [findSearchSlots]), read 64 s0 (by simp [findSearchSlots])⟩
end OCaml.Vm.Boot.Startup
