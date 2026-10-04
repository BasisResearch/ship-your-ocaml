import OCaml.Vm.Boot.Startup.FindLock
import OCaml.Vm.Boot.Startup.FindStartData
import OCaml.Vm.Primitives.MemoryFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def findLog (sp ra s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  nativeWordLog sp 80 [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra), (32, s4)]

theorem findLog_eq (sp ra s1 s2 s3 s4 s5 s6 : BitVec 64) :
    findLog sp ra s1 s2 s3 s4 s5 s6 = findPrefixLog sp ra s1 s2 s3 s5 s6 ++ findStartLog sp s4 := rfl

theorem findLog_bounds {ra s1 s2 s3 s4 s5 s6 : BitVec 64} {off value}
    (member : (off, value) ∈ [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra), (32, s4)]) :
    off + 8 ≤ 80 := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h | h
  all_goals first | contradiction | (obtain ⟨rfl, _⟩ := h; decide)

theorem findLog_inside {sp ra s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (findLog sp ra s1 s2 s3 s4 s5 s6) :=
  frame.word_log_inside (fun _ _ hm => findLog_bounds hm)

/-- Native frame stores preserve every total read lying below the frame. -/
theorem native_log_read_below {sp size log a n} (mem : Std.ExtHashMap Nat (BitVec 8))
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (below : a + n ≤ nativeFrameBase sp size) :
    bytesT (writeLog mem log) a n = bytesT mem a n :=
  bytesT_writeLog_out mem (OCaml.Vm.Sim.outLRange_of_windows inside ⟨Or.inl below, trivial⟩)

/-- All seven saved words are read back from the combined exact prologue log. -/
theorem find_saved {sp ra s1 s2 s3 s4 s5 s6} {before after : Config} (frame : NativeFrame sp 80)
    (memory : after.σ.mem = writeLog before.σ.mem (findLog sp ra s1 s2 s3 s4 s5 s6)) :
    FindReturnSaved sp ra s1 s2 s3 s5 s6 after ∧ bytesT after.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4 := by
  have read (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra), (32, s4)]) :
      bytesT after.σ.mem (nativeFrameBase sp 80 + off) 8 = value := by
    rw [memory]
    unfold findLog
    exact frame.word_log_read (fun _ _ hm => findLog_bounds hm)
      (by simp [List.pairwise_cons]) before.σ.mem member
  exact ⟨⟨read 72 ra (by simp), read 56 s1 (by simp), read 48 s2 (by simp),
    read 40 s3 (by simp), read 24 s5 (by simp), read 16 s6 (by simp)⟩, read 32 s4 (by simp)⟩
end OCaml.Vm.Boot.Startup
