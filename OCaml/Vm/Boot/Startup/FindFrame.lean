import OCaml.Vm.Boot.Startup.FindPrefix
import OCaml.Vm.Boot.Startup.FindReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The generated prologue's six disjoint stores supply all restoring loads. -/
theorem findPrefix_saved {sp ra s1 s2 s3 s5 s6} {before after : Config} (frame : NativeFrame sp 80)
    (memory : after.σ.mem = writeLog before.σ.mem (findPrefixLog sp ra s1 s2 s3 s5 s6)) :
    FindReturnSaved sp ra s1 s2 s3 s5 s6 after := by
  have read (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra)]) :
      bytesT after.σ.mem (nativeFrameBase sp 80 + off) 8 = value := by
    rw [memory]
    unfold findPrefixLog
    exact frame.word_log_read (fun _ _ hm => findPrefix_bounds hm)
      (by simp [List.pairwise_cons]) before.σ.mem member
  constructor
  · exact read 72 ra (by simp)
  · exact read 56 s1 (by simp)
  · exact read 48 s2 (by simp)
  · exact read 40 s3 (by simp)
  · exact read 24 s5 (by simp)
  · exact read 16 s6 (by simp)
end OCaml.Vm.Boot.Startup
