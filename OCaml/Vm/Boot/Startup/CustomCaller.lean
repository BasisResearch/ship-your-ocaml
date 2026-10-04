import OCaml.Vm.Boot.Startup.CustomNodes
import OCaml.Vm.Boot.Startup.CallerFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst OCaml.Vm.Primitives

theorem CustomRegistered.caller_frame {H capacity kind sp s0 head before after}
    (w : CustomRegistered H capacity kind sp s0 head before after) (frame : NativeFrame sp 544) :
    CallerFrame sp before after := by
  apply (w.allocation.caller_frame frame).trans
  constructor
  intro a caller
  rw [w.publication.memory]
  apply congrArg (fun (value : Option (BitVec 8)) => value.getD 0)
  apply writeLog_out
  have high := w.region.upper
  have stack := frame.lower
  have table : Layout.sym_custom_ops_table + 8 ≤ heapEnd := by decide
  have payload : (vsaReg w.allocated 10).toNat + 16 ≤ a := by omega
  have global : Layout.sym_custom_ops_table + 8 ≤ a :=
    Nat.le_trans table (Nat.le_trans (Nat.le_add_right heapEnd 544) (Nat.le_trans stack caller))
  exact customPublish_out_byte w.region (Or.inr payload) (Or.inr global)

theorem CustomNextRegistered.caller_frame {H capacity kind sp head before after}
    (w : CustomNextRegistered H capacity kind sp head before after) (frame : NativeFrame sp 544) :
    CallerFrame sp before after :=
  (CallerFrame.of_memory w.setup.memory).trans (w.registration.caller_frame frame)

theorem CustomNodes.caller_frame {H capacity sp ra s0 head before after}
    (w : CustomNodes H capacity sp ra s0 head before after) (frame : NativeFrame sp 560) :
    CallerFrame (nativeStack sp 16) w.int32.saved after := by
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  exact (CallerFrame.of_memory w.int32.call.memory).trans
    ((w.int32.registration.caller_frame nested).trans
      ((w.nativeint.caller_frame nested).trans
        ((w.int64.caller_frame nested).trans (w.bigarray.caller_frame nested))))

/-- Read either original caller word after all four allocator calls and publications. -/
theorem CustomNodes.saved_word {H capacity sp ra s0 head before after off value}
    (w : CustomNodes H capacity sp ra s0 head before after) (frame : NativeFrame sp 560)
    (member : (off, value) ∈ [(8, ra), (0, s0)]) :
    bytesT after.σ.mem (nativeFrameBase sp 16 + off) 8 = value := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  rw [word_observed (m := w.int32.saved.σ.mem) (nativeFrameBase sp 16 + off)
    (fun i hi => (w.caller_frame frame).byte _ (by rw [short.stack_nat]; omega)), w.int32.setup.memory]
  apply short.word_log_read (slots := [(8, ra), (0, s0)])
  · intro k v hk
    have choices : (k, v) = (8, ra) ∨ (k, v) = (0, s0) := by simpa using hk
    rcases choices with eq | eq <;> cases eq <;> decide
  · simp
  · exact member
end OCaml.Vm.Boot.Startup
