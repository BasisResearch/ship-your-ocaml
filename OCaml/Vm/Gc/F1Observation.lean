import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Primitives.ObservationContract

/-! The F1 runtime invariant reads memory only totally (`getD 0`), so every
allocation instance (`f1_allocFrame_core`, `f1_allocFrame_core'`,
`f1_allocation`) also gives the observation form that library summaries with
total post-call bytes consume. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Memories equal on every total byte keep `f1Runtime`. -/
theorem f1_totalMemory {c c' : Config}
    (same : ∀ a : Nat, (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) (ok : f1Runtime c) : f1Runtime c' :=
  f1_transfer (fun x n _ => Reloc.bytesT_congr fun j _ => by simp only [bytesT, same])
    (fun ⟨H, cap, chs, h⟩ => ⟨H, cap, chs, h.keep_windows (ws := []) (fun _ hw => by cases hw)
      (Reloc.bytesT_congr fun j _ => by simp only [bytesT, same]) fun a _ => same a⟩) ok

/-- **Allocation to observation**: a log whose exact effect keeps the F1
runtime invariant also keeps it under its total-byte view. -/
theorem f1_observation_of {c : Config} {log : List WEntry}
    (alloc : AllocationRuntime f1Runtime c log) :
    ObservationRuntime f1Runtime c (fun x => ((writeLog c.σ.mem log)[x]?).getD 0) := by
  intro after observed ok
  let mid : Config := { c with σ := { c.σ with mem := writeLog c.σ.mem log } }
  refine f1_totalMemory (c := mid) (fun a => ?_) (alloc mid rfl ok)
  have h : bytesT after.σ.mem a 1 = _ := observed a
  simp only [bytesT] at h
  change (0#0).append _ = _ at h
  rw [BitVec.append] at h
  simpa using h

end OCaml.Vm.Gc
