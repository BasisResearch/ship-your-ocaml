import OCaml.Vm.Boot.Startup.CompareNames
import Vsa.Sim.FnSummary

/-! The primitive-name lookup consumes the existing full strcmp summary through
this named equality postcondition. Both aligned and unaligned paths are covered. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable

/-- Library framing excludes every register changed by instruction/tick bookkeeping. -/
theorem strcmp_frame_noise {r : Register} (hr : NotWrittenStrcmp r) :
    ∀ q ∈ noiseRegs, (q == r) = false := by
  intro q hq
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [NotWrittenStrcmp]

structure NameComparePost (g : (r : Register) → Option (RegisterType r))
    (link : BitVec 64) (sa sb : String) (memory : Vsa.MemRepr.Mem)
    (output : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  pc : PCAt link c
  ra : c.σ.regs.get? .x1 = some link
  mem : c.σ.mem = memory
  out : c.σ.sailOutput = output
  tick : c.tick < 2
  frame : ∀ r, NotWrittenStrcmp r → c.σ.regs.get? r = g r
  result : ∃ x : BitVec 64, c.σ.regs.get? .x10 = some x ∧ (x = 0 ↔ sa = sb)

/-- Destructure the library's legacy postcondition once at its consumer boundary. -/
theorem NameComparePost.of_strcmp {g link pa pb sa sb memory output c}
    (h : strcmp_post g link pa pb sa sb memory output c) :
    NameComparePost g link sa sb memory output c := by
  obtain ⟨good, pc, ra, mem, out, tick, frame, a, b, x, ha, hb, hsa, hsb, hx, sign⟩ := h
  refine ⟨good, pc, ra, mem, out, tick, frame, x, hx, ?_⟩
  rw [← strcmpSign_zero_iff, sign, strcmpSpecSign_zero_iff ha hb, hsa, hsb]
  exact String.ofList_inj.symm

/-- The landed full strcmp run, with the equality observation needed by lookup. -/
theorem compare_names (g : (r : Register) → Option (RegisterType r))
    (pa pb link : BitVec 64) (sa sb : String) (memory : Vsa.MemRepr.Mem)
    (output : Array String) :
    Triple (StrcmpEntryCond g pa pb link sa sb memory output)
      (NameComparePost g link sa sb memory output) := by
  intro c pre
  obtain ⟨after, steps, post⟩ := strcmp_full_spec_cond g pa pb link sa sb memory output c pre
  exact ⟨after, steps, NameComparePost.of_strcmp post⟩

end OCaml.Vm.Boot.Startup
