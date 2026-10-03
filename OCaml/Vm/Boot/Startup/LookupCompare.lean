import OCaml.Vm.Boot.Startup.CompareCall
import OCaml.Vm.Boot.Startup.LookupBlocks

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable

/-- The comparison and its branch preserve all strcmp-framed registers. -/
structure LookupCompared (g : (r : Register) → Option (RegisterType r))
    (sa sb : String) (memory : Vsa.MemRepr.Mem) (output : Array String)
    (c : Config) : Prop where
  ready : LookupReady c
  memory_eq : c.σ.mem = memory
  output_eq : c.σ.sailOutput = output
  pc : PCAt (if sa = sb then 0x80024e3c#64 else 0x80024e1c#64) c
  frame : ∀ r, NotWrittenStrcmp r → c.σ.regs.get? r = g r

/-- Compose the full library comparison with the actual lookup branch. -/
theorem lookup_compare (g : (r : Register) → Option (RegisterType r))
    (pa pb : BitVec 64) (sa sb : String) (memory : Vsa.MemRepr.Mem)
    (output : Array String) (code : Code.Caml_build_primitive_tableLoaded memory) :
    Triple (StrcmpEntryCond g pa pb 0x80024e38#64 sa sb memory output)
      (LookupCompared g sa sb memory output) := by
  intro c pre
  obtain ⟨mid, compareRun, post⟩ := compare_names g pa pb _ sa sb memory output c pre
  obtain ⟨x, hx, zero⟩ := post.result
  let taken := decide (sa ≠ sb)
  have branch : guardB .BNE x 0 = taken := by
    by_cases eq : sa = sb
    · have hx0 := zero.mpr eq
      simp [guardB, taken, eq, hx0]
    · have hx0 : x ≠ 0 := fun h => eq (zero.mp h)
      simp only [guardB, taken, eq, ne_eq, not_false_eq_true, decide_true]
      exact bne_iff_ne.mpr hx0
  have ready : LookupReady mid := ⟨post.good, by rw [post.mem]; exact code, post.tick⟩
  obtain ⟨after, branchRun, done⟩ := (lookup_branch mid x taken ready hx branch).run mid ⟨post.pc, rfl⟩
  refine ⟨after, compareRun.trans branchRun,
    ⟨done.ready, done.memory.trans post.mem, done.output.trans post.out, ?_, ?_⟩⟩
  · have pc := done.pc
    by_cases eq : sa = sb <;> simpa [taken, eq] using pc
  · intro r hr
    exact (done.frame r (strcmp_frame_noise hr)).trans (post.frame r hr)

end OCaml.Vm.Boot.Startup
