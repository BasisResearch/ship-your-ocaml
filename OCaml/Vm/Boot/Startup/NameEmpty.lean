import Vsa.Sim.GRegsFrame
import OCaml.Vm.Boot.Startup.NameLoop
import OCaml.Vm.Boot.Startup.FindEmpty
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The native scan and empty-array test reach the restoring not-found path. -/
theorem name_scan_empty (c : Config) (p env ra value : BitVec 64) (cs : List Char)
    (data : EnvName p cs c) (positive : 0 < cs.length) (leaf : LeafInput ra c)
    (cursor : gprGet c.σ 12 = some p) (argument : gprGet c.σ 10 = some value)
    (environment : gprGet c.σ 9 = some env) (window : ReadWindow env 8)
    (empty : bytesT c.σ.mem env.toNat 8 = 0#64) :
    FnSummary 0x80037490#64 (fun d => d = c)
      (RegistersPost [14, 12, 15, 20, 10] c.σ.mem c 0x8003756c#64 0#64 (findEmptyRegs env ++ [(12, nameCursor p cs.length), (15, -61#64)])) := by
  apply summary_bind (name_scan c p ra value cs data positive leaf cursor argument) (fun _ post => post.pc)
  intro mid scanned
  have leaf' : LeafInput ra mid :=
    ⟨scanned.good, scanned.image, scanned.minstret,
      (scanned.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, scanned.tick⟩
  have regs : GHolds mid.σ (findEmptyInput env) :=
    ⟨(scanned.frame .x9 (by decide) (by decide)).trans environment,
      gholds_lookup _ scanned.regs (by rfl), trivial⟩
  have empty' : bytesT mid.σ.mem env.toNat 8 = 0#64 := by rw [scanned.memory]; exact empty
  apply (find_empty mid env ra leaf' regs window empty').weaken (fun _ eq => eq)
  intro after post
  refine ⟨?_, ?_⟩
  · have combined := scanned.toEffectPost.trans post.toEffectPost
    exact { combined with memory := post.memory.trans scanned.memory }
  · apply (gholds_append _ _).mpr
    exact ⟨post.regs,
      (post.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ scanned.regs (by rfl)),
      (post.frame .x15 (by decide) (by decide)).trans (gholds_lookup (n := 15) _ scanned.regs (by rfl)), trivial⟩
end OCaml.Vm.Boot.Startup
