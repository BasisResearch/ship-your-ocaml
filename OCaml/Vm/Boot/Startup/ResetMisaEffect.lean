import OCaml.Vm.Boot.Startup.ResetMisa
import Vsa.Sim.StateExt
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
theorem MisaResetPost.effect {s t : MState} (post : MisaResetPost s t) :
    t = { s with regs := s.regs.insert .misa initMisa } := by
  apply state_eq t { s with regs := s.regs.insert .misa initMisa } _ post.memory post.cycles post.output
  apply Std.ExtDHashMap.ext_get?
  intro r
  by_cases eq : r = .misa
  · subst r; simp [post.misa]
  · rw [post.frame r eq]
    simp [Std.ExtDHashMap.get?_insert, Ne.symm eq]
theorem reset_misa_effect (s : MState) (h : s.regs.get? .misa = some 0x8000000000000000#64) :
    (reset_misa ()).run s = .ok () { s with regs := s.regs.insert .misa initMisa } := by
  obtain ⟨t, ht⟩ := reset_misa_run s h
  rw [ht.run, ht.effect]
end OCaml.Vm.Boot.Startup
