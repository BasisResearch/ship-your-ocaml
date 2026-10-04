import OCaml.Vm.Boot.Startup.TableTail
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def tableTailFinalRegs (base : Nat) (s0 s1 : BitVec 64) : GRegs :=
  [(8, s0), (9, s1), (2, firstMallocStack), (1, jal_8002a934_call.link), (11, 0#64)] ++ memset56Regs base

/-- Restore the table function's caller frame, execute its native tail memset,
and return to caml_init_domain with the saved ABI registers restored. -/
theorem table_tail_zero (c : Config) (base : Nat) (s0 s1 ra : BitVec 64)
    (region : Memset56Region base) (h : LeafInput ra c)
    (stack : gprGet c.σ 2 = some (firstMallocStack - 32#64))
    (pointer : gprGet c.σ 10 = some (BitVec.ofNat 64 base)) (saved : TableSaved s0 s1 c) :
    FnSummary 0x8000988c#64 (fun d => d = c)
      (RegistersPost [8, 1, 9, 12, 11, 2, 6, 14, 15, 13, 5] (memset56Memory c.σ.mem base) c
        jal_8002a934_call.link (BitVec.ofNat 64 base) (tableTailFinalRegs base s0 s1)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, restoreRun, restore⟩ := (table_tail_restore c _ s0 s1 ra h stack pointer saved).run c ⟨pc, rfl⟩
  have input : Memset56Input (BitVec.ofNat 64 base) jal_8002a934_call.link a := {
    good := restore.good
    image := restore.image
    minstret := restore.minstret
    raReg := gholds_lookup _ restore.regs (by rfl)
    aligned := by decide
    tick := restore.tick
    pointer := restore.result
    zero := gholds_lookup _ restore.regs (by rfl)
    size := gholds_lookup _ restore.regs (by rfl)
    alignedPointer := by
      have nat := region.pairs.cursor_nat (k := 0) (by decide)
      simp only [pairCursor, Nat.mul_zero, Nat.add_zero] at nat
      rw [nat]; exact region.aligned }
  obtain ⟨after, zeroRun, zeroed⟩ := (memset56_registers a base _ region input).run a ⟨restore.pc, rfl⟩
  have effect := (restore.toEffectPost.trans zeroed.toEffectPost).widen
    (writes' := [8, 1, 9, 12, 11, 2, 6, 14, 15, 13, 5]) (by decide)
  refine ⟨after, restoreRun.trans zeroRun, ?_, ?_⟩
  · refine ⟨effect.good, effect.image, effect.minstret, effect.tick, effect.pc,
      effect.result, ?_, effect.output, effect.frame⟩
    exact zeroed.memory.trans (congrArg (fun m => memset56Memory m base) restore.memory)
  · have restored : GHolds a.σ [(8, s0), (9, s1), (2, firstMallocStack), (1, jal_8002a934_call.link), (11, 0#64)] :=
      holds_project restore.regs (by simp [tableTailRegs, lookupG])
    have final := holds_frame_ne zeroed.frame restored (by simp only [keysG]; decide)
      (by simp only [keysG]; decide) (by simp only [keysG]; decide)
    exact (gholds_append _ _).mpr ⟨final, zeroed.regs⟩
end OCaml.Vm.Boot.Startup
