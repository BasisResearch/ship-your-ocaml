import OCaml.Vm.Boot.Startup.AtomTable
import OCaml.Vm.Boot.Startup.InitStackReset

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives Startup

/-- The atom return retains the domain ownership and the low initial root data. -/
structure AtomTableReset (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra ent raw : BitVec 64) (before after : Config) : Prop where
  done : AtomTableDone H capacity sp ra ent raw before after
  domainOwned : (firstDomainPtr.toNat, 928) ∈ H
  lastExn : bytesT after.σ.mem (domainField backtrace_last_exnOffset) 8 = 1#64
  globals : ∀ x, (0x80064d10 ≤ x ∧ x < 0x80064d14) ∨ (0x800684e0 ≤ x ∧ x < 0x80068570) →
    (after.σ.mem[x]?).getD 0 = 0

/-- The reset run through the atom-table initializer. The native allocator,
256-header loop and page registration execute before returning to caml_main. -/
theorem reset_init_atom_table_reset_exists :
    ∃ initial after, Steps (Vsa.Densify.fillZero initial) after ∧
      ∃ H ent raw before, AtomTableReset H
        (startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192)
        parameterStack jal_80004e7c_call.link ent raw before after := by
  obtain ⟨initial, d, run, H, s0, s1, s2, mx, p, before, R⟩ := reset_init_stack_reset_exists
  obtain ⟨ent, T⟩ := R.table
  obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp (R.done.ready.gpr_some 10 (by decide) (by decide))
  have pc : PCAt 0x80004e7c#64 d := by
    have link : jal_80004e78_call.link = 0x80004e7c#64 := by decide
    rw [← link]
    exact R.done.pc
  obtain ⟨e, step, P⟩ := (caml_init_atoms_call d jal_80004e78_call.link a0 R.done.ready.toLeafInput
    ⟨ha0, trivial⟩).run d ⟨pc, rfl⟩
  have g := GprsSame.of_post P (by decide)
  have credits : startupAllocatorCredits - 656 - initGcCredits - 32768 =
      (startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192) + 8192 := by decide
  have ready := R.done.ready
  rw [credits] at ready
  have readyE := ready.stack_log P (by decide) (by simp only [keysG]; decide) (by decide)
    (g.get (by decide) (by decide) (by decide) R.done.ready.stack)
    (gholds_lookup (n := 1) _ P.regs rfl) (by decide) initStack_frame (by simp only [LogInW])
  have mem : e.σ.mem = d.σ.mem := P.memory
  obtain ⟨raw, f, steps, A⟩ := caml_init_atom_table e ((p.toNat, 32768) :: H)
    (startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192) 8192
    parameterStack jal_80004e7c_call.link ent {
      pc := by rw [← jal_80004e7c_call_target]; exact P.pc
      regs := ⟨readyE.stack, readyE.raReg, trivial⟩
      ready := readyE
      frame := by constructor <;> decide
      charged := ⟨by decide, by decide⟩
      table := by rw [mem]; exact T.table
      room := by rw [mem, T.count]; decide }
  exact ⟨initial, f, run.trans (step.trans steps), _, ent, raw, e, {
    done := A
    domainOwned := List.mem_cons_of_mem _ R.domainOwned
    lastExn := by
      have live := A.domain_live (List.mem_cons_of_mem _ R.domainOwned)
      rw [word_observed (m := e.σ.mem) _ fun i hi => live.byte _ (List.mem_singleton_self _) _
        ⟨by unfold domainField backtrace_last_exnOffset; dsimp only; omega,
         by unfold domainField backtrace_last_exnOffset; dsimp only; omega⟩, mem]
      exact R.lastExn
    globals := fun x hx => by
      rw [A.root_globals hx, mem]
      exact R.globals x hx }⟩

/-- Compatibility projection of the stronger reset producer. -/
theorem reset_init_atom_table_returned_exists :
    ∃ initial after, Steps (Vsa.Densify.fillZero initial) after ∧
      ∃ H ent raw before, AtomTableDone H
        (startupAllocatorCredits - 656 - initGcCredits - 32768 - 8192)
        parameterStack jal_80004e7c_call.link ent raw before after := by
  obtain ⟨initial, after, run, H, ent, raw, before, A⟩ := reset_init_atom_table_reset_exists
  exact ⟨initial, after, run, H, ent, raw, before, A.done⟩

end OCaml.Vm.Boot.WhileMinElfParse
