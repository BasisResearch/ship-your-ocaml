import OCaml.Vm.Boot.Startup.SecondAttemptReset
import OCaml.Vm.Boot.Startup.OpenProg
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

theorem argv1_prog_byte (k : Nat) (hk : k ≤ 5) :
    BitVec.ofNat 8 (byteVal WhileMinImage.argv1Chars k) = progByte k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- caml_attempt_open's heap copy of `argv[1]` is the "/prog" `resolve` sees. -/
theorem ResetProgOpenCall.prog_path {initial after} (w : ResetProgOpenCall initial after) :
    ProgPath after.σ.mem w.call.copy where
  aligned := w.call.aligned
  region := by
    have := w.call.fresh
    have := w.call.aligned
    unfold heapStart heapEnd at *
    exact ⟨by omega, by omega, Or.inr (by simp only [Layout.sym_tohost]; omega)⟩
  bytes := fun k hk => by
    rw [w.call.bytes k hk, ← w.call.late.embed.byte _ (argv1_embedded k hk), argv1_byte w.call.late.embed k hk,
      argv1_prog_byte k hk]

/-- Actual reset execution up to the return of `open("/prog", O_RDONLY)`:
descriptor 3. -/
structure ResetProgOpened (initial after : Config) where
  atCall : Config
  call : ResetProgOpenCall initial atCall
  opened : OpenProg ((call.call.copy.toNat, 5 + 1) :: (call.retry.failed.opened.opened.node.toNat, 5) ::
      call.retry.failed.opened.call.search.path.table.H) (startupAllocatorCredits - 592) attemptStack
    jal_80004920_call.link (vsaReg atCall 8) (vsaReg atCall 9) call.call.copy (vsaReg atCall 19) (vsaReg atCall 20)
    (vsaReg atCall 21) (vsaReg atCall 22) (vsaReg atCall 23) (vsaReg atCall 24) (vsaReg atCall 25) (vsaReg atCall 26)
    atCall after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_prog_opened_exists : ∃ initial after, Nonempty (ResetProgOpened initial after) := by
  obtain ⟨initial, c, ⟨w⟩⟩ := reset_prog_open_call_exists
  have present (n : Nat) (lo : 1 ≤ n) (hi : n < 32) : gprGet c.σ n = some (vsaReg c n) := by
    unfold vsaReg
    simp only [VsaIris.PC, show n ≠ 32 by omega, ↓reduceIte]
    exact gprGet_of_isSome (w.call.ready.platform.gpr n lo (by omega))
  have regs : GHolds c.σ (libOpenInput attemptStack jal_80004920_call.link w.call.copy 0#64
      (vsaReg c 12) (vsaReg c 13) (vsaReg c 14) (vsaReg c 15) (vsaReg c 16) (vsaReg c 17) ++
      openCarried (vsaReg c 8) (vsaReg c 9) w.call.copy (vsaReg c 19) (vsaReg c 20) (vsaReg c 21) (vsaReg c 22)
        (vsaReg c 23) (vsaReg c 24) (vsaReg c 25) (vsaReg c 26)) := by
    refine ⟨w.call.stack, w.call.link, w.call.path, w.call.flags, present 12 (by decide) (by decide),
      present 13 (by decide) (by decide), present 14 (by decide) (by decide), present 15 (by decide) (by decide),
      present 16 (by decide) (by decide), present 17 (by decide) (by decide), present 8 (by decide) (by decide),
      present 9 (by decide) (by decide), w.call.truename, present 19 (by decide) (by decide),
      present 20 (by decide) (by decide), present 21 (by decide) (by decide), present 22 (by decide) (by decide),
      present 23 (by decide) (by decide), present 24 (by decide) (by decide), present 25 (by decide) (by decide),
      present 26 (by decide) (by decide), trivial⟩
  have frame : NativeFrame attemptStack openProgDepth := by constructor <;> decide
  have nodeB := w.call.ready.heap.block_bounds (q := w.retry.failed.opened.opened.node.toNat) (n := 5)
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have fresh := w.call.fresh
  have aligned := w.call.aligned
  obtain ⟨after, run, O⟩ := (open_prog c _ (startupAllocatorCredits - 592) attemptStack jal_80004920_call.link
    w.call.copy w.retry.failed.opened.opened.node _ _ _ _ _ _ _ _ w.call.copy _ _ _ _ _ _ _ _ w.call.ready frame regs
    w.call.late.reent w.fs
    (by unfold heapStart heapEnd at *; exact ⟨by omega, by omega, Or.inr (by simp only [Layout.sym_tohost]; omega)⟩)
    nodeB.1 nodeB.2 w.prog_path fresh.1 (by omega) (by
      have h : heapEnd + openProgDepth ≤ attemptStack.toNat := by decide
      unfold heapEnd at *; omega)).run c
    ⟨w.call.pc, rfl⟩
  exact ⟨initial, after, ⟨⟨c, w, O, w.run.trans run⟩⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
