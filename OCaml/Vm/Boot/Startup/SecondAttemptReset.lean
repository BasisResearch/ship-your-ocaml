import OCaml.Vm.Boot.Startup.RetryReset
import OCaml.Vm.Boot.Startup.AttemptToOpen
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- `argv[1]` ("/prog") is a `/`-rooted name in every state keeping the embedded image. -/
theorem argv1_rooted {d : Config} (h : EmbedImage d) : RootedName d.σ.mem argv1Ptr 5 where
  bytes := {
    nz := fun i hi => by
      change (d.σ.mem[_]?).getD 0 ≠ 0
      rw [argv1_byte h i (by omega)]
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
    nul := by change (d.σ.mem[_]?).getD 0 = 0; rw [argv1_byte h 5 (by decide)]; decide
    lo := by decide
    hi := by decide
    htif := by decide }
  region := by constructor <;> decide
  slash := by change (d.σ.mem[_]?).getD 0 = _; rw [argv1_byte h 0 (by decide)]; decide

theorem argv1_embedded (k : Nat) (hk : k ≤ 5) : EmbedByte (argv1Ptr.toNat + k) := by
  rw [show argv1Ptr.toNat = WhileMinImage.argv1 from by decide]
  constructor
  · unfold WhileMinImage.argv1 Vsa.Sim.DlHeap.heapEnd; omega
  · unfold WhileMinImage.argv1 embedLimit Layout.sym_stack_top Layout.sym_stack_size; omega

/-- Actual reset execution through the second caml_attempt_open's search and
duplication, up to `open("/prog", O_RDONLY)`. -/
structure ResetProgOpenCall (initial after : Config) where
  atRetry : Config
  retry : ResetRetryCall initial atRetry
  call : AttemptAtOpen ((retry.failed.opened.opened.node.toNat, 5) :: retry.failed.opened.call.search.path.table.H)
    (startupAllocatorCredits - 592) jal_8000512c_call.link (vsaReg atRetry 8) argvPtr (vsaReg atRetry 18)
    (vsaReg atRetry 19) (vsaReg atRetry 20) 1#64 argv1Ptr 5 atRetry after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_prog_open_call_exists : ∃ initial after, Nonempty (ResetProgOpenCall initial after) := by
  obtain ⟨initial, c, ⟨w⟩⟩ := reset_retry_call_exists
  have credits : startupAllocatorCredits - 496 = ((startupAllocatorCredits - 592) + 16) + 16 + 64 := by decide
  have ready : RuntimeReady ((w.failed.opened.opened.node.toNat, 5) :: w.failed.opened.call.search.path.table.H)
      ((((startupAllocatorCredits - 592) + 16) + 16) + 64) parameterStack jal_8000512c_call.link c := by
    rw [← credits]; exact w.ready
  have r (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) := gpr_of_ready w.ready n lo hi
  obtain ⟨s, run1, ⟨S⟩⟩ := (attempt_open_search c _ (((startupAllocatorCredits - 592) + 16)) 16
    jal_8000512c_call.link (vsaReg c 8) argvPtr (vsaReg c 18) (vsaReg c 19) (vsaReg c 20) 1#64 argv1Ptr 5 ready
    ⟨w.ready.stack, gholds_lookup (n := 1) _ w.regs rfl, r 8 (by decide) (by decide), w.argv,
      r 18 (by decide) (by decide), r 19 (by decide) (by decide), r 20 (by decide) (by decide),
      gholds_lookup (n := 10) _ w.regs rfl, gholds_lookup (n := 11) _ w.regs rfl,
      gholds_lookup (n := 12) _ w.regs rfl, trivial⟩
    w.late w.exeName argv1_embedded (fun d h => Or.inr (argv1_rooted h)) (by decide)
    ⟨by decide, by decide⟩).run c ⟨w.pc, rfl⟩
  obtain ⟨after, run2, ⟨A⟩⟩ := attempt_open_to_open S argv1_embedded (fun d h => Or.inr (argv1_rooted h))
    (by decide) ⟨by decide, by decide⟩
  exact ⟨initial, after, ⟨c, w, A, w.run.trans (run1.trans run2)⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
