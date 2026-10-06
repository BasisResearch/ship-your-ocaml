import OCaml.Vm.Boot.Startup.FreeNull
import OCaml.Vm.Boot.Startup.FreeRun
import OCaml.Vm.Boot.Startup.StatCheckedAllocate
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- A generated read-only boundary is a register post with its memory unchanged. -/
theorem BoundaryPost.registers {writes before ra pc regs after value}
    (h : BoundaryPost writes before ra pc regs after) (result : lookupG 10 regs = some value) :
    RegistersPost writes before.σ.mem before pc value regs after :=
  ⟨⟨h.good, h.image, h.minstret, h.tick, h.pc, gholds_lookup _ h.regs result, h.memory, h.output, h.frame⟩,
    h.regs⟩
end OCaml.Vm.Primitives

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open VsaIris.MallocFast OCaml.Vm.Primitives

/-- Nonpooling `caml_stat_free` of a live block: dispatch, then the landed free. -/
structure StatFreed (H : List (Nat × Nat)) (q : BitVec 64) (n capacity : Nat) (sp ra : BitVec 64)
    (before after : Config) where
  atFree : Config
  dispatch : BoundaryPost [15, 14] before ra (BitVec.ofNat 64 Vsa.Alloc.freeEntry)
    [(15, q + 0#64), (14, 0#64), (10, q)] atFree
  platform : VsaOk startupLive atFree
  free : LocalPost startupLive roR allocText aRegs (fS H q n sp)
    (FreeRoomEnd vsaLayoutP vsaRoomB H ra sp (firstMallocSaved (vsaReg atFree)) capacity) atFree after
  ready : RuntimeReady H capacity sp ra after

theorem stat_free_block (c : Config) (H : List (Nat × Nat)) (q : BitVec 64) (n capacity : Nat)
    (sp ra : BitVec 64) (ready : RuntimeReady ((q.toNat, n) :: H) capacity sp ra c)
    (pointer : gprGet c.σ 10 = some q) (frame : NativeFrame sp allocHeadroom)
    (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd) :
    FnSummary 0x8000bb98#64 (fun d => d = c)
      (fun after => Nonempty (StatFreed H q n capacity sp ra c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨atFree, run1, dispatch⟩ := (stat_free_dispatch c ra q ready.toLeafInput ⟨pointer, trivial⟩
    ready.poolZero).run c ⟨pc, rfl⟩
  have mid := ready.effect (dispatch.registers (value := q) (by rfl)) (by decide)
    (by simp only [keysG]; decide) (by decide)
    ((dispatch.frame .x2 (by decide) (by decide)).trans ready.stack)
    ((dispatch.frame .x1 (by decide) (by decide)).trans ready.raReg) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have input : FreeInput H q n ra sp capacity atFree :=
    { good := mid.platform
      readOnly := mid.readOnly
      room := mid.room
      pointer := gholds_lookup (n := 10) _ dispatch.regs (by rfl)
      stack := mid.stack
      link := mid.raReg
      stackOk := frame.allocator_stack
      high := frame.lower
      aligned := mid.aligned
      blockLow := blockLow
      blockHigh := blockHigh }
  obtain ⟨after, run2, freed⟩ := (free_summary atFree H q n ra sp capacity input).run atFree ⟨dispatch.pc, rfl⟩
  exact ⟨after, run1.trans run2,
    ⟨atFree, dispatch, mid.platform, freed, mid.free_result frame.lower blockLow blockHigh freed⟩⟩

/-- The free keeps every library-saved register. -/
theorem StatFreed.saved_gpr {H q n capacity sp ra before after k}
    (w : StatFreed H q n capacity sp ra before after) (member : k ∈ vsaSaved) :
    gprGet after.σ k = gprGet before.σ k := by
  have range : 1 ≤ k ∧ k ≤ 31 ∧ k ≠ 15 ∧ k ≠ 14 := by simp [vsaSaved] at member; omega
  have mid : gprGet w.atFree.σ k = gprGet before.σ k := by
    apply gprGet_of_frame k range.1 range.2.1 (gpr_avoids_noise k (by omega) range.1)
    · intro m hm
      have hm' : m = 15 ∨ m = 14 := by
        rcases List.mem_cons.1 hm with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_singleton.1 h)
      rcases hm' with rfl | rfl
      · exact gprReg_beq_false 15 (by decide) k (by omega) (by decide) range.1 (fun e => range.2.2.1 e.symm)
      · exact gprReg_beq_false 14 (by decide) k (by omega) (by decide) range.1 (fun e => range.2.2.2 e.symm)
    · intro r noise outside
      exact w.dispatch.frame r (fun m hm => by
        have ne := outside m hm
        exact fun e => by rw [e, beq_self_eq_true] at ne; contradiction) noise
  exact (allocator_saved_register w.platform w.ready.platform w.free.result.frame k member).trans mid
end OCaml.Vm.Boot.Startup
