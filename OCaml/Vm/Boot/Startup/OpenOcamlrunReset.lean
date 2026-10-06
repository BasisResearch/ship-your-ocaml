import OCaml.Vm.Boot.Startup.OpenCallReset
import OCaml.Vm.Boot.Startup.OpenRun
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

theorem gprGet_of_isSome {s : MState} {n : Nat} (h : (gprGet s n).isSome) :
    gprGet s n = some ((gprGet s n).getD 0) := by
  cases e : gprGet s n with
  | none => rw [e] at h; cases h
  | some v => rfl

/-- The heap copy of `argv[0]` is the name `resolve` sees. -/
theorem ResetOpenCall.ocamlrun_name {initial after} (w : ResetOpenCall initial after) :
    OcamlrunName after.σ.mem w.search.copy where
  aligned := by have := w.search.aligned; omega
  region := by
    have := w.search.fresh
    have := w.search.aligned
    unfold heapStart heapEnd at *
    exact ⟨by omega, by omega, Or.inr (by simp only [Layout.sym_tohost]; omega)⟩
  bytes := w.name

/-- Actual reset execution up to the return of `open("ocamlrun", O_RDONLY)`:
`-1` with ENOENT, and htif.c's file system initialised. -/
structure ResetOcamlrunOpened (initial after : Config) where
  atCall : Config
  call : ResetOpenCall initial atCall
  s0 : BitVec 64
  s1 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  s6 : BitVec 64
  s7 : BitVec 64
  s8 : BitVec 64
  s9 : BitVec 64
  s10 : BitVec 64
  opened : OpenOcamlrun ((call.search.copy.toNat, 9) :: call.search.path.table.H) (startupAllocatorCredits - 496)
    attemptStack jal_80004920_call.link call.search.copy s0 s1 call.search.copy s3 s4 s5 s6 s7 s8 s9 s10 atCall after
  run : Steps (Vsa.Densify.fillZero initial) after

theorem reset_ocamlrun_opened_exists : ∃ initial after, Nonempty (ResetOcamlrunOpened initial after) := by
  obtain ⟨initial, c, ⟨w⟩⟩ := reset_open_call_exists
  have present (n : Nat) (lo : 1 ≤ n) (hi : n < 32) : gprGet c.σ n = some ((gprGet c.σ n).getD 0) :=
    gprGet_of_isSome (w.ready.platform.gpr n lo (by omega))
  let r (n : Nat) : BitVec 64 := (gprGet c.σ n).getD 0
  have credits : startupAllocatorCredits - 480 = (startupAllocatorCredits - 496) + 16 := by decide
  have ready : RuntimeReady ((w.search.copy.toNat, 9) :: w.search.path.table.H) ((startupAllocatorCredits - 496) + 16)
      attemptStack jal_80004920_call.link c := by rw [← credits]; exact w.ready
  have regs : GHolds c.σ (libOpenInput attemptStack jal_80004920_call.link w.search.copy 0#64
      (r 12) (r 13) (r 14) (r 15) (r 16) (r 17) ++
      openCarried (r 8) (r 9) w.search.copy (r 19) (r 20) (r 21) (r 22) (r 23) (r 24) (r 25) (r 26)) := by
    refine ⟨w.stack, w.link, w.path, w.flags, present 12 (by decide) (by decide), present 13 (by decide) (by decide),
      present 14 (by decide) (by decide), present 15 (by decide) (by decide), present 16 (by decide) (by decide),
      present 17 (by decide) (by decide), present 8 (by decide) (by decide), present 9 (by decide) (by decide),
      w.truename, present 19 (by decide) (by decide), present 20 (by decide) (by decide),
      present 21 (by decide) (by decide), present 22 (by decide) (by decide), present 23 (by decide) (by decide),
      present 24 (by decide) (by decide), present 25 (by decide) (by decide), present 26 (by decide) (by decide), trivial⟩
  have frame : NativeFrame attemptStack openDepth := by constructor <;> decide
  have home : ∃ e ∈ (w.search.copy.toNat, 9) :: w.search.path.table.H,
      e.1 ≤ w.search.copy.toNat ∧ w.search.copy.toNat + 9 ≤ e.1 + e.2 :=
    ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have pathLow : w.search.copy.toNat + 16 ≤ heapEnd := by
    have := w.search.fresh; have := w.search.aligned; unfold heapEnd at *; omega
  obtain ⟨after, run, ⟨o⟩⟩ := (open_ocamlrun c _ (startupAllocatorCredits - 496) 16 attemptStack
    jal_80004920_call.link w.search.copy _ _ _ _ _ _ _ _ w.search.copy _ _ _ _ _ _ _ _ ready frame (by decide)
    w.kept.embed regs w.kept.htif.notReady w.kept.htif.clear w.kept.htif.reent w.ocamlrun_name home pathLow
    ⟨by decide, by decide⟩).run c ⟨w.pc, rfl⟩
  exact ⟨initial, after, ⟨⟨c, w, r 8, r 9, r 19, r 20, r 21, r 22, r 23, r 24, r 25, r 26, o, w.run.trans run⟩⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
