import OCaml.Vm.Boot.Startup.MallocBootTop
import OCaml.Vm.Boot.Startup.AllocatorFresh
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A bounded log frame transports a word without expanding the memory map. -/
theorem read64_log_range {m : Mem} {log : List WEntry} {a : Nat}
    (h : OutLRange log a 8) : read64 (writeLog m log) a = read64 m a :=
  VsaIris.Sym.read64_logOut fun k hk => outL_of_range h (by omega) (by omega)

/-- The source effects establish the fresh-arena contract from initial ELF
metadata; this is the first initialized allocator invariant in startup. -/
theorem malloc_boot_fresh {C : MCtx} {R1 R2 R3 : Nat → BitVec 64} {m1 m2 m3 : Mem}
    (first : MallocBootAfterMorecore C R1 m1) (second : MallocBootAligned C m1 R2 m2)
    (top : MallocBootTop C m2 R3 m3) (arena : InitialArena C.Mt0)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat) : FreshArena m3 (heapStart + 3776) := by
  have below (a : Nat) (ha : a + 8 ≤ heapEnd) (safe : ∀ k, k < 8 → ¬ SbrkW 0 (a + k)) :
      read64 m2 a = read64 (writeLog m1 (mallocAlignLog C.s)) a := by
    apply second.read
    intro k hk
    have := safe k hk
    unfold SbrkW at *
    unfold mHead at stackHigh
    omega
  have initial (a : Nat) (ha : a + 8 ≤ heapEnd)
      (safe : ∀ k, k < 8 → ¬ SbrkW 0 (a + k))
      (alignOut : OutLRange (mallocAlignLog C.s) a 8)
      (topOut : OutLRange mallocTopLog a 8) : read64 m3 a = read64 C.Mt0 a := by
    rw [top.memory, read64_log_range topOut, below a ha safe,
      read64_log_range alignOut, first.initial_read stackHigh ha safe]
  have alignOut (a : Nat) (ha : a + 8 ≤ heapEnd)
      (mi : a + 8 ≤ mallinfoAddr ∨ mallinfoAddr + 8 ≤ a)
      (base : a + 8 ≤ sbrkBaseAddr ∨ sbrkBaseAddr + 8 ≤ a) :
      OutLRange (mallocAlignLog C.s) a 8 := by
    simp only [mallocAlignLog, OutLRange, and_true]
    unfold mHead at stackHigh
    omega
  refine ⟨?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [top.memory, read64_log_range (by simp only [mallocTopLog, OutLRange] <;> decide), below sbrkBaseAddr (by decide)
      (by intro k hk; unfold SbrkW brkAddr sbrkBaseAddr; omega)]
    apply read64_of_writeLog_at _ _ 1 _ (BitVec.ofNat 64 heapStart) rfl
    simp only [mallocAlignLog, List.drop, OutLRange, and_true]
    unfold sbrkBaseAddr heapEnd mHead at *
    omega
  · rw [top.memory, read64_log_range (by simp only [mallocTopLog, OutLRange] <;> decide)]
    exact second.brk
  · rw [top.memory]
    exact read64_of_writeLog_at _ _ 0 _ (BitVec.ofNat 64 heapStart) rfl (by simp only [mallocTopLog, List.drop, OutLRange] <;> decide)
  · rw [top.memory]
    exact read64_of_writeLog_at _ _ 1 _ (3777#64) rfl (by simp only [mallocTopLog, List.drop, OutLRange] <;> decide)
  · rw [initial topPadAddr (by decide)
      (by intro k hk; unfold SbrkW brkAddr topPadAddr; omega)
      (alignOut _ (by decide) (by decide) (by decide)) (by simp only [mallocTopLog, OutLRange] <;> decide)]
    exact arena.top_pad
  · rw [initial maxSbrkedAddr (by decide)
      (by intro k hk; unfold SbrkW brkAddr maxSbrkedAddr; omega)
      (alignOut _ (by decide) (by decide) (by decide)) (by simp only [mallocTopLog, OutLRange] <;> decide), arena.max_sbrked]
    rfl
  · have stat : read64 m3 mallinfoAddr = some 3776 := by
      rw [top.memory]
      exact read64_of_writeLog_at _ _ 2 _ (3776#64) rfl (by simp only [mallocTopLog, List.drop, OutLRange] <;> decide)
    rw [stat]; rfl
  · intro i lo hi
    have links := arena.bin_links i lo hi
    have bounds : avAddr + 16 ≤ binAt i ∧ binAt i + 32 ≤ avAddr + 16 * numBins + 16 := by
      unfold binAt; omega
    have preserve (off : Nat) (ho : off = 16 ∨ off = 24) :
        read64 m3 (binAt i + off) = read64 C.Mt0 (binAt i + off) := by
      refine initial _ ?_ ?_ ?_ ?_
      · unfold heapEnd avAddr numBins at *; omega
      · intro k hk
        unfold SbrkW brkAddr avAddr numBins at *
        omega
      · apply alignOut <;> unfold heapEnd mallinfoAddr sbrkBaseAddr avAddr numBins at * <;> omega
      · simp only [mallocTopLog, OutLRange, and_true]
        unfold topAddr avAddr heapStart mallinfoAddr numBins at *
        omega
    refine ⟨binAt i, ?_, .close ?_⟩
    · rw [preserve 16 (Or.inl rfl)]; exact links.1
    · rw [preserve 24 (Or.inr rfl)]; exact links.2
  · rw [initial binblocksAddr (by decide)
      (by intro k hk; unfold SbrkW brkAddr binblocksAddr avAddr; omega)
      (alignOut _ (by decide) (by decide) (by decide)) (by simp only [mallocTopLog, OutLRange] <;> decide)]
    exact arena.binblocks

/-- First malloc has initialized the ordinary allocator heap. The remaining
statistics pass and top split consume the existing library proofs. -/
structure MallocBootReady (C : MCtx) (R : Nat → BitVec 64) (m : Mem) : Prop where
  frame : MFrame C R m
  a2 : R 12 = 3777#64
  a4 : R 14 = 944#64
  a6 : R 16 = BitVec.ofNat 64 avAddr
  t3 : R 28 = BitVec.ofNat 64 heapStart
  heap : PHeapAt m [] heapStart (heapStart + 3776) [] (fun _ => [])
  present : ∀ a : Nat, (C.Mt0[a]?).isSome → (m[a]?).isSome
  agree : ∀ a, ¬ MWin C.H C.s a → m[a]? = C.Mt0[a]?

/-- Generated malloc steps and two source morecore summaries establish the
initialized heap from source initial metadata, without assuming HeapAt. -/
theorem malloc_boot_initialize {C : MCtx} (O : WOK C) {R : Nat → BitVec 64}
    (E : MEntry C R) (arena : InitialArena C.Mt0) (size : C.n = 928#64)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat) (empty : C.H = [])
    (next : ∀ R' m, MallocBootReady C R' m → AW C.live C.S C.Q 0x800379e8#64 R' m) :
    AW C.live C.S C.Q 0x800375b8#64 R C.Mt0 := by
  apply malloc_boot_morecore O E arena size stackHigh
  intro R1 m1 first
  apply malloc_alignment_morecore O first arena stackHigh
  intro R2 m2 second
  apply malloc_boot_top O second stackHigh empty
  intro R3 m3 top
  apply next
  refine ⟨top.frame, top.a2, top.a4, top.a6, top.t3,
    (malloc_boot_fresh first second top arena stackHigh).heap, ?_, ?_⟩
  · intro a ha
    rw [top.memory]
    exact writeLog_present _ _ _ (second.present a (first.present a ha))
  · intro a ha
    rw [top.memory, writeLog_out, second.agree a ha, first.agree a ha]
    have globals : ¬ allocGlobal a := fun h => ha (.inl (.inl h))
    have heap : ¬ (heapStart ≤ a ∧ a < heapEnd) := by
      intro h
      apply ha
      refine .inl (.inr ⟨h.1, h.2, ?_⟩)
      rw [empty]
      simp
    simp only [mallocTopLog, OutL, and_true]
    unfold allocGlobal InRange at globals
    unfold topAddr avAddr heapStart heapEnd mallinfoAddr at *
    omega
end OCaml.Vm.Boot.Startup
