import OCaml.Vm.Boot.Startup.MallocBootHeap
import VsaIris.Vsa.MallocExtend
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The complete first allocation consumes source initial metadata, establishes
HeapAt, then reuses the landed allocator's statistics, split and return proofs.
RAM presence is supplied by the reset witness's densified memory. -/
theorem malloc_bootstrap {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    (E : MEntry C R) (arena : InitialArena C.Mt0) (size : C.n = 928#64)
    (stackHigh : heapEnd + mHead ≤ C.s.toNat) (empty : C.H = [])
    (top0 : C.top0 = heapStart)
    (present : ∀ a, vsaFoot C.H a → (C.Mt0[a]?).isSome) :
    AW C.live C.S C.Q 0x800375b8#64 R C.Mt0 := by
  apply malloc_boot_initialize O.toWOK E arena size stackHigh empty
  intro R0 m ready
  apply ext_stats O ready.heap.heap.heap.max_sbrked
  intro R' m' regs memory maxPresent pres
  have keep (a : Nat) (off : a + 8 ≤ maxSbrkedAddr - 8 ∨ maxSbrkedAddr + 8 ≤ a) :
      read64 m' a = read64 m a :=
    read64_keep fun k hk => memory _ (by unfold maxSbrkedAddr at off; omega)
  have heap' : PHeapAt m' [] heapStart (heapStart + 3776) [] (fun _ => []) := by
    refine ready.heap.topResize (by decide) (by decide) (by decide) ?_ ?_ ?_ maxPresent ?_
    · rw [keep brkAddr (by decide)]; exact ready.heap.heap.heap.brk
    · rw [keep (heapStart + 8) (by decide)]; exact ready.heap.heap.heap.top_header
    · rw [keep mallinfoAddr (by decide)]; exact ready.heap.heap.heap.mallinfo
    · intro a _ outside
      apply memory
      unfold GrowW brkAddr topPadAddr at outside
      omega
  have F : MFrame C R' m' := by
    refine ⟨(regs 2 (by decide)).trans ready.frame.sp, ?_, ?_,
      (regs 9 (by decide)).trans ready.frame.s1,
      (regs 18 (by decide)).trans ready.frame.s2,
      (regs 19 (by decide)).trans ready.frame.s3⟩
    · rw [keep _ (by unfold maxSbrkedAddr heapEnd mHead at *; omega)]
      exact ready.frame.s0
    · rw [keep _ (by unfold maxSbrkedAddr heapEnd mHead at *; omega)]
      exact ready.frame.ra
  have H : MHeap C m' (heapStart + 3776) [] (fun _ => []) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [empty, top0] using heap'
    · intro a ha
      exact pres a (ready.present a (present a ha))
    · intro a lo hi foot
      unfold vsaFoot allocGlobal InRange at foot
      unfold heapStart heapEnd mHead at *
      omega
    · intro a ha
      rw [memory a (by
        intro changed
        apply ha
        exact .inl (.inl (by unfold allocGlobal InRange; omega)))]
      exact ready.agree a ha
    · unfold LiveKeep
      rw [empty]
      simp
  have nb : NbOK C.n 944 := by rw [size]; exact ⟨by decide⟩
  apply ext_top O F H nb (by decide)
  · rw [regs 28 (by decide), ready.t3, top0]; rfl
  · rw [regs 12 (by decide), ready.a2, top0]; rfl
  · rw [regs 14 (by decide), ready.a4]; rfl
  · rw [regs 16 (by decide), ready.a6]; rfl
  · rw [top0]; decide

/-- The public malloc wrapper tail-calls the proved bootstrap body. -/
theorem malloc_bootstrap_entry {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    (E : MRegs C R) (request : R 10 = C.n) (arena : InitialArena C.Mt0)
    (size : C.n = 928#64) (stackHigh : heapEnd + mHead ≤ C.s.toNat)
    (empty : C.H = []) (top0 : C.top0 = heapStart)
    (present : ∀ a, vsaFoot C.H a → (C.Mt0[a]?).isSome) :
    AW C.live C.S C.Q mallocEntryBV R C.Mt0 := by
  change AW C.live C.S C.Q 0x80037598#64 R C.Mt0
  sx_run [4] O.live at 0x800375b8
  apply malloc_bootstrap O (arena := arena) (size := size) (stackHigh := stackHigh)
    (empty := empty) (top0 := top0) (present := present)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact E.ra
  · exact E.sp
  · rfl
  · exact request
  · exact E.s0
  · exact E.s1
  · exact E.s2
  · exact E.s3

/-- The general allocator result has a unique pointer at this first request:
its bounded top and aligned 928-byte allocation force the first chunk. -/
theorem MRet.first_pointer {C : MCtx} {R : Nat → BitVec 64} {m : Mem}
    (p : MRet C R m) (size : C.n = 928#64) (top0 : C.top0 = heapStart) :
    R 10 = BitVec.ofNat 64 (heapStart + 16) := by
  obtain ⟨top, brkv, chunks, bins, heap, topBound, _⟩ := p.heap
  have H := heap.heap.heap
  have member : ((R 10).toNat, C.n.toNat) ∈ ((R 10).toNat, C.n.toNat) :: C.H := .head _
  obtain ⟨c, hc, _, pointer, fits⟩ := H.exact _ member member
  have bounds := H.walk.chunk_bounds c hc
  have aligned := p.align
  rw [size, top0] at topBound
  rw [size] at fits
  change 936 ≤ c.size at fits
  have upper : top ≤ heapStart + 944 := topBound
  apply BitVec.eq_of_toNat_eq
  unfold heapStart at *
  simp only [BitVec.toNat_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod]
  omega
end OCaml.Vm.Boot.Startup
