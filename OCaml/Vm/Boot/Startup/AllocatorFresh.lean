import OCaml.Vm.Boot.Startup.AllocatorInitial
import VsaIris.Vsa.HeapRoom
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.VsaHeap

/-- Source words of a newly initialized arena, before any chunk is allocated.
The boot execution supplies these fields after its two morecore calls. -/
structure FreshArena (m : Mem) (brkv : Nat) : Prop where
  base : read64 m sbrkBaseAddr = some heapStart
  brk : read64 m brkAddr = some brkv
  bound : brkv ≤ heapEnd
  room : heapStart + 32 ≤ brkv
  page : brkv % 4096 = 0
  top : read64 m topAddr = some heapStart
  header : read64 m (heapStart + 8) = some (brkv - heapStart + 1)
  pad : read64 m topPadAddr = some 0
  max_sbrked : (read64 m maxSbrkedAddr).isSome
  mallinfo : (read64 m mallinfoAddr).isSome
  bins : ∀ i, 0 < i → i < numBins → BinList m i []
  binblocks : read64 m binblocksAddr = some 0

theorem FreshArena.size_align {m : Mem} {brkv : Nat} (p : FreshArena m brkv) :
    (brkv - heapStart) % 16 = 0 := by
  have := p.page
  have := p.room
  unfold heapStart at *
  omega

private theorem odd_word {word : Option Nat} {n : Nat} (h : word = some n)
    (odd : n % 2 = 1) : word.any (fun h => h % 2 == 1) := by
  rw [h]
  simpa only [Option.any_some, beq_iff_eq] using odd

theorem FreshArena.first_prev {m : Mem} {brkv : Nat} (p : FreshArena m brkv) :
    (read64 m (heapStart + 8)).any (fun h => h % 2 == 1) :=
  odd_word p.header (by have := p.size_align; omega)

/-- Empty bins and a single free top satisfy the ordinary allocator invariant. -/
theorem FreshArena.raw_heap {m : Mem} {brkv : Nat} (p : FreshArena m brkv) :
    HeapAt m [] (fun _ => False) heapStart brkv [] (fun _ => []) := by
  refine {
    sbrk_base := p.base
    brk := p.brk
    brk_le := p.bound
    top_ptr := p.top
    top_le := by have := p.room; omega
    top_size := p.size_align
    top_header := p.header
    top_pad := p.pad
    max_sbrked := p.max_sbrked
    mallinfo := p.mallinfo
    first_prev := p.first_prev
    walk := .top
    coalesced := fun i hi => False.elim (Nat.not_lt_zero (i + 1) hi)
    footer := fun c hc => nomatch hc
    bins_list := p.bins
    bins_nodup := fun _ => .nil
    bin_free := fun _ _ _ _ h => nomatch h
    free_binned := fun c hc => nomatch hc
    remainder := by decide
    binblocks_present := by rw [p.binblocks]; rfl
    binblocks := fun _ _ _ _ _ h => False.elim (h rfl)
    live := fun e he => nomatch he
    exact := fun e he => nomatch he
  }
theorem FreshArena.heap {m : Mem} {brkv : Nat} (p : FreshArena m brkv) :
    PHeapAt m [] heapStart brkv [] (fun _ => []) := by
  refine ⟨⟨?_, by have := p.room; omega⟩, p.page, ?_⟩
  · simpa only [List.not_mem_nil] using p.raw_heap
  · intro bb hb
    rw [p.binblocks] at hb
    cases hb
    decide
end OCaml.Vm.Boot.Startup
