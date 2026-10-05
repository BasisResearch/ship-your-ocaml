import OCaml.Vm.Gc.BestFitSplitGeometry
import OCaml.Vm.Boot.FreeList

/-!
# Placement of best-fit splits

`bf_split` (`freelist.c`) carves the requested block from the top of a
large free block and keeps the bottom as the remnant. If the free block lies in
a region `[lo, hi)` (`FreeIn`), so do both pieces (`Post.placed`). The remnant
ends exactly where the allocated block begins, so a region disjoint from the
nursery stays disjoint from it through every split. This is the step case of
the free-list placement invariant that supplies the collector's
`OwnedFrame.targetOutside`/`payloadOutside`.
-/

namespace OCaml.Vm.Gc.BestFitSplit
open Vsa.Machine Vsa.Sim Primitives

/-- A free block, header through last field, lies in `[lo, hi)`. -/
structure FreeIn (lo hi : Nat) (source : BitVec 64) (c : Config) : Prop where
  low : lo ≤ (headerAddr source).toNat
  high : (headerAddr source).toNat + 8 * ((header source c).toNat / 1024 + 1) ≤ hi
  ram : hi ≤ 2 ^ 64

/-- The header address of the block `split` returns. -/
def allocated (request source : BitVec 64) (c : Config) : BitVec 64 :=
  (delta request (header source c) <<< (3 : Nat)) + headerAddr source

theorem allocated_toNat {lo hi request source c} (free : FreeIn lo hi source c)
    (fits : request.toNat ≤ (header source c).toNat / 1024) :
    (allocated request source c).toNat =
      (headerAddr source).toNat + 8 * ((header source c).toNat / 1024 - request.toNat) := by
  have d := delta_nat request (header source c) fits
  have hh := free.high
  have hr := free.ram
  have bound := (header source c).isLt
  unfold allocated
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, d]
  have small : (header source c).toNat / 1024 - request.toNat < 2 ^ 54 := by omega
  rw [Nat.mod_eq_of_lt (by omega : ((header source c).toNat / 1024 - request.toNat) * 2 ^ 3 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A split stays in the free block's region.** The allocated block
(`request` fields plus its header) ends where the original block ended, and
the remnant written back at the original header lies below it. -/
theorem Post.placed {ra request source before after lo hi} (post : Post ra request source before after)
    (free : FreeIn lo hi source before) (fits : request.toNat < (header source before).toNat / 1024) :
    gprGet after.σ 10 = some (allocated request source before) ∧
      lo ≤ (allocated request source before).toNat ∧
      (allocated request source before).toNat + 8 * (request.toNat + 1) ≤ hi ∧
      FreeIn lo (allocated request source before).toNat source after := by
  have r := allocated_toNat free (Nat.le_of_lt fits)
  have remnant := post.remnant fits
  have hl := free.low
  have hh := free.high
  refine ⟨post.result, by omega, by omega, ⟨hl, ?_, by omega⟩⟩
  have size : (header source after).toNat / 1024 = (header source before).toNat / 1024 - request.toNat - 1 :=
    remnant.2
  rw [size, r]
  omega

/-- The startup singleton block lies between its own header and `heap_end`. -/
theorem freeIn_singleton {c : Config} {b : Boot.FreeBlock} (shape : Boot.BestFitSingletonAt c b) :
    FreeIn (b.block - 8) Layout.sym_heap_end (BitVec.ofNat 64 b.block) c := by
  have nonnull := shape.nonnull
  have fits := shape.fits
  have hdr := shape.header
  simp only [Layout.header_bytes, Layout.value_bytes, Layout.sym_heap_end, Layout.gc_blue] at nonnull fits hdr
  have addr : (headerAddr (BitVec.ofNat 64 b.block)).toNat = b.block - 8 := by
    simp only [headerAddr, Layout.header_bytes, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have size : (header (BitVec.ofNat 64 b.block) c).toNat / 1024 = b.words := by
    simp only [header, addr] at hdr ⊢
    rw [hdr]
    omega
  refine ⟨by rw [addr]; omega, ?_, by simp only [Layout.sym_heap_end]; omega⟩
  rw [addr, size]
  simp only [Layout.sym_heap_end]
  omega

end OCaml.Vm.Gc.BestFitSplit
