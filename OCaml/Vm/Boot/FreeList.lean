import OCaml.Vm.Runtime

/-! A concrete startup specialization of the best-fit free-list shape.

`runtime/freelist.c` stores size-indexed small lists and a size-ordered
large-block tree. At the observed cut every small list is empty and the
large tree contains a single block. This predicate describes that shape;
allocation and collection may require a more general free-list predicate.
Structure sizes, field offsets and symbols come from the target compiler
and ELF through `gen_layout.py`.
-/
namespace OCaml.Vm.Boot
open Vsa.Machine

/-- The address of a small-list slot, indexed as in `freelist.c` (1 through 16). -/
def smallSlot (i : Nat) : Nat := Layout.sym_bf_small_fl + i * Layout.bf_small_size

/-- One empty small-list slot, including its merge cursor. -/
structure EmptySmall (c : Config) (i : Nat) : Prop where
  head : word c (smallSlot i + Layout.off_bf_small_free) = 0
  merge : (word c (smallSlot i + Layout.off_bf_small_merge)).toNat =
    smallSlot i + Layout.off_bf_small_free

/-- A singleton blue large-block tree with the allocator's accounting and
small-list cursors. The block address and size are witnesses, not pins. -/
structure FreeBlock where
  block : Nat
  words : Nat

/-- Concrete fields of the singleton tree and the empty small lists. -/
structure BestFitSingletonAt (c : Config) (b : FreeBlock) : Prop where
  nonnull : Layout.header_bytes ≤ b.block
  aligned : b.block % Layout.value_bytes = 0
  large : Layout.bf_small_count < b.words
  fits : b.block + Layout.value_bytes * b.words ≤ Layout.sym_heap_end
  small : ∀ i, 1 ≤ i → i ≤ Layout.bf_small_count → EmptySmall c i
  bitmap : word32 c Layout.sym_bf_small_map = 0
  root : (word c Layout.sym_bf_large_tree).toNat = b.block
  least : (word c Layout.sym_bf_large_least).toNat = b.block
  header : (word c (b.block - Layout.header_bytes)).toNat = b.words * 1024 + Layout.gc_blue
  node : word32 c (b.block + Layout.off_bf_isnode) = 1
  left : word c (b.block + Layout.off_bf_left) = 0
  right : word c (b.block + Layout.off_bf_right) = 0
  prev : (word c (b.block + Layout.off_bf_prev)).toNat = b.block
  next : (word c (b.block + Layout.off_bf_next)).toNat = b.block
  total : (word c Layout.sym_caml_fl_cur_wsz).toNat = b.words + 1

/-- The startup shape with its concrete free block hidden. -/
structure BestFitSingleton (c : Config) : Prop where
  shape : ∃ b, BestFitSingletonAt c b

end OCaml.Vm.Boot
