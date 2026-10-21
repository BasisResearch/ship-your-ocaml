import OCaml.Vm.Gc.OpenChannels
import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Gc.G1RoomDefs

/-!
# The custom-block count from the channels' refcounts

`caml_alloc_channel` (io.c) increments `chan->refcount` before every
`caml_alloc_custom_mem`, from `caml_ml_open_descriptor_{in,out}` and from
each channel `caml_ml_out_channels_list` lists. No finalizer runs under G1,
so the custom blocks allocated since program start are the sum of the open
channels' refcounts (`RefcountSum m n`, `RefcountSumAt` naming the list). a6-gc's `Customs c n` is read at
this `n` (`F1Pins.customs`); the representation ties each refcount to the
channel's `refs` in the world.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm

/-- A channel record's `refcount`. -/
def chanRefs (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : Nat :=
  (bytesT m (a + chanOffRefcount) 4).toNat

/-- The refcounts of the records `chs`, summed. -/
def refcountSum (m : Std.ExtHashMap Nat (BitVec 8)) (chs : List Nat) : Nat :=
  (chs.map (chanRefs m)).sum

/-- **The open channels `chs`, whose refcounts sum to `n`.** -/
structure RefcountSumAt (m : Std.ExtHashMap Nat (BitVec 8)) (chs : List Nat) (n : Nat) : Prop where
  opened : OpenChannelList m chs
  sum : refcountSum m chs = n

/-- The open channels' refcounts sum to `n`. -/
def RefcountSum (m : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) : Prop :=
  ∃ chs, RefcountSumAt m chs n

/-- The sum is determined by memory (the list is: `OpenChannels.unique`). -/
theorem RefcountSum.unique {m : Std.ExtHashMap Nat (BitVec 8)} {n n' : Nat}
    (h : RefcountSum m n) (h' : RefcountSum m n') : n = n' := by
  obtain ⟨chs, opened, sum⟩ := h
  obtain ⟨chs', opened', sum'⟩ := h'
  rw [← sum, ← sum', OpenChannels.unique opened opened']

/-- An empty list head (the whileMin cut: `read_caml_all_opened_channels`)
sums to 0. -/
theorem RefcountSum.of_null {m : Std.ExtHashMap Nat (BitVec 8)}
    (head : bytesT m Layout.sym_caml_all_opened_channels 8 = 0#64) : RefcountSum m 0 :=
  ⟨[], by rw [OpenChannelList, head]; exact .nil, rfl⟩

/-- The G1 budget's custom blocks are the quiet ones (`quietBound`). -/
theorem g1Budget_customs : g1Budget.customs = quietBound := rfl

end OCaml.Vm.Gc
