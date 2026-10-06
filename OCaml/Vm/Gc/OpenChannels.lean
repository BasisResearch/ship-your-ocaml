import OCaml.Vm.Repr

/-!
# The runtime's open-channel list

`caml_all_opened_channels` heads a singly linked list of every open channel
record, through each record's `next` field (`link_channel`, `io.c`). F1's
newlib-heap invariant uses it to know that every channel record is a live
malloc block; `caml_open_descriptor_in` links the new record at the head.
-/

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim OCaml.Vm

/-- `struct channel`'s `next` field (`runtime/caml/io.h`, LP64). -/
def chanOffNext : Nat := 48

/-- `as` is the open-channel list starting at record address `a` (`0` ends it). -/
inductive OpenChannels (m : Std.ExtHashMap Nat (BitVec 8)) : Nat → List Nat → Prop
  | nil : OpenChannels m 0 []
  | cons {a : Nat} {as : List Nat} : a ≠ 0 → OpenChannels m (bytesT m (a + chanOffNext) 8).toNat as →
      OpenChannels m a (a :: as)

/-- The runtime's open channels, from the list head. -/
def OpenChannelList (m : Std.ExtHashMap Nat (BitVec 8)) (as : List Nat) : Prop :=
  OpenChannels m (bytesT m Layout.sym_caml_all_opened_channels 8).toNat as

/-- `link_channel`'s effect: the new record `a` heads the list and points at
the old head. -/
structure OpenChannelsLinked (before after : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : Prop where
  head : bytesT after Layout.sym_caml_all_opened_channels 8 = BitVec.ofNat 64 a
  next : bytesT after (a + chanOffNext) 8 = bytesT before Layout.sym_caml_all_opened_channels 8
  nonzero : a ≠ 0

end OCaml.Vm.Gc
