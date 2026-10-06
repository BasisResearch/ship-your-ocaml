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

/-- Equal `next` words keep the open-channel list. -/
theorem OpenChannels.congr {m m' : Std.ExtHashMap Nat (BitVec 8)} {x : Nat} {chs : List Nat}
    (h : OpenChannels m x chs) (same : ∀ a ∈ chs, bytesT m' (a + chanOffNext) 8 = bytesT m (a + chanOffNext) 8) :
    OpenChannels m' x chs := by
  -- discipline: allow(O5-run-induction) `OpenChannels` is the shape of one linked list in a fixed memory, not a run relation
  induction h with
  | nil => exact .nil
  | @cons a chs ne _ ih =>
    refine .cons ne ?_
    rw [same a List.mem_cons_self]
    exact ih fun b hb => same b (List.mem_cons_of_mem _ hb)

/-- The open-channel list is determined by memory. -/
theorem OpenChannels.unique {m : Std.ExtHashMap Nat (BitVec 8)} {x : Nat} {l₁ l₂ : List Nat}
    (h₁ : OpenChannels m x l₁) (h₂ : OpenChannels m x l₂) : l₁ = l₂ := by
  -- discipline: allow(O5-run-induction) `OpenChannels` is the shape of one linked list in a fixed memory, not a run relation
  induction h₁ generalizing l₂ with
  | nil =>
    cases h₂ with
    | nil => rfl
    | cons ne _ => exact absurd rfl ne
  | @cons a rest ne _ ih =>
    cases h₂ with
    | nil => exact absurd rfl ne
    | cons _ tail => rw [ih tail]

end OCaml.Vm.Gc
