import OCaml.Vm.Gc.OpenChannels
import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Gc.G1RoomDefs

/-!
# The custom-block count from the channels' refcounts

`caml_alloc_channel` (io.c) increments `chan->refcount` before every
`caml_alloc_custom_mem`, from `caml_ml_open_descriptor_{in,out}` and from
each channel `caml_ml_out_channels_list` lists. No finalizer runs under G1,
so the custom blocks allocated since program start are the sum of the open
channels' refcounts at VM boundaries (`RefcountSum m n`, `RefcountSumAt`
naming the list). `ChannelCustomsAt` also names the intermediate offset:
io.c increments the refcount before the physical custom allocation. The
physical-count supplier and its connection to the represented world's
`refs` must be carried by the invariant; `F1Pins` does not yet carry them.
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

/-- The list links survive a call. Refcounts may change independently; this
is shared by ordinary channel calls and the listing primitive. -/
structure ChannelLinksKept (m m' : Std.ExtHashMap Nat (BitVec 8)) (chs : List Nat) : Prop where
  head : bytesT m' Layout.sym_caml_all_opened_channels 8 = bytesT m Layout.sym_caml_all_opened_channels 8
  next : ∀ a ∈ chs, bytesT m' (a + chanOffNext) 8 = bytesT m (a + chanOffNext) 8

theorem ChannelLinksKept.opened {m m' : Std.ExtHashMap Nat (BitVec 8)} {chs : List Nat}
    (kept : ChannelLinksKept m m' chs) (opened : OpenChannelList m chs) : OpenChannelList m' chs := by
  unfold OpenChannelList
  rw [kept.head]
  exact opened.congr kept.next

/-- Pointwise refcount increments add to the total. `charge` is one for each
record visited by `caml_ml_out_channels_list` and zero for the other records.
The premise uses natural counts, so the caller must establish no 32-bit wrap. -/
theorem refcountSum_add {m m' : Std.ExtHashMap Nat (BitVec 8)} (chs : List Nat) (charge : Nat → Nat)
    (refs : ∀ a ∈ chs, chanRefs m' a = chanRefs m a + charge a) :
    refcountSum m' chs = refcountSum m chs + (chs.map charge).sum := by
  induction chs with
  | nil => rfl
  | cons a chs ih =>
    have tail := ih (fun b hb => refs b (List.mem_cons_of_mem _ hb))
    have head := refs a List.mem_cons_self
    simp only [refcountSum, List.map_cons, List.sum_cons] at *
    omega

/-- A call's refcount update, with unchanged list links. -/
theorem RefcountSumAt.add {m m' : Std.ExtHashMap Nat (BitVec 8)} {chs : List Nat} {n : Nat}
    (before : RefcountSumAt m chs n) (links : ChannelLinksKept m m' chs) (charge : Nat → Nat)
    (refs : ∀ a ∈ chs, chanRefs m' a = chanRefs m a + charge a) :
    RefcountSumAt m' chs (n + (chs.map charge).sum) :=
  ⟨links.opened before.opened, by rw [refcountSum_add chs charge refs, before.sum]⟩

/-- Non-allocating channel calls keep the custom count when they keep the
links and the refcount fields. Buffer, cursor and descriptor writes are free. -/
theorem RefcountSumAt.frame {m m' : Std.ExtHashMap Nat (BitVec 8)} {chs : List Nat} {n : Nat}
    (before : RefcountSumAt m chs n) (links : ChannelLinksKept m m' chs)
    (refs : ∀ a ∈ chs, chanRefs m' a = chanRefs m a) : RefcountSumAt m' chs n := by
  refine ⟨links.opened before.opened, ?_⟩
  rw [refcountSum, List.map_congr_left refs]
  exact before.sum

/-- A newly opened channel is prepended with its initial reference count.
Existing records need only their next links and refcounts preserved. -/
theorem RefcountSumAt.link {m m' : Std.ExtHashMap Nat (BitVec 8)} {chs : List Nat} {n a k : Nat}
    (before : RefcountSumAt m chs n) (linked : OpenChannelsLinked m m' a) (bound : a < 2 ^ 64)
    (next : ∀ b ∈ chs, bytesT m' (b + chanOffNext) 8 = bytesT m (b + chanOffNext) 8)
    (refs : ∀ b ∈ chs, chanRefs m' b = chanRefs m b) (initial : chanRefs m' a = k) :
    RefcountSumAt m' (a :: chs) (n + k) := by
  refine ⟨?_, ?_⟩
  · unfold OpenChannelList
    rw [linked.head, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    apply OpenChannels.cons linked.nonzero
    rw [linked.next]
    exact before.opened.congr next
  · simp only [refcountSum, List.map_cons, List.sum_cons, initial]
    rw [List.map_congr_left refs]
    have sum := before.sum
    unfold refcountSum at sum
    omega

/-- Physical custom allocations and channel references at a native boundary.
`pending` counts references incremented before their custom allocations;
it is zero at VM boundaries and one immediately before `caml_alloc_custom_mem`.
`Customs` reads the runtime's physical accounting state, separately from refs. -/
structure ChannelCustomsAt (Customs : Config → Nat → Prop) (c : Config)
    (chs : List Nat) (n pending : Nat) : Prop where
  physical : Customs c n
  refs : RefcountSumAt c.σ.mem chs (n + pending)

/-- Initial empty channels, given the runtime's physical zero-count witness. -/
theorem ChannelCustomsAt.of_null {Customs : Config → Nat → Prop} {c : Config}
    (physical : Customs c 0)
    (head : bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8 = 0#64) :
    ChannelCustomsAt Customs c [] 0 0 := by
  refine ⟨physical, ?_⟩
  refine ⟨?_, rfl⟩
  unfold OpenChannelList
  rw [head]
  exact .nil

/-- Shared caller-store frame. Buffer/link readbacks and the custom-state
frame are supplied once, independently of the consumer's byte argument. -/
theorem ChannelCustomsAt.frame {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c d : Config} {chs : List Nat} {n pending : Nat}
    (accounting : CustomMemCall.Accounting Ready state Customs)
    (before : ChannelCustomsAt Customs c chs n pending)
    (memory : ∀ a, state c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (links : ChannelLinksKept c.σ.mem d.σ.mem chs)
    (refs : ∀ a ∈ chs, chanRefs d.σ.mem a = chanRefs c.σ.mem a) :
    ChannelCustomsAt Customs d chs n pending :=
  ⟨accounting.frame before.physical memory domain, before.refs.frame links refs⟩

/-- The caller has bumped references, but the allocator has not run yet.
For an out-list batch the sum is the number of listed records, not one. -/
theorem ChannelCustomsAt.charge {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c d : Config} {chs : List Nat} {n pending : Nat}
    (accounting : CustomMemCall.Accounting Ready state Customs)
    (before : ChannelCustomsAt Customs c chs n pending)
    (memory : ∀ a, state c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (links : ChannelLinksKept c.σ.mem d.σ.mem chs) (charge : Nat → Nat)
    (refs : ∀ a ∈ chs, chanRefs d.σ.mem a = chanRefs c.σ.mem a + charge a) :
    ChannelCustomsAt Customs d chs n (pending + (chs.map charge).sum) := by
  refine ⟨accounting.frame before.physical memory domain, ?_⟩
  simpa only [Nat.add_assoc] using before.refs.add links charge refs

/-- An allocator return consumes exactly one pending reference. The exact
physical increment is a field of the named custom-call accounting obligation;
it is never inferred from the returned `Ready k`. -/
theorem ChannelCustomsAt.allocate
    {state Customs : Config → Nat → Prop} {c d : Config} {chs : List Nat} {n pending : Nat}
    {H : List (Nat × Nat)} {site : CustomMemSite} {v : BitVec 64}
    (before : ChannelCustomsAt Customs c chs n (pending + 1))
    (returned : CustomMemCountedReturned state Customs H site v c d)
    (links : ChannelLinksKept c.σ.mem d.σ.mem chs)
    (refs : ∀ a ∈ chs, chanRefs d.σ.mem a = chanRefs c.σ.mem a) :
    ChannelCustomsAt Customs d chs (n + 1) pending := by
  refine ⟨returned.count before.physical, ?_⟩
  have kept := before.refs.frame links refs
  rw [show n + 1 + pending = n + (pending + 1) by omega]
  exact kept

/-- Readiness uses physical accounting and the successful successor's budget.
This also applies to several out-list custom allocations. -/
theorem ChannelCustomsAt.ready {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {c : Config} {chs : List Nat} {n pending k : Nat}
    (accounting : CustomMemCall.Accounting Ready state Customs)
    (before : ChannelCustomsAt Customs c chs n pending)
    (bound : n + k ≤ quietBound) : Ready k c :=
  accounting.ready_of_bound before.physical bound

/-- The G1 budget's custom blocks are the quiet ones (`quietBound`). -/
theorem g1Budget_customs : g1Budget.customs = quietBound := rfl

end OCaml.Vm.Gc
