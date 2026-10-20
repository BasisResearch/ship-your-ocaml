import OCaml.Vm.Gc.OldifySlot

/-! # The collection in progress: what every root-slot call relies on

During a minor collection's root scan each `caml_oldify_one(*p, p)` starts
from memory that the collection so far has prepared: the forwarding table
published (`copies`), the major heap's allocator ready, the grey queue well
formed, the nursery bounds in `Caml_state`. `SlotSupply Ready Root pl support
writes` names that state as an obligation (lane a6-gc):

* `Ready copies m`: memory `m` is mid-collection with published table `copies`;
* `Root m p`: `p` is a root slot of this collection;
* `supply`: at a call on a root slot (`SlotEntry`: the caller's registers,
  the callee's frame, `R 10 = *R 11`) the call has a slot-level summary
  (`SlotCall`, one of the proved routes);
* `preserve`: after the call (`SlotDone` to `copies'`) memory is ready again,
  and the other roots are still roots;
* `footprint`: the call writes only inside the fixed region `writes`, its own
  native frame and the slot;
* `stable`: stores outside the fixed region `support` keep memory ready.

The root loops (`StackScan.loop`, `ChainScan.ChainLoop.walk`,
`GlobalScan.insert_loop`) take their per-call obligations from it. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The caller's side of a root-slot call at the callee's entry `e`. -/
structure SlotEntry (R : Nat → BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (e : Config) : Prop where
  good : GoodState e.σ
  minstret : ∃ v, e.σ.regs.get? Register.minstret = some v
  tick : e.tick < 2
  memory : e.σ.mem = m
  registers : GHolds e.σ (OldifyEntry.regs R)
  /-- the callee's native frame below the caller's `sp` -/
  windows : ∀ cell ∈ OldifyEntry.saves, WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  /-- the slot holds the value -/
  value : R 10 = bytesT m (R 11).toNat 8
  slotWrite : WriteWindow (R 11) 8
  slotApart : (R 11).toNat + 8 ≤ (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ (R 11).toNat
  aligned : (R 1).toNat % 4 = 0

/-- **The collection in progress** (named obligation, lane a6-gc). `writes`
and `support` are fixed for the whole collection: where calls may write
(the major heap's arena, the nursery, the grey queue, the domain's minor-GC
words) and what readiness reads. -/
structure SlotSupply (Ready : List PendingCopy → Std.ExtHashMap Nat (BitVec 8) → Prop)
    (Root : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) (pl : Place) (support writes : Nat → Prop) : Prop where
  supply : ∀ R copies m e, Ready copies m → Root m (R 11).toNat → SlotEntry R m e → SlotCall R copies pl e
  preserve : ∀ R copies copies' m e mid, Ready copies m → Root m (R 11).toNat → SlotEntry R m e →
    SlotDone R copies copies' pl e mid → Ready copies' mid.σ.mem ∧ ∀ q, Root m q → Root mid.σ.mem q
  footprint : ∀ R copies copies' m e mid, Ready copies m → Root m (R 11).toNat → SlotEntry R m e →
    SlotDone R copies copies' pl e mid → ∀ a, ¬ writes a →
    (a < (OldifyEntry.frameSp R).toNat ∨ (R 2).toNat ≤ a) → (a < (R 11).toNat ∨ (R 11).toNat + 8 ≤ a) →
    mid.σ.mem[a]? = m[a]?
  stable : ∀ copies m m', Ready copies m → (∀ a, support a → m'[a]? = m[a]?) →
    Ready copies m' ∧ ∀ q, Root m q → Root m' q
  /-- the code lies outside both -/
  codeOutside : ∀ a, a < tohostAddr → ¬ writes a

end OCaml.Vm.Gc
