import OCaml.Vm.Sim.PayloadObserved
import OCaml.Vm.Primitives.Allocation

/-!
# The VM payload after `openChan`

At the return of `caml_ml_open_descriptor_*`, a payload of the old state
(kept across the call by `VmPayload.keep_observed`) extends to the opened
state: the placement gains the new record (`ChanPlace.put`), the heap the
custom block (`VmPayload.allocate`), and the world the new channel.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A channel object holds no heap pointers. -/
theorem allocationRoots_channel (P : Prog) (s : St) (id : Nat) : AllocationRoots P s (.channel id) :=
  fun _ _ h => nomatch h

/-- The roots read the world only through its argv, named values, callbacks
and pending exception. -/
theorem roots_chans (P : Prog) (s : St) (chs : List Chan) :
    roots P {s with world := {s.world with chans := chs}} = roots P s := rfl

/-- The state after `openChan` (pc and stack aside): the custom block in the
accumulator, the heap with it, the world with the new channel. -/
def openedSt (s : St) (ch : Chan) : St :=
  { s with
    accu := Val.ptr (s.heap.alloc (Obj.channel s.world.chans.length)).2 0
    heap := (s.heap.alloc (Obj.channel s.world.chans.length)).1
    world := { s.world with chans := s.world.chans ++ [ch] } }

/-- **The payload of the opened state**: the custom block `v` (placed at the
fresh location, laid out under the extended placement) and the new channel's
record `r`. -/
theorem VmPayload.openChan {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high r v : Nat}
    {ch : Chan} (h : VmPayload P s c pl cp sp high)
    (fresh : ∀ l, s.heap.get? l ≠ some (.channel s.world.chans.length))
    (placed : pl.φ (s.heap.alloc (.channel s.world.chans.length)).2 = some v)
    (layout : ObjAt c pl (cp.put s.world.chans.length r) v (.channel s.world.chans.length))
    (outside : AllocationOutside P s pl v (.channel s.world.chans.length))
    (record : ChanAt c r ch) :
    VmPayload P (openedSt s ch) c pl (cp.put s.world.chans.length r) sp high := by
  have placedAt : VmPayload P s c pl (cp.put s.world.chans.length r) sp high :=
    { h with
      heap := ⟨fun l hl => by
          obtain ⟨a, o, ha, ho, lay⟩ := h.heap.1 l hl
          exact ⟨a, o, ha, ho, ObjAt.openChan lay fresh ho⟩, h.heap.2⟩
      world := ⟨h.world.output, fun id ch' hc => by
          obtain ⟨a, ha, lay⟩ := h.world.chans id ch' hc
          have lt : id < s.world.chans.length := (List.getElem?_eq_some_iff.mp hc).1
          exact ⟨a, by rw [ChanPlace.put_other cp (Nat.ne_of_lt lt)]; exact ha, lay⟩, h.world.ooId⟩ }
  have alloc := VmPayload.allocate placedAt (allocationRoots_channel P s _) placed layout outside
  exact { alloc with
    heap := alloc.heap
    world := ⟨alloc.world.output, fun id ch' hc => by
        rcases chans_append_cases hc with ⟨old, lt⟩ | ⟨rfl, rfl⟩
        · exact alloc.world.chans id ch' old
        · exact ⟨r, ChanPlace.put_self cp _ r, record⟩, alloc.world.ooId⟩ }

end OCaml.Vm.Sim
