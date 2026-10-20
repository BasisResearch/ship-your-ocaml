import OCaml.Vm.Sim.OpenOutObserved
import OCaml.Vm.Sim.OpenPayload

/-!
# The VM payload at `caml_ml_open_descriptor_out`'s return

The entry's payload is kept across the call (`open_out_observed`,
`VmPayload.keep_observed`, the console output by `OpenedOut.output`), then
extends to the opened state (`VmPayload.openChan`): the custom block is laid
out as `.channel n` (header, `&channel_operations`, the record), apart from
every old object (it lies in the free nursery), and the record represents the
new console channel (`OutRecord.chanAt`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel

/-- **The payload of the opened state** at the return. -/
theorem open_out_payload {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {spV high : Nat} {fd : Int} {heap' : Heap} {world' : World} {val : Val}
    {live : Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {H : List (Nat × Nat)} {cap cap' charge : Nat} {sp ra r0 r1 r2 v head : BitVec 64} {c d : Config}
    (custom : Gc.CustomMemCall Ready state)
    (o : OpenedOut live Ready state k H cap' charge sp ra r0 r1 r2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput live H cap' charge sp ra r0 r1 r2 v head c)
    (N : OutNursery H (Gc.placedChannels cp s.world.chans.length) c)
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) (g : OCaml.LoopGeometry L P s c pl cp high)
    (fits : 8 * s.stack.length ≤ Layout.stackBytes)
    (ok : openChan s.heap s.world fd true = .ok val heap' world')
    (fdWord : ((fdOf v).setWidth 32).toInt = fd) (open_ : fd ≠ -1)
    (placed : pl.φ (s.heap.alloc (.channel s.world.chans.length)).2 = some o.value.toNat) :
    VmPayload P (openedSt s ⟨fd, true, [], [], 0, -1⟩) d pl
      (cp.put s.world.chans.length o.opening.record.toNat) spV high := by
  have kept := VmPayload.keep_observed data (open_out_observed custom o heap h N pins data g fits) o.output
  have block := o.block
  have room := N.room
  have low := N.low
  have small : o.value.toNat + 16 < 2 ^ 64 := by have := g.nursery.top; omega
  have v8 : (o.value + 8#64).toNat = o.value.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have layout : ObjAt d pl (cp.put s.world.chans.length o.opening.record.toNat) o.value.toNat
      (.channel s.world.chans.length) := by
    refine ⟨?_, ?_, ?_⟩
    · change HeaderOk (bytesT d.σ.mem (o.value.toNat - 8) 8) _ _
      rw [o.header]; exact Gc.customHeader_ok
    · change (bytesT d.σ.mem o.value.toNat 8).toNat = _
      rw [o.ops]; rfl
    · change _ = some (bytesT d.σ.mem (o.value.toNat + 8) 8).toNat
      rw [o.channel, ChanPlace.put_self]
  have outside : AllocationOutside P s pl o.value.toNat (.channel s.world.chans.length) := by
    intro l b old _ hb found
    have free := g.nursery.heap l b old hb found
    have bl := g.toStackGeometry.heapLow l b old hb found
    simp only [OutWRange, Gc.nurseryFree, and_true] at free
    show o.value.toNat + 8 * 2 ≤ b - 8 ∨ b + 8 * old.wosize ≤ o.value.toNat - 8
    omega
  have record := OutRecord.chanAt o.record fdWord open_ o.opening.high o.opening.align
  exact VmPayload.openChan kept (openChan_fresh ok) placed layout outside record

end OCaml.Vm.Sim
