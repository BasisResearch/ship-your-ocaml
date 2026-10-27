import OCaml.Vm.Repr.ChannelCounts
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Sim.LogWindow

/-! The shared frame for physical customs, natural channel refcounts and list
links. A physical count alone does not reconstruct the boundary invariant. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Observations a non-custom span must preserve, independently of its opcode.
The physical component comes from `CustomMemCall.accounting.frame`; the other
components use the same whole-record frame as the ordinary VM payload. -/
structure ChannelCountFrame (Customs : Config → Nat → Prop) (cp : ChanPlace)
    (w : World) (c d : Config) : Prop where
  physical : Gc.CustomCountStep Customs c d 0
  references : ∀ id ch a, w.chans[id]? = some ch → cp id = some a →
    Gc.chanRefs d.σ.mem a = Gc.chanRefs c.σ.mem a
  links : Gc.ChannelLinksKept c.σ.mem d.σ.mem (Gc.placedChannels cp w.chans.length)

/-- Reconstruct all three boundary components from one shared frame. -/
theorem ChannelCountFrame.repr {Customs : Config → Nat → Prop} {cp : ChanPlace}
    {w : World} {c d : Config} (frame : ChannelCountFrame Customs cp w c d)
    (before : ChannelCustomsRepr Customs c cp w) : ChannelCustomsRepr Customs d cp w := by
  refine ⟨⟨?_⟩, frame.links.opened before.opened, ?_⟩
  · intro id ch at_
    obtain ⟨a, placed, refs⟩ := before.references.refs id ch at_
    exact ⟨a, placed, (frame.references id ch a at_ placed).trans refs⟩
  · simpa only [Nat.add_zero] using frame.physical.count before.physical

/-- Register-only spans share the physical and channel frame. -/
theorem ChannelCountFrame.sameMemory {Ready : Nat → Config → Prop}
    {state Customs : Config → Nat → Prop} {cp : ChanPlace} {w : World} {c d : Config}
    (accounting : Gc.CustomAccounting Ready state Customs) (memory : d.σ.mem = c.σ.mem) :
    ChannelCountFrame Customs cp w c d := by
  exact ⟨accounting.sameMemory memory, fun _ _ _ _ _ => by rw [memory],
    ⟨by rw [memory], fun _ _ => by rw [memory]⟩⟩

/-- Whole-record payload separation also frames refcounts and list links.
Physical state separation is supplied by the independent custom-state frame. -/
theorem ChannelCountFrame.of_log {Customs : Config → Nat → Prop} {s : St}
    {cp : ChanPlace} {c d : Config} {log : List WEntry}
    (records : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
      OutLRange log a (chanOffBuff + ioBufferSize))
    (head : OutLRange log Layout.sym_caml_all_opened_channels 8)
    (memory : d.σ.mem = writeLog c.σ.mem log)
    (physical : Gc.CustomCountStep Customs c d 0) :
    ChannelCountFrame Customs cp s.world c d := by
  have record (id : Nat) (ch : Chan) (a off n : Nat)
      (at_ : s.world.chans[id]? = some ch) (placed : cp id = some a)
      (bound : off + n ≤ chanOffBuff + ioBufferSize) :
      bytesT d.σ.mem (a + off) n = bytesT c.σ.mem (a + off) n := by
    rw [memory]
    exact bytesT_writeLog_out _ (outLRange_subrange (records id ch a at_ placed)
      (by omega) (by omega))
  refine ⟨physical, ?_, ⟨?_, ?_⟩⟩
  · intro id ch a at_ placed
    exact congrArg BitVec.toNat (record id ch a chanOffRefcount 4 at_ placed (by decide))
  · rw [memory]
    exact bytesT_writeLog_out _ head
  · intro a member
    obtain ⟨id, member, placed⟩ := List.mem_filterMap.mp member
    have bound : id < s.world.chans.length := List.mem_range.mp (List.mem_reverse.mp member)
    exact record id s.world.chans[id] a Gc.chanOffNext 8
      (List.getElem?_eq_getElem bound) placed (by decide)

end OCaml.Vm.Sim
