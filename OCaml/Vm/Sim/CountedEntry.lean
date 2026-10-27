import OCaml.Vm.Gc.ChannelCustomCount
import OCaml.Vm.Sim.CountedInvariant
import OCaml.Vm.Sim.ChannelCountFrame
import OCaml.Vm.Sim.EntryF1

/-! The actual interpreter prologue carries the concrete startup table-count
component to the counted loop relation. No additional machine/frame supplier
is used. This does not yet instantiate the full physical runtime predicate
needed by `CustomMemCall`; see `ChannelCustomCount`. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The named custom runtime's footprint also frames a complete physical
accounting predicate through the actual prologue, independently of which
concrete predicate its eventual supplier selects. -/
theorem EntryFrame.customCountFrame {c d : Config} {pl : Place}
    {sp : Nat} {regs : Nat → BitVec 64}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (frame : EntryFrame sp)
    (dom : (word c Layout.sym_Caml_state).toNat = Gc.f1Domain)
    (memory : d.σ.mem = writeLog c.σ.mem (entryLog sp regs (BitVec.ofNat 64 pl.codeBase) c)) :
    Gc.CustomCountStep Customs c d 0 := by
  have cover := entryLog_cover (regs := regs) (a0 := BitVec.ofNat 64 pl.codeBase) (c := c) frame
  have outside (a : Nat) (at_ : state c a) :
      OutLRange (entryLog sp regs (BitVec.ofNat 64 pl.codeBase) c) a 1 := by
    apply outLRange_of_cover cover
    have apart := custom.apart c a at_
    have low := apart.belowStack
    have static := apart.static
    have domain := apart.domainField
    obtain ⟨lo, hi, aligned⟩ := frame.nat
    simp only [Gc.domainAddr, dom, Gc.f1Domain, Boot.WhileMinRuntime.domain,
      VsaIris.InExt, Layout.off_extra_heap_resources_minor, Layout.domainStateBytes,
      Layout.sym_caml_extra_heap_resources, Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at *
    simp only [OutLRange, entryFootprint, dom, Gc.f1Domain, Boot.WhileMinRuntime.domain,
      Layout.off_external_raise, interpFrame, Layout.interpFrameBytes,
      Layout.sym_caml_callback_depth, and_true]
    omega
  constructor
  intro n physical
  simpa only [Nat.add_zero] using custom.accounting.frame physical
    (fun a at_ => by rw [memory, writeLog_out _ _ _
      (outL_of_range (outside a at_) (Nat.le_refl a) (by omega))])
    (word_of_log memory (outLRange_of_cover cover (by
      obtain ⟨lo, hi, aligned⟩ := frame.nat
      have domainAbove : Layout.sym_Caml_state + 8 ≤
          (word c Layout.sym_Caml_state).toNat + Layout.off_external_raise := by
        rw [dom]; decide
      simp only [OutLRange, entryFootprint, interpFrame, Layout.interpFrameBytes,
        Layout.sym_caml_callback_depth, Layout.sym_Caml_state, and_true] at domainAbove ⊢
      omega)))

/-- Attach any complete physical count to entry's retained placement using
the same whole-record and opened-head frame as the loaded payload. -/
theorem EntryLoopPost.counted {P : Prog} {c d : Config} {pl : Place} {cp : ChanPlace}
    {high sp : Nat} {regs saved : Nat → BitVec 64} {Customs : Config → Nat → Prop}
    (post : EntryLoopPost Gc.f1Layout P c pl cp high sp regs d)
    (caller : InterpCaller P c pl cp high sp regs saved)
    (counts : ChannelCustomsRepr Customs c cp P.init.world)
    (physical : Gc.CustomCountStep Customs c d 0) :
    CountedLoopAt Customs Gc.f1Layout P P.init d := by
  have outside := caller.outside.cover (entryLog_cover (regs := regs)
    (a0 := BitVec.ofNat 64 pl.codeBase) (c := c) (EntryFrame.of_caller caller))
  have counted := (ChannelCountFrame.of_log outside.channels outside.openHead post.memory physical).repr counts
  exact ⟨{ toRunning := post.toRunning, countedStack :=
    ⟨pl, cp, high, high, { post.represented with counts := counted }, post.geometry⟩ }, post.clock⟩

/-- Complete physical accounting is carried through the actual prologue
using only the accepted named custom machine premise's existing frame. The
initial count itself must be supplied by startup, never by `Loaded` alone. -/
theorem counted_entry_of_custom {P : Prog} {c : Config} {pl : Place} {cp : ChanPlace}
    {high sp : Nat} {regs saved : Nat → BitVec 64}
    {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs)
    (h : OCaml.LoadedAt Gc.f1Layout P c pl cp high)
    (caller : InterpCaller P c pl cp high sp regs saved)
    (counts : ChannelCustomsRepr Customs c cp P.init.world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Customs Gc.f1Layout P P.init after := by
  have dom := Gc.f1_domain h.platform.runtime
  have frame := EntryFrame.of_caller caller
  obtain ⟨after, run, post⟩ := entry_loopAt_framed h caller h.geometry
    (by rw [dom]; exact f1_entryStable frame)
  exact ⟨after, run, post.counted caller counts (frame.customCountFrame custom dom post.memory)⟩

/-- Entry's actual stores miss the custom table's two count words. -/
theorem EntryFrame.customCount {c d : Config} {pl : Place}
    {sp : Nat} {regs : Nat → BitVec 64} (frame : EntryFrame sp)
    (dom : (word c Layout.sym_Caml_state).toNat = Gc.f1Domain)
    (memory : d.σ.mem = writeLog c.σ.mem (entryLog sp regs (BitVec.ofNat 64 pl.codeBase) c)) :
    Gc.CustomCountStep Gc.ChannelCustomCount c d 0 := by
  constructor
  intro n count
  simpa only [Nat.add_zero] using count.frame (fun a foot => by
    have outside : OutLRange (entryLog sp regs (BitVec.ofNat 64 pl.codeBase) c) a 1 := by
      apply outLRange_of_cover (entryLog_cover frame)
      obtain ⟨low, high, aligned⟩ := frame.nat
      simp only [Gc.ChannelCustomCountFoot, Boot.WhileMinRuntime.customTable,
        Layout.off_custom_table_base, Layout.off_custom_table_ptr] at foot
      simp only [OutLRange, entryFootprint, dom, Gc.f1Domain, Boot.WhileMinRuntime.domain,
        Layout.off_external_raise, interpFrame, Layout.interpFrameBytes,
        Layout.sym_caml_callback_depth, and_true]
      omega
    exact (outsideLog_of_observedLog (by rw [memory]; intro a; rfl)) a
      (outL_of_range outside (Nat.le_refl a) (by omega)))

/-- The shared native entry execution retains complete counts at the same
placement used by its ordinary stack witness. -/
theorem counted_entry_loopAt {P : Prog} {c : Config} {pl : Place} {cp : ChanPlace}
    {high sp : Nat} {regs saved : Nat → BitVec 64}
    (h : OCaml.LoadedAt Gc.f1Layout P c pl cp high)
    (caller : InterpCaller P c pl cp high sp regs saved)
    (counts : ChannelCustomsRepr Gc.ChannelCustomCount c cp P.init.world) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Gc.ChannelCustomCount Gc.f1Layout P P.init after := by
  have dom := Gc.f1_domain h.platform.runtime
  have frame := EntryFrame.of_caller caller
  obtain ⟨after, run, post⟩ := entry_loopAt_framed h caller h.geometry
    (by rw [dom]; exact f1_entryStable frame)
  exact ⟨after, run, post.counted caller counts (frame.customCount dom post.memory)⟩

/-- Concrete startup reads supply the count before the actual prologue. The
general loaded-state predicate does not imply this memory observation. -/
theorem f1_counted_entry {P : Prog} {c : Config} (h : OCaml.Loaded Gc.f1Layout P c)
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem Boot.WhileMinImage.initialMem Boot.WhileMinLog.log)) :
    ∃ after, OCaml.Plus c after ∧ CountedLoopAt Gc.ChannelCustomCount Gc.f1Layout P P.init after := by
  obtain ⟨pl, cp, high, loaded⟩ := h
  obtain ⟨sp, regs, saved, caller⟩ := loaded.caller
  exact counted_entry_loopAt loaded caller (Gc.channelCustoms_startup memory rfl)

/-- The captured whileMin entry establishes the counted loop relation for
the table-count component from its actual zero witness and the closed
allocator certificate. Full custom runtime accounting remains open. -/
theorem whileMin_counted_entry :
    ∃ after, OCaml.Plus Boot.WhileMin.cut after ∧
      CountedLoopAt Gc.ChannelCustomCount Gc.f1Layout OCaml.Programs.whileMin
        OCaml.Programs.whileMin.init after :=
  f1_counted_entry Gc.whileMin_loaded_f1 Boot.WhileMin.memory_equiv

/-- Contract obstruction: table occupancy permits every resource-accumulator
word. Thus its checked startup zero does not by itself supply the physical
runtime predicate needed for quiet custom calls. No reachability claim. -/
theorem table_count_resources_unconstrained {c : Config} {n : Nat}
    (count : Gc.ChannelCustomCount c n) (value : BitVec 64) :
    ∃ d, Gc.ChannelCustomCount d n ∧ word d Layout.sym_caml_extra_heap_resources = value := by
  let log : List WEntry := [(Layout.sym_caml_extra_heap_resources, 8, value)]
  let d : Config := { c with σ := { c.σ with mem := writeLog c.σ.mem log } }
  have memory : d.σ.mem = writeLog c.σ.mem log := rfl
  refine ⟨d, count.frame (fun a foot => ?_), ?_⟩
  · have outside : OutL log a := by
      simp only [Gc.ChannelCustomCountFoot, Boot.WhileMinRuntime.customTable,
        Layout.off_custom_table_base, Layout.off_custom_table_ptr] at foot
      simp only [log, OutL, Layout.sym_caml_extra_heap_resources, and_true]
      omega
    rw [byte_total, byte_total, memory, writeLog_out _ _ _ outside]
  · change bytesT (writeLog c.σ.mem log) Layout.sym_caml_extra_heap_resources 8 = value
    exact Gc.word_writeLog_at c.σ.mem log 0 Layout.sym_caml_extra_heap_resources value rfl (by trivial)

end OCaml.Vm.Sim
