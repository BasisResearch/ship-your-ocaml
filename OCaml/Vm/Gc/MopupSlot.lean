import OCaml.Vm.Gc.OldifyResume
import OCaml.Vm.Gc.SlotBridge
import OCaml.Vm.Gc.MopupResume
import OCaml.Vm.Gc.Advance

/-! # A mopup `caml_oldify_one` call over any route

Mopup's two call sites (first field, later fields) are `OldifyBridge.Site`s
with a generated return continuation (`Resume`: a jump to the field
advance). `slot_resume` composes the call with a `SlotCall` supplied at the
jumped-to state, for any route (immediate, non-young, forwarded, fresh), and
the continuation; `MopupResume.forwarded_resume` is its forwarded instance
in the older form. -/
namespace OCaml.Vm.Gc.OldifyBridge
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A mopup site as a `SlotSite` over mopup's code image. -/
def Site.toSlot (site : Site) : SlotSite Code.Caml_oldify_mopupLoaded :=
  ⟨site.call, site.shape, site.decode, site.target, site.aligned, site.pins⟩

variable (site : Site) (resume : Resume site)

/-- The call returned through the continuation. -/
structure SlotResumed (R : Nat → BitVec 64) (copies : List PendingCopy) (pl : Place) (before after : Config) : Prop where
  call : ∃ e copies' mid, SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link before e ∧
    SlotDone (site.toSlot.linked R) copies copies' pl e mid ∧ after.σ.mem = mid.σ.mem
  pc : PCAt resume.exit after
  registers : GHolds after.σ (OldifyEntry.callerRegs (site.toSlot.linked R))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v

/-- **A mopup call over any route**, then the return continuation. `kept`:
the callee keeps mopup's code. -/
theorem slot_resume {R : Nat → BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w) (registers : GHolds c.σ (carried R))
    (supply : ∀ e, SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link c e →
      SlotCall (site.toSlot.linked R) copies pl e)
    (kept : ∀ e copies' mid, SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link c e →
      SlotDone (site.toSlot.linked R) copies copies' pl e mid → Code.Caml_oldify_mopupLoaded mid.σ.mem) :
    FnSummary site.call.pc (fun d => d = c) (SlotResumed site resume R copies pl c) := by
  have call := site.toSlot.slot (copies := copies) (pl := pl) code good tick minstret
    (show GHolds c.σ (OldifyBridge.carried R) from registers)
    (fun e called => supply e (by simpa only [Site.toSlot, site.target] using called))
  constructor
  rintro c0 ⟨pc0, rfl⟩
  obtain ⟨mid, run1, ret⟩ := call.run c0 ⟨pc0, rfl⟩
  obtain ⟨e, copies', called, done⟩ := ret.entered
  have called' : SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link c0 e := by
    simpa only [Site.toSlot, site.target] using called
  obtain ⟨log, returned⟩ := done.returned
  have midCode := kept e copies' mid called' done
  have midPc : PCAt resume.entry mid := by
    have h := returned.pc
    simp only [SlotSite.linked, ite_true, Site.toSlot] at h
    rw [← resume.link]; exact h
  let L := OldifyEntry.callerRegs (site.toSlot.linked R)
  have summary := block_summary resume.blocks resume.entry L [] mid
    ⟨returned.good, returned.minstret, returned.registers,
      by change KeysOK [2,9,25,24,23,22,21,20,19,18,8,1]; decide,
      chainPlan_facts (resume.code midCode) (resume.access _ _), resume.shape _, returned.tick⟩
  obtain ⟨after, run2, post⟩ := summary.run mid ⟨midPc, rfl⟩
  have memory : after.σ.mem = mid.σ.mem := by rw [post.memory, resume.log]; rfl
  refine ⟨after, run1.trans run2, ⟨e, copies', mid, called', done, memory⟩, ?_, ?_, post.good, post.tick,
    post.minstret⟩
  · rw [PCAt, post.pc, resume.pc]
  · simpa only [resume.registers] using post.regs

end OCaml.Vm.Gc.OldifyBridge

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A young field's call over any route has returned and the scan advanced. -/
structure SlotAdvanced (R : Nat → BitVec 64) (copies : List PendingCopy) (pl : Place) (before after : Config) :
    Prop where
  call : ∃ e copies' mid, SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link before e ∧
    SlotDone (site.toSlot.linked R) copies copies' pl e mid ∧ after.σ.mem = mid.σ.mem ∧
    PCAt (if FieldCopy.advanceAgain (R 19) (R 9) mid then FieldCopy.pc else FieldCopy.exitPc) after
  registers : GHolds after.σ (FieldCopy.regs (R 8 + 8#64) (R 18) (R 19) (R 9 + 1#64))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

/-- **A young field over any route**: the call, the return continuation and
the header-controlled advance. -/
theorem slot_advance {R : Nat → BitVec 64} {copies : List PendingCopy} {pl : Place} {c : Config}
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w) (registers : GHolds c.σ (carried R))
    (header : ReadWindow (R 19 - 8#64) 8)
    (supply : ∀ e, SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link c e →
      SlotCall (site.toSlot.linked R) copies pl e)
    (kept : ∀ e copies' mid, SegCallFacts [] (carried R) [] OldifyEntry.pc site.call.link c e →
      SlotDone (site.toSlot.linked R) copies copies' pl e mid → Code.Caml_oldify_mopupLoaded mid.σ.mem) :
    FnSummary call.pc (fun d => d = c) (SlotAdvanced R copies pl c) := by
  constructor
  apply Vsa.Logic.Triple.seq (OldifyBridge.slot_resume site resume code good tick minstret registers supply kept).run
  intro middle returned
  obtain ⟨e, copies', mid, called, done, memory⟩ := returned.call
  have midCode : Code.Caml_oldify_mopupLoaded middle.σ.mem := by rw [memory]; exact kept e copies' mid called done
  have input : FieldCopy.AdvanceInput (R 8) (R 18) (R 19) (R 9) middle := by
    refine ⟨returned.good, returned.minstret, returned.tick, midCode, ?_, header⟩
    apply gholds_select returned.registers
    intro n v member
    simp only [FieldCopy.regs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h <;> cases h <;> rfl
  obtain ⟨after, run, advanced⟩ := (FieldCopy.advance_machine input).run middle ⟨returned.pc, rfl⟩
  refine ⟨after, run, ⟨⟨e, copies', mid, called, done, advanced.memory.trans memory, ?_⟩, advanced.registers,
    advanced.machine.good, advanced.machine.tick, advanced.machine.minstret, advanced.code⟩⟩
  have same : FieldCopy.advanceAgain (R 19) (R 9) middle = FieldCopy.advanceAgain (R 19) (R 9) mid := by
    unfold FieldCopy.advanceAgain word
    rw [memory]
  simpa only [same] using advanced.pc

end OCaml.Vm.Gc.MopupCall
