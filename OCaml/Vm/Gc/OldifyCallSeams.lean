import OCaml.Vm.Gc.OldifyYoung
import OCaml.Vm.Gc.OldifySaved
import Vsa.Sim.GRegsFrame

namespace OCaml.Vm.Gc.OldifyEntry
open Vsa.Machine Vsa.Sim Primitives

/-- Three runtime observations used by the nursery tests lie outside the
native save bank. The caller's stack/domain geometry supplies these bounds. -/
structure DomainOutside (R : Nat → BitVec 64) (domain : BitVec 64) : Prop where
  root : OutLRange (saveLog saves R) Layout.sym_Caml_state 8
  lower : OutLRange (saveLog saves R) (domain + BitVec.ofNat 64 Layout.off_young_start).toNat 8
  upper : OutLRange (saveLog saves R) (domain + BitVec.ofNat 64 Layout.off_young_end).toNat 8

theorem Post.word_unchanged {R before after a} (post : Post R before after)
    (outside : OutLRange (saveLog saves R) a 8) : word after a = word before a := by
  change bytesT after.σ.mem a 8 = _
  rw [post.memory, bytesT_writeLog_out _ outside]
  rfl

theorem Post.young_input {R domain before after} (post : Post R before after)
    (root : word before Layout.sym_Caml_state = domain)
    (windows : Young.Windows domain) (outside : DomainOutside R domain)
    (lower : (Young.lowerWord domain before).toNat < (R 10).toNat)
    (upper : (R 10).toNat < (Young.upperWord domain before).toNat) :
    OldifyYoung.Input (R 10) domain after := by
  refine {
    good := post.machine.good
    minstret := post.machine.minstret
    tick := post.machine.tick
    code := post.code
    registers := ?_
    root := (post.word_unchanged outside.root).trans root
    windows := windows
    lower := ?_
    upper := ?_ }
  · exact ⟨gholds_lookup _ post.registers rfl, gholds_lookup _ post.registers rfl, True.intro⟩
  · simpa only [Young.lowerWord, post.word_unchanged outside.lower] using lower
  · simpa only [Young.upperWord, post.word_unchanged outside.upper] using upper

/-- The same decoded native slots serve every oldify return path. -/
theorem Input.return_windows {R c} (input : Input R c) :
    ∀ off ∈ OldifyReturn.offsets, ReadWindow (frameSp R + BitVec.ofNat 64 off) 8 := by
  intro off member
  rw [OldifyReturn.offsets_eq] at member
  obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp member
  exact (input.windows cell (restore_slots cell hc)).read

/-- Carry the root destination and stack pointer through the nursery tests. -/
def carried (R : Nat → BitVec 64) : GRegs := [(9, R 11), (2, frameSp R)]

theorem Post.carried {R before after} (post : Post R before after) : GHolds after.σ (carried R) :=
  ⟨gholds_lookup _ post.registers rfl, gholds_lookup _ post.registers rfl, True.intro⟩

theorem carried_after_young {R value domain before after}
    (post : OldifyYoung.Post value domain before after) (holds : GHolds before.σ (carried R)) :
    GHolds after.σ (carried R) := by
  apply gholds_of_frame post.machine.frame _ (by change KeysOK [9,2]; decide) ?_ ?_ holds
  · change ∀ n ∈ [9,2], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · have safe : ∀ n ∈ [9,2], ∀ m ∈ [14,15,25], (gprReg m == gprReg n) = false := by decide
    intro n hn m hm
    exact safe n hn m (OldifyYoung.written m hm)

end OCaml.Vm.Gc.OldifyEntry
