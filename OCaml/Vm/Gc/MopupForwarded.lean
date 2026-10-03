import OCaml.Vm.Gc.Generated.MopupCall
import OCaml.Vm.Gc.ForwardedCall

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Every oldify input register except ra, which the JAL supplies. -/
def carried (R : Nat → BitVec 64) : GRegs :=
  [(2,R 2),(8,R 8),(9,R 9),(10,R 10),(11,R 11),(18,R 18),(19,R 19),
   (20,R 20),(21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

def linked (R : Nat → BitVec 64) (n : Nat) : BitVec 64 := if n = 1 then call.link else R n

theorem carried_regs {R} {c : Config} (holds : GHolds c.σ (OldifyEntry.regs R)) : GHolds c.σ (carried R) := by
  apply gholds_select holds
  intro n v member
  simp only [carried, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem linked_regs {R before after}
    (post : SegCallFacts [] (carried R) [] call.target call.link before after) :
    GHolds after.σ (OldifyEntry.regs (linked R)) := by
  have holds : GHolds after.σ ((1,call.link) :: carried R) := ⟨post.ra, post.registers⟩
  apply gholds_select holds
  intro n v member
  simp only [OldifyEntry.regs, OldifyEntry.entryKeys, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

/-- JAL changes ra and preserves memory. Transfer only concrete callee input
facts; the complete callee execution is supplied by forwarded_call. -/
theorem linked_input {R domain before after} (input : ForwardedCall.Input R domain before)
    (post : SegCallFacts [] (carried R) [] call.target call.link before after) :
    ForwardedCall.Input (linked R) domain after := by
  have memory : after.σ.mem = before.σ.mem := post.mem
  refine {
    entry := {
      good := post.good
      minstret := post.minstret
      tick := post.tick
      code := memory ▸ input.entry.code
      registers := linked_regs post
      windows := input.entry.windows
      even := input.entry.even }
    root := ?_
    domainWindows := input.domainWindows
    domainOutside := ⟨input.domainOutside.root, input.domainOutside.lower, input.domainOutside.upper⟩
    lower := ?_
    upper := ?_
    header := ?_
    headerRead := input.headerRead
    sourceRead := input.sourceRead
    rootWrite := input.rootWrite
    headerOutside := input.headerOutside
    sourceOutside := input.sourceOutside
    rootOutside := input.rootOutside
    aligned := by change call.link.toNat % 4 = 0; decide }
  · simpa only [word, memory] using input.root
  · change (Young.lowerWord domain after).toNat < (R 10).toNat
    simpa only [Young.lowerWord, word, memory] using input.lower
  · change (R 10).toNat < (Young.upperWord domain after).toNat
    simpa only [Young.upperWord, word, memory] using input.upper
  · change word after (R 10 - 8#64).toNat = 0
    simpa only [word, memory] using input.header

structure ForwardedPost (R : Nat → BitVec 64) (before after : Config) : Prop where
  body : ForwardedCall.Post (linked R) before after
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem forwarded {R domain c} (input : ForwardedCall.Input R domain c)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) :
    FnSummary call.pc (fun d => d = c) (ForwardedPost R c) := by
  have jump := call_summary call_shape call_decode c (call_pins code) input.entry.good
    input.entry.tick input.entry.minstret (carried R) (carried_regs input.entry.registers)
    (by change KeysOK [2,8,9,10,11,18,19,20,21,22,23,24,25]; decide)
    (by change ∀ n ∈ ([2,8,9,10,11,18,19,20,21,22,23,24,25] : List Nat), n ≠ 1; decide)
  constructor
  apply Vsa.Logic.Triple.seq jump.run
  intro entered called
  have memory : entered.σ.mem = c.σ.mem := called.mem
  have calleeInput := linked_input input called
  have pc : PCAt OldifyEntry.pc entered := by simpa only [PCAt, call_target] using called.pc
  obtain ⟨after, run, returned⟩ := (ForwardedCall.forwarded_call calleeInput).run entered ⟨pc,rfl⟩
  refine ⟨after, run, ⟨?_, returned.mopupCode calleeInput (memory ▸ code)⟩⟩
  refine ⟨returned.good, returned.minstret, returned.tick, returned.code, ?_, ?_, returned.pc,
    returned.registers, returned.output.trans called.output, ?_⟩
  · simpa only [ForwardedCall.effect, word, memory] using returned.memory
  · simpa only [word, memory] using returned.root
  · intro r noise untouched
    apply (returned.native r noise untouched).trans
    apply called.frame r noise (by simp [wrChain])
    exact untouched 1 (by decide)

/-- Callee-saved native registers; the JAL deliberately replaces ra. -/
def preserved (R : Nat → BitVec 64) : GRegs :=
  [(2,R 2),(8,R 8),(9,R 9),(18,R 18),(19,R 19),(20,R 20),
   (21,R 21),(22,R 22),(23,R 23),(24,R 24),(25,R 25)]

/-- Two finite pin views used to recover the actual ABI frame. -/
structure PreservedPins (R : Nat → BitVec 64) (before after : Config) : Prop where
  beforePins : GHolds before.σ (preserved R)
  afterPins : GHolds after.σ (preserved R)

theorem preserved_pins {R before after exitPC}
    (post : ForwardedCall.Post (linked R) before after exitPC)
    (registers : GHolds before.σ (OldifyEntry.regs R)) :
    PreservedPins R before after := by
  constructor
  · apply gholds_select registers
    intro n v member
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl
  · apply gholds_select post.registers
    intro n v member
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem abi_frame {R before after exitPC}
    (post : ForwardedCall.Post (linked R) before after exitPC)
    (registers : GHolds before.σ (OldifyEntry.regs R)) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ [1,12,14,15], (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r := by
  have pins := preserved_pins post registers
  apply frame_of_restored post.native (preserved R)
    (by change KeysOK [2,8,9,18,19,20,21,22,23,24,25]; decide) pins.beforePins pins.afterPins
  change ∀ n ∈ ForwardedCall.writes, n ∈ [1,12,14,15] ∨ n ∈ [2,8,9,18,19,20,21,22,23,24,25]
  decide

end OCaml.Vm.Gc.MopupCall
