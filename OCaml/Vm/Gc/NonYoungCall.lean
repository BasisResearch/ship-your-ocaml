import OCaml.Vm.Gc.OldifyNonYoung
import OCaml.Vm.Gc.OldifyCallSeams
import OCaml.Vm.Gc.NativeRestore
import OCaml.Vm.Gc.OldifyReturned

/-! # `caml_oldify_one` on a pointer outside the nursery

The whole call for an even value that is not strictly young: the real
prologue (eleven saves), the nursery tests rejecting it, and the shared native
restore, root store `*p = v` and return (`StoreReturn`). Composed from
`OldifyEntry.entry_machine`, `OldifyYoung.nonYoung_machine` and
`StoreReturn.finish`; the result is `OldifyReturned` plus the root value. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

namespace OldifyEntry

/-- The nursery tests' input from the prologue, without the young bounds. -/
theorem Post.read_input {R domain before after} (post : Post R before after)
    (root : word before Layout.sym_Caml_state = domain)
    (windows : Young.Windows domain) (outside : DomainOutside R domain) :
    OldifyYoung.ReadInput (R 10) domain after where
  good := post.machine.good
  minstret := post.machine.minstret
  tick := post.machine.tick
  code := post.code
  registers := ⟨gholds_lookup _ post.registers rfl, gholds_lookup _ post.registers rfl, True.intro⟩
  root := (post.word_unchanged outside.root).trans root
  windows := windows

/-- The root destination and stack pointer survive the rejecting tests. -/
theorem carried_after_reject {R value domain before after}
    (post : OldifyYoung.Rejected value domain before after) (holds : GHolds before.σ (carried R)) :
    GHolds after.σ (carried R) := by
  apply gholds_of_frame post.machine.frame _ (by change KeysOK [9,2]; decide) ?_ ?_ holds
  · change ∀ n ∈ [9,2], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · intro n hn m hm
    have small := OldifyYoung.reject_written (OldifyYoung.passesUpper value domain before) m hm
    simp only [carried, keysG, List.map, List.mem_cons, List.not_mem_nil, or_false] at hn small
    rcases hn with rfl | rfl <;> rcases small with rfl | rfl | rfl <;> decide

end OldifyEntry

namespace NonYoung

/-- Geometry and values of a non-young call: the young interval read from
the domain record excludes the value; the root is writable and apart from the
native save bank; the return address is aligned. -/
structure Conditions (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop where
  root : word c Layout.sym_Caml_state = domain
  domainWindows : Young.Windows domain
  domainOutside : OldifyEntry.DomainOutside R domain
  notYoung : ¬ ((Young.lowerWord domain c).toNat < (R 10).toNat ∧ (R 10).toNat < (Young.upperWord domain c).toNat)
  rootWrite : WriteWindow (R 11) 8
  rootOutside : ∀ off ∈ OldifyReturn.offsets,
    (R 11).toNat + 8 ≤ (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat ∨
      (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat + 8 ≤ (R 11).toNat
  aligned : (R 1).toNat % 4 = 0

structure Input (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop
    extends Conditions R domain c where
  entry : OldifyEntry.Input R c

/-- The call's memory effect: the native saves, then the root store. -/
def effect (R : Nat → BitVec 64) : List WEntry :=
  OldifyEntry.saveLog OldifyEntry.saves R ++ [((R 11).toNat, 8, R 10)]

/-- The non-young call returned: the common return, and the root holds the value. -/
structure Post (R : Nat → BitVec 64) (before after : Config) : Prop
    extends OldifyReturned R (effect R) before after where
  root : word after (R 11).toNat = R 10

theorem store_offsets : ∀ off ∈ StoreReturn.offsets, ∃ cell ∈ OldifyEntry.saves, cell.2 = off := by decide

theorem return_offsets : ∀ cell ∈ StoreReturn.returnSlots, cell.2 ∈ OldifyReturn.offsets := by decide

/-- **`caml_oldify_one` on a non-young pointer**, entry to return. -/
theorem call {R domain c} (input : Input R domain c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (Post R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (OldifyEntry.entry_machine input.entry).run
  intro entered entry
  have read := entry.read_input input.root input.domainWindows input.domainOutside
  have notYoung : ¬ ((Young.lowerWord domain entered).toNat < (R 10).toNat ∧
      (R 10).toNat < (Young.upperWord domain entered).toNat) := by
    simpa only [Young.lowerWord, Young.upperWord, entry.word_unchanged input.domainOutside.lower,
      entry.word_unchanged input.domainOutside.upper] using input.notYoung
  apply Vsa.Logic.Triple.seq (OldifyYoung.nonYoung_machine read notYoung).run
  case a => exact ⟨entry.pc, rfl⟩
  intro rejected rej
  have carried := OldifyEntry.carried_after_reject rej entry.carried
  have saved : ∀ cell ∈ OldifyEntry.saves,
      word rejected (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1 := by
    intro cell member
    simpa only [word, rej.memory] using entry.saved input.entry cell member
  have ra : StoreReturn.returnWord (OldifyEntry.frameSp R) rejected = R 1 := by
    simpa only [StoreReturn.returnWord, OldifyReturn.returnWord, word, rej.memory] using
      entry.returnWord input.entry
  have storeInput : StoreReturn.Input (OldifyEntry.frameSp R) (R 10) (R 11) rejected :=
    { good := rej.machine.good
      tick := rej.machine.tick
      minstret := rej.machine.minstret
      code := rej.code
      registers := ⟨gholds_lookup _ carried rfl, rej.value, gholds_lookup _ carried rfl, True.intro⟩
      windows :=
        { stack := fun off member => by
            obtain ⟨cell, hc, rfl⟩ := store_offsets off member
            exact (input.entry.windows cell hc).read
          destination := input.rootWrite
          outside := fun cell member => ⟨Or.symm (input.rootOutside cell.2 (return_offsets cell member)), True.intro⟩ }
      aligned := by rw [ra]; exact input.aligned }
  obtain ⟨after, run, post⟩ := (StoreReturn.finish storeInput).run rejected ⟨rej.pc, rfl⟩
  refine ⟨after, run, ⟨⟨post.machine.good, post.machine.minstret, post.machine.tick, post.code, ?_,
    StoreReturn.original_caller saved post.registers, ?_,
    (post.machine.output.trans rej.machine.output).trans entry.machine.output, ?_⟩, post.value⟩⟩
  · simpa only [ra] using post.pc
  · rw [post.memory, rej.memory, entry.memory, effect, writeLog_append]
    rfl
  · intro r noise gprs
    have store : ∀ n ∈ wrChain StoreReturn.blocks, n < 32 := by decide
    have prologue : ∀ n ∈ wrChain OldifyEntry.blocks, n < 32 := by decide
    have reject : ∀ n ∈ wrChain (OldifyYoung.rejectBlocks (OldifyYoung.passesUpper (R 10) domain entered)), n < 32 :=
      fun n hn => by
        have h := OldifyYoung.reject_written _ n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        omega
    exact ((post.machine.frame r noise fun n hn => gprs n (store n hn)).trans
      (rej.machine.frame r noise fun n hn => gprs n (reject n hn))).trans
      (entry.machine.frame r noise fun n hn => gprs n (prologue n hn))

end NonYoung
end OCaml.Vm.Gc
