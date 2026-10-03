import OCaml.Vm.Gc.OldifyCallSeams
import OCaml.Vm.Gc.ForwardedReturn

namespace OCaml.Vm.Gc.ForwardedCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Whole already-forwarded call input. The caller supplies disjoint native,
nursery, root and domain windows; all saved values are established by the
real prologue, rather than supplied as scalar-load or callee-run premises. -/
structure Input (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop where
  entry : OldifyEntry.Input R c
  root : word c Layout.sym_Caml_state = domain
  domainWindows : Young.Windows domain
  domainOutside : OldifyEntry.DomainOutside R domain
  lower : (Young.lowerWord domain c).toNat < (R 10).toNat
  upper : (R 10).toNat < (Young.upperWord domain c).toNat
  header : word c (R 10 - 8#64).toNat = 0
  headerRead : ReadWindow (R 10 - 8#64) 8
  sourceRead : ReadWindow (R 10) 8
  rootWrite : WriteWindow (R 11) 8
  headerOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) (R 10 - 8#64).toNat 8
  sourceOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) (R 10).toNat 8
  rootOutside : ∀ off ∈ OldifyReturn.offsets,
    (R 11).toNat + 8 ≤ (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat ∨
      (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat + 8 ≤ (R 11).toNat
  aligned : (R 1).toNat % 4 = 0

def effect (R : Nat → BitVec 64) (c : Config) : List WEntry :=
  OldifyEntry.saveLog OldifyEntry.saves R ++ [((R 11).toNat, 8, word c (R 10).toNat)]

def writes : List Nat := wrChain OldifyEntry.blocks ++ wrChain OldifyYoung.blocks ++
  (wrChain Forwarded.blocks ++ wrChain OldifyReturn.blocks)

/-- A complete oldify invocation on an already-forwarded young argument.
The caller registers and return PC are original entry values. The only
stores are the native save bank and the updated caller root. -/
structure Post (R : Nat → BitVec 64) (before after : Config) (exitPC : BitVec 64 := R 1) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem (effect R before)
  root : word after (R 11).toNat = word before (R 10).toNat
  pc : PCAt exitPC after
  registers : GHolds after.σ (OldifyEntry.callerRegs R)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem after_entry {R domain before entered} (input : Input R domain before)
    (entry : OldifyEntry.Post R before entered) :
    FnSummary OldifyYoung.pc (fun d => d = entered) (Post R before) := by
  have young := entry.young_input input.root input.domainWindows input.domainOutside input.lower input.upper
  constructor
  apply Vsa.Logic.Triple.seq (OldifyYoung.young_machine young).run
  intro ranged range
  have carried := OldifyEntry.carried_after_young range entry.carried
  have source : word ranged (R 10).toNat = word before (R 10).toNat := by
    simpa only [word, range.memory] using entry.word_unchanged input.sourceOutside
  have header : word ranged (R 10 - 8#64).toNat = 0 := by
    simpa only [word, range.memory] using (entry.word_unchanged input.headerOutside).trans input.header
  have ra : OldifyReturn.returnWord (OldifyEntry.frameSp R) ranged = R 1 := by
    simpa only [OldifyReturn.returnWord, range.memory] using entry.returnWord input.entry
  have restore : OldifyReturn.restored (OldifyEntry.frameSp R) ranged = OldifyEntry.callerRegs R := by
    simpa only [OldifyReturn.restored, range.memory] using entry.restored_caller input.entry
  have copiedInput : Forwarded.Input (R 10) (R 11) ranged :=
    ⟨range.machine.good, range.machine.minstret, range.machine.tick, range.code,
      ⟨gholds_lookup _ range.registers rfl, gholds_lookup _ carried rfl, True.intro⟩,
      header, input.headerRead, input.sourceRead, input.rootWrite⟩
  have stack : gprGet ranged.σ 2 = some (OldifyEntry.frameSp R) := gholds_lookup _ carried rfl
  have outside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange [((R 11).toNat, 8, word ranged (R 10).toNat)]
        (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat 8 := by
    intro off member
    exact ⟨Or.symm (input.rootOutside off member), True.intro⟩
  have aligned : (OldifyReturn.returnWord (OldifyEntry.frameSp R) ranged).toNat % 4 = 0 := by
    rw [ra]; exact input.aligned
  obtain ⟨after, run, returned⟩ :=
    (Forwarded.forwarded_return copiedInput stack input.entry.return_windows outside aligned).run
      ranged ⟨range.pc, rfl⟩
  refine ⟨after, run, ⟨returned.good, returned.minstret, returned.tick, returned.code,
    ?_, returned.rootWord.trans source, ?_, ?_,
    (returned.output.trans range.machine.output).trans entry.machine.output, ?_⟩⟩
  · rw [returned.memory, source, range.memory, entry.memory, ← writeLog_append]
    rfl
  · simpa only [ra] using returned.pc
  · simpa only [restore] using returned.registers
  · intro r noise untouched
    have left : ∀ n ∈ wrChain OldifyEntry.blocks, (gprReg n == r) = false :=
      fun n hn => untouched n (List.mem_append_left _ (List.mem_append_left _ hn))
    have middle : ∀ n ∈ wrChain OldifyYoung.blocks, (gprReg n == r) = false :=
      fun n hn => untouched n (List.mem_append_left _ (List.mem_append_right _ hn))
    have right : ∀ n ∈ wrChain Forwarded.blocks ++ wrChain OldifyReturn.blocks, (gprReg n == r) = false :=
      fun n hn => untouched n (List.mem_append_right _ hn)
    exact ((returned.native r noise right).trans (range.machine.frame r noise middle)).trans
      (entry.machine.frame r noise left)

/-- Whole generated-machine call, including prologue, nursery checks,
forwarded root update and native return, composed only through the kernel. -/
theorem forwarded_call {R domain c} (input : Input R domain c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (Post R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (OldifyEntry.entry_machine input.entry).run
  intro entered entry
  exact (after_entry input entry).run entered ⟨entry.pc, rfl⟩

/-- Every store in the whole-call log obeys the same above-HTIF policy as
the underlying scalar instructions. Stored register values are irrelevant. -/
theorem Input.effect_high {R domain c} (input : Input R domain c) :
    ∀ e ∈ effect R c, tohostAddr ≤ e.1 := by
  intro e member
  rcases List.mem_append.mp member with saved | root
  · obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp saved
    have high := (input.entry.windows cell hc).htif
    simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using
      Nat.le_trans (Nat.le_add_right Layout.sym_tohost 16) high
  · have same : e = ((R 11).toNat, 8, word c (R 10).toNat) := List.mem_singleton.mp root
    subst e
    have high := input.rootWrite.htif
    simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using
      Nat.le_trans (Nat.le_add_right Layout.sym_tohost 16) high

theorem Post.mopupCode {R domain before after exitPC} (post : Post R before after exitPC)
    (input : Input R domain before) (code : Code.Caml_oldify_mopupLoaded before.σ.mem) :
    Code.Caml_oldify_mopupLoaded after.σ.mem := by
  rw [post.memory]
  apply image_writeLog Code.caml_oldify_mopup_transport code
  intro e member
  exact Nat.le_trans (by decide : (0x80009f08 : Nat) ≤ tohostAddr) (input.effect_high e member)

end OCaml.Vm.Gc.ForwardedCall
