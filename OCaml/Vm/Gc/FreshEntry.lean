import OCaml.Vm.Gc.FreshAccess
import OCaml.Vm.Gc.OldifyCallSeams

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Values retained for allocation and the post-allocation update. Runtime
global addresses come from Layout; tag constants match the decoded prologue. -/
def loopConstants : GRegs :=
  [(18,BitVec.ofNat 64 Layout.sym_Caml_state),(19,maxScannedTag),
   (20,250),(21,249),(22,1),(23,253)]

def allocationCarried (R : Nat → BitVec 64) : GRegs :=
  [(2,OldifyEntry.frameSp R),(9,R 11)] ++ loopConstants

theorem carried_constants {R σ} (holds : GHolds σ (allocationCarried R)) : GHolds σ loopConstants :=
  ((gholds_append _ _).mp holds).2

theorem entry_carried {R before after} (post : OldifyEntry.Post R before after) :
    GHolds after.σ (allocationCarried R) := by
  apply gholds_select post.registers
  intro n v member
  simp only [allocationCarried, loopConstants, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h <;> cases h <;> rfl

/-- Shared finite frame for nursery tests and fresh argument setup. -/
theorem allocation_carried_after {R bs pc regs loads before after}
    (post : BlockPost bs pc regs loads before after)
    (written : ∀ n ∈ wrChain bs, n ∈ [10,11,12,14,15,24,25])
    (holds : GHolds before.σ (allocationCarried R)) : GHolds after.σ (allocationCarried R) := by
  apply gholds_of_frame (post.frame_subset written) _
    (by change KeysOK [2,9,18,19,20,21,22,23]; decide) ?_ ?_ holds
  · change ∀ n ∈ [2,9,18,19,20,21,22,23], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · change ∀ n ∈ [2,9,18,19,20,21,22,23], ∀ m ∈ [10,11,12,14,15,24,25], (gprReg m == gprReg n) = false
    decide

/-- Whole native entry conditions for a fresh scanned object. Header and
domain observations are disjoint from the actual native-save log. -/
structure EntryInput (R : Nat → BitVec 64) (domain : BitVec 64) (size tag : Nat) (c : Config) : Prop where
  entry : OldifyEntry.Input R c
  root : word c Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  domainOutside : OldifyEntry.DomainOutside R domain
  lower : (Young.lowerWord domain c).toNat < (R 10).toNat
  upper : (R 10).toNat < (Young.upperWord domain c).toNat
  headerRead : ReadWindow (R 10 - 8#64) 8
  headerOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) (R 10 - 8#64).toNat 8
  header : HeaderOk (word c (R 10 - 8#64).toNat) size tag
  positive : 0 < size
  scanned : tag < 249

def prepareWrites : List Nat :=
  wrChain OldifyEntry.blocks ++ (wrChain OldifyYoung.blocks ++ wrChain blocks)

/-- Actual native entry through the allocation-call boundary, with complete
saved caller state and exact prologue writes. No allocator run is assumed. -/
structure Prepared (R : Nat → BitVec 64) (before after : Config)
    (exitPC : BitVec 64 := call.pc) (writes : List Nat := prepareWrites) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem (OldifyEntry.saveLog OldifyEntry.saves R)
  pc : PCAt exitPC after
  arguments : GHolds after.σ (Fresh.arguments (R 10) (word before (R 10 - 8#64).toNat))
  carried : GHolds after.σ (allocationCarried R)
  saved : ∀ cell ∈ OldifyEntry.saves,
    word after (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes,
      (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

/-- Real prologue, strict nursery tests and fresh header/tag preparation,
ending at caml_alloc_shr_for_minor_gc's JAL with derived arguments. -/
theorem prepare_entry {R domain size tag c} (input : EntryInput R domain size tag c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (Prepared R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (OldifyEntry.entry_machine input.entry).run
  intro entered entry
  have youngInput := entry.young_input input.root input.windows input.domainOutside input.lower input.upper
  obtain ⟨ranged, rangeRun, range⟩ := (OldifyYoung.young_machine youngInput).run entered ⟨entry.pc,rfl⟩
  have carried := allocation_carried_after range.machine
    (fun n hn => by
      have member := OldifyYoung.written n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide) (entry_carried entry)
  have headerSame : word ranged (R 10 - 8#64).toNat = word c (R 10 - 8#64).toNat := by
    simpa only [word, range.memory] using entry.word_unchanged input.headerOutside
  obtain ⟨nonzero,scanned⟩ := header_conditions input.header input.positive input.scanned
  have freshInput : Input (R 10) ranged :=
    ⟨range.machine.good, range.machine.minstret, range.machine.tick, range.code,
      ⟨gholds_lookup _ range.registers rfl, gholds_lookup _ carried rfl, True.intro⟩,
      input.headerRead, headerSame ▸ nonzero, headerSame ▸ scanned⟩
  obtain ⟨after, freshRun, fresh⟩ := (prepare freshInput).run ranged ⟨range.pc,rfl⟩
  have memory : after.σ.mem = entered.σ.mem := fresh.memory.trans range.memory
  refine ⟨after, rangeRun.trans freshRun, ⟨fresh.machine.good, fresh.machine.minstret, fresh.machine.tick,
    fresh.code, memory.trans entry.memory, fresh.pc, ?_, ?_, ?_,
    fresh.machine.output.trans (range.machine.output.trans entry.machine.output), ?_⟩⟩
  · simpa only [headerSame] using fresh.registers
  · exact allocation_carried_after fresh.machine
      (fun n hn => by
        have member := written n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> decide) carried
  · intro cell member
    simpa only [word, memory] using entry.saved input.entry cell member
  · intro r noise outside
    apply (fresh.machine.frame r noise (fun n hn => outside n (List.mem_append_right _ (List.mem_append_right _ hn)))).trans
    apply (range.machine.frame r noise (fun n hn => outside n (List.mem_append_right _ (List.mem_append_left _ hn)))).trans
    exact entry.machine.frame r noise (fun n hn => outside n (List.mem_append_left _ hn))

end OCaml.Vm.Gc.Fresh
