import OCaml.Vm.Gc.QueueEnqueue
import OCaml.Vm.Gc.QueueAccess

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open Enqueue

def rootLog (q : PendingCopy) (root : BitVec 64) : List WEntry :=
  [(root.toNat, 8, q.target)]

/-- The two reads use memory after the preceding stores, exactly as in the
runtime. Any link to original source contents is a separate footprint fact. -/
def enqueueLoads (q : PendingCopy) (root : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 (writeLog c.σ.mem (rootLog q root)) q.source.toNat,
   read8 (writeLog c.σ.mem (prefixLog q.source q.target root)) Layout.sym_oldify_todo_list]

/-- Allocator and nursery geometry supply these concrete write windows. -/
structure EnqueueWindows (q : PendingCopy) (root : BitVec 64) : Prop where
  rootSlot : WriteWindow root 8
  header : WriteWindow (q.source - 8#64) 8
  source : WriteWindow q.source 8
  first : WriteWindow q.target 8
  next : WriteWindow (q.target + 8#64) 8

/-- Shared normalization of the finite scalar-address expressions. This
reduces the reflected evaluator only; Sail instructions remain generated. -/
macro "enqueue_address" : tactic => `(tactic|
  simp [eaddrM, mkLine, decodeM, Enqueue.regs, Enqueue.afterPrefixRegs, stepGM, stepLdsM,
    wvalM, srcVal, lookupG, eraseG, enqueueLoads, Functions.sign_extend,
    Sail.BitVec.signExtend, imm20Of, Layout.sym_oldify_todo_list])

theorem enqueue_prefix_access (q : PendingCopy) (root size : BitVec 64) (c : Config)
    (windows : EnqueueWindows q root) :
    AccessPlan c.σ.mem (Enqueue.regs q.source q.target root size) (enqueueLoads q root c)
      prefixBlock.body := by
  simp only [AccessPlan, prefixBlock, caml_oldify_oneX9ba4TSeg, List.getD_cons_zero]
  chain_facts True.intro
  · apply windows.rootSlot.sd rfl
    enqueue_address
  · apply windows.source.read.ld rfl ?_ ?_
    · enqueue_address
    · simpa [stepMemM, wentryM, widthOfM, stepLdsM, eaddrM, mkLine, decodeM, Enqueue.regs, srcVal, lookupG,
        wvalM, enqueueLoads, rootLog, writeLog, applyW,
        Functions.sign_extend, Sail.BitVec.signExtend] using
        read8_pins (writeLog c.σ.mem (rootLog q root)) q.source.toNat
  · apply windows.header.sd rfl
    enqueue_address
  · apply windows.source.sd rfl
    enqueue_address

/-- The block-size comparison selects the intrusive-queue path. -/
theorem enqueue_prefix_control (q : PendingCopy) (root size : BitVec 64) (c : Config)
    (large : 1 < size.toNat) :
    TermFactsO (runGM prefixBlock.body (Enqueue.regs q.source q.target root size)
      (enqueueLoads q root c)) prefixBlock.term := by
  rw [prefix_regs]
  simpa [prefixBlock, caml_oldify_oneX9ba4TSeg, TermFactsO, TermFactsT,
    afterPrefixRegs, srcVal, lookupG, guardB] using
      (VsaIris.MallocFast.ult_iff 1 size).mpr large

/-- Prefix stores do not touch the old global head, as supplied by geometry. -/
theorem enqueue_loadedNext {q qs pl c root} (before : View qs pl c)
    (outside : OutLRange (prefixLog q.source q.target root) Layout.sym_oldify_todo_list 8) :
    bytesVal .ld ((enqueueLoads q root c).tail.headD []) = head qs := by
  change bytesVal .ld (read8 (writeLog c.σ.mem (prefixLog q.source q.target root))
    Layout.sym_oldify_todo_list) = _
  rw [read8_value, bytesT_writeLog_out _ outside]
  exact before.root

/-- Queue insertion reads the old global head, writes the saved first field,
then publishes the source link and next-source word. -/
theorem enqueue_push_access (q : PendingCopy) (root size : BitVec 64) (c : Config)
    (windows : EnqueueWindows q root) :
    AccessPlan (writeLog c.σ.mem (prefixLog q.source q.target root))
      (afterPrefixRegs q.source q.target size (bytesVal .ld ((enqueueLoads q root c).headD [])))
      (enqueueLoads q root c).tail pushBlock.body := by
  simp only [AccessPlan, pushBlock, caml_oldify_oneX9c98Seg, List.getD_cons_zero]
  chain_facts True.intro
  · apply todo_window.read.ld rfl ?_ ?_
    · enqueue_address
    · simpa [stepMemM, stepLdsM, mkLine, decodeM, enqueueLoads, Layout.sym_oldify_todo_list] using
        read8_pins (writeLog c.σ.mem (prefixLog q.source q.target root)) Layout.sym_oldify_todo_list
  · apply windows.first.sd rfl
    enqueue_address
  · apply todo_window.sd rfl
    enqueue_address
  · apply windows.next.sd rfl
    enqueue_address

/-- Concrete access plans for both blocks, with the branch proved from size. -/
theorem enqueue_access (q : PendingCopy) (root size : BitVec 64) (c : Config)
    (windows : EnqueueWindows q root) (large : 1 < size.toNat) :
    ChainAccess c.σ.mem (Enqueue.regs q.source q.target root size) (enqueueLoads q root c) blocks := by
  rw [blocks_eq]
  apply ChainAccess.cons ⟨enqueue_prefix_access q root size c windows,
    enqueue_prefix_control q root size c large⟩
  rw [prefix_log, prefix_regs]
  change ChainAccess (writeLog c.σ.mem (prefixLog q.source q.target root))
    (afterPrefixRegs q.source q.target size (bytesVal .ld ((enqueueLoads q root c).headD [])))
    (enqueueLoads q root c).tail [pushBlock]
  exact ChainAccess.cons ⟨enqueue_push_access q root size c windows, True.intro⟩ ChainAccess.nil

/-- The saved first-field value equals the original source observation. -/
theorem enqueue_loadedFirst {q c root first next}
    (separate : EnqueueSeparated q root first next) :
    bytesVal .ld ((enqueueLoads q root c).headD []) = word c q.source.toNat := by
  change bytesVal .ld (read8 (writeLog c.σ.mem (rootLog q root)) q.source.toNat) = _
  rw [read8_value, rootLog, bytesT_writeLog_out _ separate.sourceOutsideRoot]
  rfl

/-- Concrete entry obligations after the allocating call has returned.
Freshness, RAM geometry and callee-saved registers must come from that call;
there is no assumed machine run or scalar-load premise. -/
structure EnqueueInput (q : PendingCopy) (qs : List PendingCopy) (pl : Place)
    (root size : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  registers : GHolds c.σ (Enqueue.regs q.source q.target root size)
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  queue : View qs pl c
  windows : EnqueueWindows q root
  large : 1 < size.toNat
  headOutside : OutLRange (prefixLog q.source q.target root) Layout.sym_oldify_todo_list 8
  separate : EnqueueSeparated q root
    (bytesVal .ld ((enqueueLoads q root c).headD [])) (head qs)
  tailOutside : LinksOutside qs (effect q.source q.target root
    (bytesVal .ld ((enqueueLoads q root c).headD [])) (head qs))

/-- Retain the kernel's complete register/output frame for the epilogue splice,
and identify the first copied word with the original source observation. -/
structure EnqueueRunPost (q : PendingCopy) (qs : List PendingCopy) (pl : Place)
    (root size : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks Enqueue.pc (Enqueue.regs q.source q.target root size)
    (enqueueLoads q root before) before after
  data : EnqueuePost q qs pl root (word before q.source.toNat) after

/-- Execute the actual post-allocation queue insertion, discharging all data
loads, stores and its size branch. The callee itself remains a separate task. -/
theorem enqueue_machine {q qs pl root size c} (input : EnqueueInput q qs pl root size c) :
    FnSummary Enqueue.pc (fun d => d = c) (EnqueueRunPost q qs pl root size c) := by
  have summary := block_summary blocks Enqueue.pc (Enqueue.regs q.source q.target root size)
    (enqueueLoads q root c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [10, 9, 8, 24, 22, 25]; decide,
      chainPlan_facts (code_facts input.code) (enqueue_access q root size c input.windows input.large),
      chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have reflected : Enqueue.Post q.source q.target root size (enqueueLoads q root c) c.σ.mem after :=
    segmentPost_of_block post
  have data := enqueue input.queue reflected (enqueue_loadedNext input.queue input.headOutside)
    input.separate input.tailOutside
  rw [enqueue_loadedFirst input.separate] at data
  exact ⟨post, data⟩

end OCaml.Vm.Gc.WorkQueue
