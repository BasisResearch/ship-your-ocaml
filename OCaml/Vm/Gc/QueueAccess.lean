import OCaml.Vm.Gc.Queue

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open MopupPop

/-- The generated global symbol is an aligned ordinary-RAM word. -/
theorem todo_window : WriteWindow (BitVec.ofNat 64 Layout.sym_oldify_todo_list) 8 := by
  constructor <;> decide

/-- The first scalar read is exactly the queue-head observation. -/
theorem head_access (q : PendingCopy) (c : Config) :
    AccessPlan c.σ.mem regs (loads q c) headBlock.body := by
  simp only [AccessPlan, headBlock, caml_oldify_mopupX9d00FSeg, List.getD_cons_zero]
  chain_facts True.intro
  apply todo_window.read.ld rfl ?_ (read8_pins _ Layout.sym_oldify_todo_list)
  simp [eaddrM, mkLine, decodeM, regs, srcVal, lookupG, Functions.sign_extend, Sail.BitVec.signExtend]

/-- The symbolic register result of loading the queue head. -/
theorem head_regs {q qs pl c} (view : View (q :: qs) pl c) :
    runGM headBlock.body regs (loads q c) =
      [(18, q.source), (23, BitVec.ofNat 64 Layout.sym_oldify_todo_list)] := by
  have root : bytesVal .ld (read8 c.σ.mem Layout.sym_oldify_todo_list) = q.source := by
    rw [read8_value]
    exact view.root
  change [(18, bytesVal .ld (read8 c.σ.mem Layout.sym_oldify_todo_list)),
    (23, BitVec.ofNat 64 Layout.sym_oldify_todo_list)] = _
  rw [root]

/-- A nonzero ghost head selects the nonempty work-list branch. -/
theorem head_control {q qs pl c} (view : View (q :: qs) pl c) (nonzero : q.source ≠ 0) :
    TermFactsO (runGM headBlock.body regs (loads q c)) headBlock.term := by
  rw [head_regs view]
  simpa [headBlock, caml_oldify_mopupX9d00FSeg, TermFactsO, TermFactsT,
    guardB, srcVal, lookupG] using nonzero

/-- Per-node RAM windows; supplied by nursery and allocation geometry. -/
structure PopWindows (q : PendingCopy) : Prop where
  source : ReadWindow q.source 8
  first : ReadWindow q.target 8
  next : ReadWindow (q.target + 8#64) 8

def afterHeadRegs (q : PendingCopy) : GRegs :=
  [(18, q.source), (23, BitVec.ofNat 64 Layout.sym_oldify_todo_list)]

/-- The remaining reads follow the forwarding pointer and then the copied
payload. The only write is to the Layout-derived global queue head. -/
theorem child_access {q qs pl c} (view : View (q :: qs) pl c)
    (windows : PopWindows q) (immediate : Bool) :
    AccessPlan c.σ.mem (afterHeadRegs q) (loads q c).tail (childBlock immediate).body := by
  have target : bytesVal .ld (read8 c.σ.mem q.source.toNat) = q.target := by
    rw [read8_value]; exact view.first.target
  cases immediate <;>
    simp only [childBlock, Bool.false_eq_true, ite_false, ite_true,
      caml_oldify_mopupX9d08TSeg, caml_oldify_mopupX9d08FSeg,
      List.getD_cons_zero, AccessPlan]
  all_goals chain_facts True.intro
  all_goals first
    | apply windows.source.ld rfl ?_ (read8_pins _ q.source.toNat)
    | apply windows.next.ld rfl ?_ (read8_pins _ (q.target + 8#64).toNat)
    | apply windows.first.ld rfl ?_ (read8_pins _ q.target.toNat)
    | apply todo_window.sd rfl
  all_goals simp [eaddrM, mkLine, decodeM, afterHeadRegs, stepGM, stepLdsM,
    wvalM, srcVal, lookupG, eraseG, loads, target, Functions.sign_extend, Sail.BitVec.signExtend]

/-- The machine's low-bit test chooses the first-field branch. -/
def firstImmediate (q : PendingCopy) (c : Config) : Bool :=
  guardB .BNE (word c q.target.toNat &&& 1#64) 0

theorem child_control (q : PendingCopy) (c : Config) :
    TermFactsO (runGM (childBlock (firstImmediate q c)).body (afterHeadRegs q)
      (loads q c).tail) (childBlock (firstImmediate q c)).term := by
  generalize choice : firstImmediate q c = immediate
  cases immediate <;>
    simpa [firstImmediate, childBlock, caml_oldify_mopupX9d08TSeg,
      caml_oldify_mopupX9d08FSeg, TermFactsO, TermFactsT, runGM, stepGM, mkLine, decodeM,
      afterHeadRegs, stepLdsM, wvalM, srcVal, lookupG, eraseG, loads,
      read8_value, word, Functions.sign_extend, Sail.BitVec.signExtend] using choice

/-- All scalar and control facts for this pop, with load bytes read directly
from the represented queue. Code certificates remain reusable across visits. -/
theorem pop_access {q qs pl c} (view : View (q :: qs) pl c)
    (windows : PopWindows q) (nonzero : q.source ≠ 0) :
    ChainAccess c.σ.mem regs (loads q c) (blocks (firstImmediate q c)) := by
  rw [blocks_eq]
  apply ChainAccess.cons ⟨head_access q c, head_control view nonzero⟩
  change ChainAccess c.σ.mem (runGM headBlock.body regs (loads q c))
    (loads q c).tail [childBlock (firstImmediate q c)]
  rw [head_regs view]
  exact ChainAccess.cons ⟨child_access view windows _, child_control q c⟩ ChainAccess.nil

/-- Platform, code and queue geometry needed at the concrete mopup loop head.
The enclosing collector invariant must supply these; no run is assumed. -/
structure PopInput (q : PendingCopy) (qs : List PendingCopy) (pl : Place) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  registers : GHolds c.σ regs
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  queue : View (q :: qs) pl c
  windows : PopWindows q
  nonzero : q.source ≠ 0
  separate : Separate qs

/-- The exact generated effect together with removal of the logical head. -/
structure PopPost (q : PendingCopy) (qs : List PendingCopy) (pl : Place)
    (before after : Config) : Prop where
  machine : MopupPop.Post (firstImmediate q before) (loads q before) before.σ.mem after
  queue : View qs pl after

/-- Execute the actual mopup queue-pop code from concrete RAM and link facts.
This summary stops at the first-field branch, before any oldify call. -/
theorem pop_machine {q qs pl c} (input : PopInput q qs pl c) :
    FnSummary MopupPop.pc (fun d => d = c) (PopPost q qs pl c) := by
  constructor
  rintro d ⟨pc, same⟩
  subst d
  have pre : SegPre (blocks (firstImmediate q c)) regs (loads q c) MopupPop.pc c.σ.mem c :=
    ⟨input.good, rfl, pc, input.minstret, input.registers, by decide,
      chainPlan_facts (code_facts _ input.code) (pop_access input.queue input.windows input.nonzero),
      input.tick⟩
  obtain ⟨after, run, post⟩ := (MopupPop.run _ _ _).run c ⟨pc, pre⟩
  exact ⟨after, run, ⟨post, pop_loaded input.queue post input.separate⟩⟩

end OCaml.Vm.Gc.WorkQueue
