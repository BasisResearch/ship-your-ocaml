import OCaml.Vm.Gc.ScanSetup
import OCaml.Vm.Gc.QueueAccess

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- This scalar word is disjoint from the published work-list head. -/
def OutsideTodo (a : Nat) : Prop :=
  a + 8 ≤ Layout.sym_oldify_todo_list ∨ Layout.sym_oldify_todo_list + 8 ≤ a

/-- The nursery/allocation geometry keeps object headers and payloads separate
from the runtime global that the queue pop writes. -/
structure PayloadOutsideTodo (q : PendingCopy) (count : Nat) : Prop where
  header : OutsideTodo (q.target.toNat - 8)
  first : OutsideTodo q.target.toNat
  suffix : ∀ i, 1 ≤ i → i < count → OutsideTodo (q.source.toNat + 8 * i)

theorem PopPost.word_unchanged {q qs pl before after a} (post : PopPost q qs pl before after)
    (outside : OutsideTodo a) : word after a = word before a := by
  change bytesT after.σ.mem a 8 = bytesT before.σ.mem a 8
  rw [post.machine.memory]
  change bytesT (writeLog before.σ.mem (MopupPop.outcome _ _).log) a 8 = _
  rw [MopupPop.queue_write]
  exact bytesT_writeLog_out _ ⟨outside, True.intro⟩

theorem PopPost.code {q qs pl before after} (input : PopInput q qs pl before)
    (post : PopPost q qs pl before after) : Code.Caml_oldify_mopupLoaded after.σ.mem :=
  mopupCode_after input.code
    (chainPlan_facts (MopupPop.code_facts _ input.code)
      (pop_access input.queue input.windows input.nonzero)) post.effects

/-- Pop preserves the grey layout because only the global queue head changes. -/
theorem PopPost.payload {q qs pl before after fields}
    (post : PopPost q qs pl before after)
    (outside : PayloadOutsideTodo q fields.length)
    (grey : (pendingPayload q fields).P pl q.target.toNat before) :
    (pendingPayload q fields).P pl q.target.toNat after := by
  have image : (pendingPayload q fields).Img id pl q.target.toNat q.target.toNat before after := by
    apply Reloc.Eqv.list_val_img grey
    intro i v hi
    rw [placement_identity]
    have same : word after (if i = 0 then q.target.toNat else q.source.toNat + 8 * i) =
        word before (if i = 0 then q.target.toNat else q.source.toNat + 8 * i) := by
      by_cases zero : i = 0
      · simpa [zero] using post.word_unchanged outside.first
      · simp only [ite_eq_right zero]
        exact post.word_unchanged (outside.suffix i (by omega) (List.getElem?_eq_some_iff.mp hi).1)
    rw [same]
    exact grey i v hi
  simpa only [placement_identity] using
    (pendingPayload q fields).transport id pl _ _ before after grey image

/-- The loaded queue pointers and preserved runtime constant are precisely
those consumed by the generated suffix setup block. -/
theorem PopPost.setup_input {q qs pl count before after}
    (input : PopInput q qs pl before) (post : PopPost q qs pl before after)
    (geometry : FieldCopy.Geometry q.source.toNat q.target.toNat count)
    (large : 1 < count)
    (header : (word before (q.target.toNat - 8)).toNat / 1024 = count)
    (outside : OutsideTodo (q.target.toNat - 8))
    (s8 : gprGet before.σ 24 = some 1#64) :
    FieldCopy.SetupInput q.source.toNat q.target.toNat count after := by
  have loadedSource : bytesVal .ld ((loads q before).headD []) = q.source := by
    change bytesVal .ld (read8 before.σ.mem Layout.sym_oldify_todo_list) = _
    rw [read8_value]; exact input.queue.root
  have loadedTarget : bytesVal .ld ((loads q before).tail.headD []) = q.target := by
    change bytesVal .ld (read8 before.σ.mem q.source.toNat) = _
    rw [read8_value]; exact input.queue.first.target
  have registers := post.machine.source_target
  rw [loadedSource, loadedTarget] at registers
  have keep : gprGet after.σ 24 = gprGet before.σ 24 :=
    post.effects.frame Register.x24 (by decide) (MopupPop.preserves_s8 _)
  refine ⟨post.machine.good, post.machine.minstret, post.machine.tick,
    post.code input, ?_, geometry, large, ?_⟩
  · simpa [FieldCopy.setupRegs] using
      (show GHolds after.σ [(19, q.target), (18, q.source), (24, 1)] from
        ⟨gholds_lookup _ registers rfl, gholds_lookup _ registers rfl, keep.trans s8, True.intro⟩)
  · rw [post.word_unchanged outside]
    exact header

/-- A destination suffix is disjoint from the remaining queue's link cells
and the global head. Heap ownership supplies these finite separation facts. -/
structure QueueOutsideScan (qs : List PendingCopy) (b count : Nat) : Prop where
  root : Layout.sym_oldify_todo_list + 8 ≤ b + 8 ∨ b + 8 * count ≤ Layout.sym_oldify_todo_list
  cells : ∀ (i : Nat) (p : PendingCopy), qs[i]? = some p →
    ∀ (j : Nat) (cell : Nat × BitVec 64), (p.cells (next qs i))[j]? = some cell →
      cell.1 + 8 ≤ b + 8 ∨ b + 8 * count ≤ cell.1

theorem View.scan_frame {qs pl before after b count}
    (queue : View qs pl before) (outside : QueueOutsideScan qs b count)
    (memory : FrameOn (FieldCopy.scanWindow b 1 count) before.σ.mem after.σ.mem) :
    View qs pl after := by
  refine ⟨(FieldCopy.word_frame memory outside.root).trans queue.root, ?_⟩
  apply body_frame_words queue.links
  intro i p hp j cell hc
  exact FieldCopy.word_frame memory (outside.cells i p hp j cell hc)

/-- An integer saved first field selects the path directly into suffix setup. -/
theorem first_immediate {q : PendingCopy} {fields : List Val} {pl c}
    (grey : (pendingPayload q fields).P pl q.target.toNat c)
    (nonempty : 0 < fields.length)
    (integers : ∀ (i : Nat) v, fields[i]? = some v → ∃ n, v = Val.int n) :
    firstImmediate q c = true := by
  have hi : fields[0]? = some fields[0] := List.getElem?_eq_getElem nonempty
  obtain ⟨n, value⟩ := integers 0 fields[0] hi
  have represented := grey 0 fields[0] hi
  have same : tag64 n = word c q.target.toNat := by
    simpa [Reloc.Eqv.val, value, valWord] using represented
  change guardB .BNE (word c q.target.toNat &&& 1#64) 0 = true
  rw [← same]
  exact FieldCopy.immediate_tag n

/-- The pop changes exactly its global head word. -/
theorem PopPost.memory_frame {q qs pl before after} (post : PopPost q qs pl before after) :
    FrameOn [⟨Layout.sym_oldify_todo_list, Layout.sym_oldify_todo_list + 8⟩]
      before.σ.mem after.σ.mem := by
  rw [post.machine.memory]
  change FrameOn _ _ (writeLog before.σ.mem (MopupPop.outcome _ _).log)
  rw [MopupPop.queue_write]
  apply frameOn_writeLog
  exact ⟨Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩, True.intro⟩

/-- One pending integer-valued block has been removed and fully scanned. The
next queue iteration/ephemeron branch and pointer fields remain separate. -/
structure PopScanPost (q : PendingCopy) (qs : List PendingCopy) (fields : List Val)
    (pl : Place) (cp : ChanPlace) (tag : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_mopupLoaded after.σ.mem
  pc : PCAt FieldCopy.exitPc after
  object : ObjAt after pl cp q.target.toNat (.block tag fields)
  queue : View qs pl after
  memory : FrameOn (⟨Layout.sym_oldify_todo_list, Layout.sym_oldify_todo_list + 8⟩ ::
    FieldCopy.scanWindow q.target.toNat 1 fields.length) before.σ.mem after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [8, 9, 10, 11, 15, 18, 19], (gprReg n == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r

/-- Concrete queue pop, first-field immediate classifier, setup and complete
integer suffix. The only separation premises describe actual word footprints. -/
theorem pop_scan {q qs fields pl cp tag c}
    (input : PopInput q qs pl c)
    (geometry : FieldCopy.Geometry q.source.toNat q.target.toNat fields.length)
    (large : 1 < fields.length)
    (header : HeaderOk (word c (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat c)
    (integers : ∀ (i : Nat) v, fields[i]? = some v → ∃ n, v = Val.int n)
    (outside : PayloadOutsideTodo q fields.length)
    (queueOutside : QueueOutsideScan qs q.target.toNat fields.length)
    (s8 : gprGet c.σ 24 = some 1#64) :
    FnSummary MopupPop.pc (fun d => d = c) (PopScanPost q qs fields pl cp tag c) := by
  constructor
  apply Vsa.Logic.Triple.seq (pop_machine input).run
  intro middle popped
  have immediate := first_immediate grey (by omega) integers
  have pc : PCAt FieldCopy.setupPc middle := by
    have machine := popped.machine
    rw [immediate] at machine
    exact machine.setup_pc
  have setupInput := popped.setup_input input geometry large header.2 outside.header s8
  have middleHeader : HeaderOk (word middle (q.target.toNat - 8)) fields.length tag := by
    rw [popped.word_unchanged outside.header]
    exact header
  obtain ⟨after, run, post⟩ := (FieldCopy.setup_scan (cp := cp) setupInput middleHeader
    (popped.payload outside grey) (fun i v hi _ => integers i v hi)).run middle ⟨pc, rfl⟩
  refine ⟨after, run, ⟨post.good, post.minstret, post.tick, post.code, post.pc, post.object,
    popped.queue.scan_frame queueOutside post.memory, ?_,
    post.output.trans popped.effects.output, ?_⟩⟩
  · intro a outside
    exact (post.memory a outside.2).trans (popped.memory_frame a ⟨outside.1, True.intro⟩)
  · intro r noise untouched
    apply (post.native r noise ?_).trans
      (popped.effects.frame r noise (fun n hn => untouched n (MopupPop.written _ n hn)))
    intro n hn
    apply untouched n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OCaml.Vm.Gc.WorkQueue
