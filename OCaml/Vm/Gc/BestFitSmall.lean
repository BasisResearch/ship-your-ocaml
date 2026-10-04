import OCaml.Vm.Gc.BestFitChunks

namespace OCaml.Vm.Gc.BestFitSmall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def first (size : BitVec 64) (c : Config) := word c (slot size).toNat
def cursor (size : BitVec 64) (c : Config) :=
  word c (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat
def next (size : BitVec 64) (c : Config) := word c (first size c).toNat
def total (c : Config) := word c Layout.sym_caml_fl_cur_wsz

def loads (size : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (slot size).toNat,
   read8 c.σ.mem (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat,
   read8 c.σ.mem (first size c).toNat,read8 c.σ.mem Layout.sym_caml_fl_cur_wsz]

def effect (size : BitVec 64) (c : Config) : List WEntry :=
  [((slot size).toNat,8,next size c), (Layout.sym_caml_fl_cur_wsz,8,total c - 1#64 - size)]

/-- Initial observations for the exact-size small-list route. The first
node and its successor are nonnull, the merge cursor is elsewhere, and
list-head replacement is separated from the free-word counter. This is
one allocation branch, not a complete free-list invariant. -/
structure CoreInput (ra size : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded c.σ.mem
  registers : GHolds c.σ (regs ra size)
  positive : 0 < size.toNat
  small : size.toNat ≤ Layout.bf_small_count
  head : first size c ≠ 0
  headWrite : WriteWindow (slot size) 8
  mergeRead : ReadWindow (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge) 8
  nextRead : ReadWindow (first size c) 8
  counterOutside : OutLRange [((slot size).toNat,8,next size c)] Layout.sym_caml_fl_cur_wsz 8
  aligned : ra.toNat % 4 = 0

/-- The common allocator observations specialized to a nonempty successor. -/
structure BaseInput (ra size : BitVec 64) (c : Config) : Prop extends CoreInput ra size c where
  tail : next size c ≠ 0

/-- The base observations plus the unchanged-cursor branch condition. -/
structure Input (ra size : BitVec 64) (c : Config) : Prop extends BaseInput ra size c where
  merge : cursor size c ≠ first size c

theorem access {ra size c} (input : Input ra size c) :
    ChainAccess c.σ.mem (regs ra size) (loads size c) blocks := by
  apply ChainAccess.append_eval (state := SegEvalState.init (regs ra size) (loads size c))
    (left := entryBlocks) (right := mergeBlock :: popReturnBlocks)
  · change ChainAccess c.σ.mem (regs ra size) (loads size c) entryBlocks
    apply entry_access _ _ _ _ _ input.headWrite.read (read8_pins _ _) input.small
    simpa only [read8_value,first,word] using input.head
  · simp only [loads,entry_eval,read8_value]
    change ChainAccess c.σ.mem (listed ra size (first size c)) _ _
    apply ChainAccess.cons ⟨merge_access _ _ _ _ _ _ input.mergeRead (read8_pins _ _),?_⟩
    · rw [merge_log,merge_regs,merge_loads]
      simp only [read8_value]
      change ChainAccess c.σ.mem (merged ra size (first size c) (cursor size c)) _ _
      apply pop_return_access _ _ _ _ _ _ _ input.nextRead input.headWrite (read8_pins _ _)
      · apply lpins8_writeLog (read8_pins _ _)
        simpa only [read8_value,next,word] using input.counterOutside
      · simpa only [read8_value,next,word] using input.tail
      · exact input.aligned
    · apply merge_control
      simpa only [read8_value,cursor,first,word] using input.merge

/-- A completed allocator return, with exact two-store memory effect,
returned header address, preserved code and the full native/output frame. -/
structure Post (ra size : BitVec 64) (before after : Config)
    (path : List BBlock := blocks) (writes : List WEntry := effect size before) : Prop where
  machine : BlockPost path pc (regs ra size) (loads size before) before after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (first size before - BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem writes
  code : Code.Bf_allocateLoaded after.σ.mem

/-- Execute the actual best-fit exact-size/nonempty-tail small-list path,
including free-word accounting and the native return instruction. -/
theorem allocate {ra size c} (input : Input ra size c) :
    FnSummary pc (fun d => d = c) (Post ra size c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs ra size) (loads size c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,10]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,endpoint _ _ _ _ _ _ input.aligned]
  · have pins := post.regs
    rw [loads,registers] at pins
    simp only [read8_value] at pins
    exact gholds_lookup _ pins (return_value _ _ _ _ _ _)
  · rw [post.memory,loads,log]
    simp only [effect,next,total,word,read8_value]

/-- The last store updates the real free-word accounting cell. -/
theorem Post.counter {ra size before after} (post : Post ra size before after) :
    total after = total before - 1#64 - size := by
  unfold total word
  rw [post.memory]
  exact word_writeLog_at before.σ.mem (effect size before) 1
    Layout.sym_caml_fl_cur_wsz _ rfl True.intro

/-- The first store removes precisely the selected head from its small list. -/
theorem Post.head {ra size before after} (post : Post ra size before after)
    (outside : OutLRange [((slot size).toNat,8,next size before)] Layout.sym_caml_fl_cur_wsz 8) :
    first size after = next size before := by
  unfold first word
  rw [post.memory]
  apply word_writeLog_at before.σ.mem (effect size before) 0 (slot size).toNat _ rfl
  exact ⟨outside.1.elim Or.inr Or.inl,True.intro⟩

/-- A free-word update with sufficient credit is ordinary natural subtraction. -/
theorem accounting_nat {before after size : BitVec 64}
    (counter : after = before - 1#64 - size) (credit : size.toNat + 1 ≤ before.toNat) :
    after.toNat + size.toNat + 1 = before.toNat := by
  rw [counter]
  have one : (1#64 : BitVec 64) ≤ before := by
    rw [BitVec.le_def]
    change 1 ≤ before.toNat
    omega
  have rest : size ≤ before - 1#64 := by
    rw [BitVec.le_def,BitVec.toNat_sub_of_le one]
    change size.toNat ≤ before.toNat - 1
    omega
  rw [BitVec.toNat_sub_of_le rest,BitVec.toNat_sub_of_le one]
  change before.toNat - 1 - size.toNat + size.toNat + 1 = _
  omega

/-- With sufficient free-word credit, machine subtraction is ordinary
natural subtraction of the requested payload plus its header. -/
theorem Post.counter_nat {ra size before after} (post : Post ra size before after)
    (credit : size.toNat + 1 ≤ (total before).toNat) :
    (total after).toNat + size.toNat + 1 = (total before).toNat :=
  accounting_nat post.counter credit

end OCaml.Vm.Gc.BestFitSmall
