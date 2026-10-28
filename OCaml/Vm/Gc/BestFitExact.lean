import OCaml.Vm.Gc.BestFitEmpty
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.DomainRecord

namespace OCaml.Vm.Gc.BestFitExact
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable BestFitSmall

/-- Exact-size small-list allocation. Both branch decisions are read from
initial memory. Repair and bitmap separation are required only on routes
that actually perform those accesses. -/
structure Conditions (size : BitVec 64) (c : Config) : Prop extends CoreConditions size c where
  repair : cursor size c = first size c → RepairConditions size c
  bitmap : next size c = 0 → OutLRange (BestFitEmpty.effect size c) Layout.sym_bf_small_map 4

structure Input (ra size : BitVec 64) (c : Config) : Prop extends CoreInput ra size c, Conditions size c

theorem Conditions.of_memory {size} {before after : Config}
    (memory : after.σ.mem = before.σ.mem) (conditions : Conditions size before) : Conditions size after := by
  refine ⟨conditions.toCoreConditions.of_memory memory,?_,?_⟩
  · intro repair
    have same : cursor size before = first size before := by simpa only [cursor,first,word,memory] using repair
    have ready := conditions.repair same
    exact ⟨ready.mergeWrite,by simpa only [first,word,memory] using ready.nextOutside,ready.counterOutside⟩
  · intro empty
    have same : next size before = 0 := by simpa only [next,first,word,memory] using empty
    simpa [BestFitEmpty.effect,BestFitEmpty.route,cursor,next,first,word,memory] using conditions.bitmap same

def effect (size : BitVec 64) (c : Config) : List WEntry :=
  if next size c = 0 then BestFitEmpty.allocationEffect size c else selectedEffect size c

/-- Factor only the bounded store log, retaining both memory-selected branches. -/
theorem effect_parts (size : BitVec 64) (c : Config) :
    effect size c = BestFitEmpty.effect size c ++
      (if next size c = 0 then [(Layout.sym_bf_small_map,4,
        BestFitBitmap.cleared size (bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map)))] else []) ++
      BestFitFinish.effect size c := by
  by_cases empty : next size c = 0
  all_goals by_cases repair : cursor size c = first size c
  all_goals simp only [effect,empty,repair,ite_true,ite_false,BestFitEmpty.allocationEffect,
    BestFitEmpty.effect,BestFitEmpty.route,selectedEffect,decide_true,decide_false,
    BestFitSmall.effect,BestFitFinish.effect,total,Bool.false_eq_true,List.append_assoc,List.cons_append,List.nil_append]

/-- Separation certificate for the actual possible exact-size stores. -/
structure StoreOutside (size : BitVec 64) (a n : Nat) : Prop where
  slot : a+n ≤ (BestFitSmall.slot size).toNat ∨ (BestFitSmall.slot size).toNat+8 ≤ a
  merge : a+n ≤ (BestFitSmall.slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat ∨
    (BestFitSmall.slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat+8 ≤ a
  bitmap : a+n ≤ Layout.sym_bf_small_map ∨ Layout.sym_bf_small_map+4 ≤ a
  counter : a+n ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ a

theorem effect_outside {size c a n} (outside : StoreOutside size a n) :
    OutLRange (effect size c) a n := by
  rw [effect_parts]
  by_cases empty : next size c = 0
  all_goals by_cases repair : cursor size c = first size c
  all_goals simp only [BestFitEmpty.effect,BestFitEmpty.route,repair,empty,decide_true,decide_false,
    ite_true,ite_false,Bool.false_eq_true,repairLog,BestFitFinish.effect,List.cons_append,List.nil_append,OutLRange]
  all_goals first
    | exact ⟨outside.merge,outside.slot,outside.bitmap,outside.counter,True.intro⟩
    | exact ⟨outside.slot,outside.bitmap,outside.counter,True.intro⟩
    | exact ⟨outside.merge,outside.slot,outside.counter,True.intro⟩
    | exact ⟨outside.slot,outside.counter,True.intro⟩

/-- The slot store is last in the pop prefix; later bitmap/accounting stores
are read back through scalar frame laws. -/
theorem effect_head {size c}
    (bitmap : (slot size).toNat+8 ≤ Layout.sym_bf_small_map ∨ Layout.sym_bf_small_map+4 ≤ (slot size).toNat)
    (counter : (slot size).toNat+8 ≤ Layout.sym_caml_fl_cur_wsz ∨ Layout.sym_caml_fl_cur_wsz+8 ≤ (slot size).toNat) :
    bytesT (writeLog c.σ.mem (effect size c)) (slot size).toNat 8 = next size c := by
  rw [effect_parts,writeLog_append,writeLog_append]
  rw [bytesT_writeLog_out _ (show OutLRange (BestFitFinish.effect size c) (slot size).toNat 8 from
    ⟨counter,True.intro⟩)]
  have suffix : OutLRange (if next size c = 0 then [(Layout.sym_bf_small_map,4,
      BestFitBitmap.cleared size (bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map)))] else [])
      (slot size).toNat 8 := by
    split
    · exact ⟨bitmap,True.intro⟩
    · trivial
  rw [bytesT_writeLog_out _ suffix,BestFitEmpty.effect,writeLog_append]
  exact word_writeLog _ _ _

/-- Bitmap observation from the actual conditional four-byte store. -/
theorem effect_bitmap {size c} (positive : 0 < size.toNat)
    (small : size.toNat ≤ Layout.bf_small_count)
    (popOutside : OutLRange (BestFitEmpty.effect size c) Layout.sym_bf_small_map 4) :
    bytesT (writeLog c.σ.mem (effect size c)) Layout.sym_bf_small_map 4 =
      if next size c = 0 then word32 c Layout.sym_bf_small_map &&& ~~~(1#32 <<< (size.toNat-1))
      else word32 c Layout.sym_bf_small_map := by
  rw [effect_parts,writeLog_append,writeLog_append]
  rw [bytesT_writeLog_out _ (show OutLRange (BestFitFinish.effect size c) Layout.sym_bf_small_map 4 from
    ⟨by
      change Layout.sym_bf_small_map+4 ≤ Layout.sym_caml_fl_cur_wsz ∨
        Layout.sym_caml_fl_cur_wsz+8 ≤ Layout.sym_bf_small_map
      decide,True.intro⟩)]
  by_cases empty : next size c = 0
  · simp only [empty,ite_true]
    rw [word32_writeLog]
    exact BestFitBitmap.cleared_word c size positive small
  · simp only [empty,ite_false]
    exact bytesT_writeLog_out _ popOutside

/-- All branch choices and store values depend only on memory observations. -/
theorem effect_of_memory {size} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    effect size after = effect size before := by
  simp [effect,BestFitEmpty.allocationEffect,BestFitEmpty.effect,BestFitEmpty.route,
    selectedEffect,BestFitSmall.effect,BestFitFinish.effect,cursor,next,first,total,word,memory]

/-- Every store of the complete exact-size path lies above the code/HTIF
boundary, including conditional cursor repair and bitmap clearing. -/
theorem Conditions.effect_high {size c} (input : Conditions size c) :
    ∀ e ∈ effect size c, Layout.sym_tohost + 16 ≤ e.1 := by
  have head := input.headWrite.htif
  have counter : Layout.sym_tohost + 16 ≤ Layout.sym_caml_fl_cur_wsz := by decide
  have bitmap : Layout.sym_tohost + 16 ≤ Layout.sym_bf_small_map := by decide
  intro e member
  by_cases empty : next size c = 0
  all_goals by_cases repair : cursor size c = first size c
  all_goals simp only [effect,empty,Bool.false_eq_true,eq_self,ite_true,ite_false,BestFitEmpty.allocationEffect,BestFitEmpty.effect,
    BestFitEmpty.route,repair,decide_true,decide_false,selectedEffect,
    repairLog,BestFitSmall.effect,BestFitFinish.effect,List.append_eq,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals first | exact head | exact counter | exact bitmap | exact (input.repair repair).mergeWrite.htif

theorem effect_high {ra size c} (input : Input ra size c) :
    ∀ e ∈ effect size c, Layout.sym_tohost + 16 ≤ e.1 := input.toConditions.effect_high

/-- Uniform result for all four exact-size small-list branches. This gives
actual execution and accounting, not a complete free-list ownership invariant. -/
structure Post (ra size : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded after.σ.mem
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (first size before - BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem (effect size before)
  counter : total after = total before - 1#64 - size
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete real exact-size small-list allocation, covering empty and
nonempty successors and both merge-cursor branches. -/
theorem allocate {ra size c} (input : Input ra size c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Post ra size c) := by
  by_cases empty : next size c = 0
  · have pathInput : BestFitEmpty.Input ra size c :=
      ⟨input.toCoreInput,empty,input.repair,input.bitmap empty⟩
    apply (BestFitEmpty.allocate pathInput).weaken (fun _ h => h)
    intro after post
    exact ⟨post.good,post.tick,post.minstret,post.code,post.pc,post.result,
      by simpa only [effect,empty,ite_true] using post.memory,
      post.counter,post.output,post.native⟩
  · have pathInput : NonemptyInput ra size c :=
      ⟨⟨input.toCoreInput,empty⟩,input.repair⟩
    apply (allocate_nonempty pathInput).weaken (fun _ h => h)
    intro after post
    have counter : total after = total c - 1#64 - size := by
      by_cases repair : cursor size c = first size c
      · have repaired : RepairPost ra size c after := by
          simpa only [NonemptyPost,selectedBlocks,selectedEffect,repair,ite_true,RepairPost] using post
        exact RepairPost.counter repaired
      · have kept : BestFitSmall.Post ra size c after := by
          simpa only [NonemptyPost,selectedBlocks,selectedEffect,repair,ite_false] using post
        exact BestFitSmall.Post.counter kept
    have cover : ∀ n ∈ wrChain (selectedBlocks size c), n ∈ [10,11,12,13,14,15] := by
      unfold selectedBlocks
      split
      · exact repair_written
      · exact BestFitSmall.written
    exact ⟨post.machine.good,post.machine.tick,post.machine.minstret,post.code,post.pc,post.result,
      by simpa only [effect,empty,ite_false] using post.memory,
      counter,post.machine.output,fun r noise outside =>
        post.machine.frame r noise (fun n hn => outside n (cover n hn))⟩

/-- All exact-size paths consume exactly the payload plus header when the
initial free-word counter has sufficient credit. -/
theorem Post.counter_nat {ra size before after} (post : Post ra size before after)
    (credit : size.toNat + 1 ≤ (total before).toNat) :
    (total after).toNat + size.toNat + 1 = (total before).toNat :=
  accounting_nat post.counter credit

/-- Shared register-frame interface for every exact-size branch. -/
theorem Post.gprs {ra size before after} (post : Post ra size before after) :
    OCaml.Vm.Boot.Startup.GprsSame before after [10,11,12,13,14,15] := by
  apply OCaml.Vm.Boot.Startup.GprsSame.of_regFrame (by decide)
  intro r outside noise
  exact post.native r noise (fun n hn => beq_eq_false_iff_ne.mpr (outside n hn))

theorem Post.live {ra size before after H} (post : Post ra size before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1+e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x →
      OutL (effect size before) x) : OCaml.Vm.Boot.Startup.LiveFrame H before after := by
  apply OCaml.Vm.Boot.Startup.LiveFrame.of_foot bounds
  intro x high owned
  rw [post.memory,writeLog_out _ _ _ (outside x high owned)]

end OCaml.Vm.Gc.BestFitExact
