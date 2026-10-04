import OCaml.Vm.Gc.BestFitBitmap
import OCaml.Vm.Gc.BestFitFinish
import OCaml.Vm.Primitives.MemoryFrame
import Vsa.Sim.GRegsFrame

namespace OCaml.Vm.Gc.BestFitBitmap
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Bitmap scratch registers do not overlap the common return interface. -/
theorem Post.return_registers {size before after} (post : Post size before after)
    {ra head} (pins : GHolds before.σ (BestFitFinish.regs ra size head)) :
    GHolds after.σ (BestFitFinish.regs ra size head) := by
  apply gholds_of_frame post.machine.frame (BestFitFinish.regs ra size head)
    (by change KeysOK [1,10,15]; decide) ?_ ?_ pins
  · change ∀ n ∈ [1,10,15], ∀ q ∈ noiseRegs, (q == gprReg n) = false
    decide
  · change ∀ n ∈ [1,10,15], ∀ m ∈ wrChain blocks, (gprReg m == gprReg n) = false
    decide

/-- Bitmap clearing leaves the separate free-word counter unchanged. -/
theorem Post.counter_frame {size before after} (post : Post size before after) :
    word after Layout.sym_caml_fl_cur_wsz = word before Layout.sym_caml_fl_cur_wsz := by
  unfold word
  rw [post.memory]
  apply bytesT_writeLog_out
  exact ⟨by
    change Layout.sym_caml_fl_cur_wsz + 8 ≤ Layout.sym_bf_small_map ∨
      Layout.sym_bf_small_map + 4 ≤ Layout.sym_caml_fl_cur_wsz
    decide,True.intro⟩

structure ReturnInput (ra size head : BitVec 64) (c : Config) : Prop extends Input size c where
  returnRegs : GHolds c.σ (BestFitFinish.regs ra size head)
  aligned : ra.toNat % 4 = 0

/-- The empty-tail suffix has cleared its bitmap bit, updated accounting
and returned the selected header pointer, retaining native/output frames. -/
structure ReturnPost (ra size head : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded after.σ.mem
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (head - BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem
    ([(Layout.sym_bf_small_map,4,cleared size (bytesVal .lw (read4 before.σ.mem Layout.sym_bf_small_map)))] ++
      BestFitFinish.effect size before)
  bitmap : word32 after Layout.sym_bf_small_map =
    word32 before Layout.sym_bf_small_map &&& ~~~(1#32 <<< (size.toNat - 1))
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Real bitmap clearing followed by the common accounting/native return,
with no assumed execution of either block sequence. -/
theorem clear_return {ra size head c} (input : ReturnInput ra size head c) :
    FnSummary pc (fun d => d = c) (ReturnPost ra size head c) := by
  constructor
  apply Vsa.Logic.Triple.seq (clear input.toInput).run
  intro middle clearedPost
  have finishInput : BestFitFinish.Input ra size head middle :=
    ⟨clearedPost.machine.good,clearedPost.machine.tick,clearedPost.machine.minstret,
      clearedPost.code,clearedPost.return_registers input.returnRegs,input.aligned⟩
  obtain ⟨after,run,finished⟩ := (BestFitFinish.finish finishInput).run middle ⟨clearedPost.pc,rfl⟩
  refine ⟨after,run,⟨finished.machine.good,finished.machine.tick,finished.machine.minstret,
    finished.code,finished.pc,finished.result,?_,?_,finished.machine.output.trans clearedPost.machine.output,?_⟩⟩
  · rw [finished.memory,BestFitFinish.effect,clearedPost.counter_frame,clearedPost.memory,writeLog_append]
    rfl
  · have frame : word32 after Layout.sym_bf_small_map = word32 middle Layout.sym_bf_small_map := by
      unfold word32
      rw [finished.memory]
      apply bytesT_writeLog_out
      exact ⟨by
        change Layout.sym_bf_small_map + 4 ≤ Layout.sym_caml_fl_cur_wsz ∨
          Layout.sym_caml_fl_cur_wsz + 8 ≤ Layout.sym_bf_small_map
        decide,True.intro⟩
    exact frame.trans clearedPost.bitmap
  · intro r noise outside
    exact (finished.machine.frame r noise (fun n hn => outside n (by
      have member := BestFitFinish.written n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl <;> simp))).trans
      (clearedPost.machine.frame r noise (fun n hn => outside n (by
        have member := written n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
        rcases member with rfl | rfl | rfl <;> simp)))

end OCaml.Vm.Gc.BestFitBitmap
