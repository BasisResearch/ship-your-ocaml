import OCaml.Vm.Primitives.ImmediateContract
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.CounterArithmetic
import OCaml.Vm.Primitives.Write

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

def counterLog (old : BitVec 64) : List WEntry := [(Layout.sym_oo_last_id, 8, old + 2)]
def counterWindows : List W := [⟨Layout.sym_oo_last_id, Layout.sym_oo_last_id + 8⟩]

theorem counter_read : ReadWindow (BitVec.ofNat 64 Layout.sym_oo_last_id) 8 := by
  constructor <;> decide

theorem counter_write : WriteWindow (BitVec.ofNat 64 Layout.sym_oo_last_id) 8 := by
  constructor <;> decide

theorem counter_image (old : BitVec 64) : ImageOutside (counterLog old) := by
  constructor <;> simp only [counterLog, OutLRange] <;> decide

theorem counter_log_in (old : BitVec 64) : LogInW counterWindows (counterLog old) := by
  simp [counterWindows, counterLog, LogInW, InsideW]

/-- The caller links the fixed global to the abstract counter and supplies
its static separation from VM observations. -/
structure CounterInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high ra [s.accu] c where
  bindingsOutside : BindingsOutside (counterLog (counterWord s.world.ooId)) P c
  counter : word c Layout.sym_oo_last_id = counterWord s.world.ooId
  outside : PayloadOutside (counterLog (counterWord s.world.ooId)) P s c pl cp sp

structure CounterPost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (before : Config) (ra : BitVec 64)
    (after : Config) : Prop
    extends PrimitivePost runtimeOk P s pl cp sp high "caml_fresh_oo_id" [s.accu]
      (Val.ofInt s.world.ooId) (counterWord s.world.ooId) s.heap
      {s.world with ooId := s.world.ooId + 1} [10, 14, 15]
      (writeLog before.σ.mem (counterLog (counterWord s.world.ooId))) before ra after where
  counter : word after Layout.sym_oo_last_id = counterWord (s.world.ooId + 1)

theorem counter_contract {runtimeOk P s pl cp sp high ra c entry}
    (stable : WindowStable runtimeOk counterWindows)
    (h : CounterInput runtimeOk P s pl cp sp high ra c)
    (S : FnSummary entry (fun x => x = c)
      (WritePost [10, 14, 15] (counterLog (word c Layout.sym_oo_last_id)) c ra
        (word c Layout.sym_oo_last_id))) :
    FnSummary entry (fun x => x = c) (CounterPost runtimeOk P s pl cp sp high c ra) := by
  rw [h.counter] at S
  apply S.weaken (fun _ h => h)
  intro after post
  have frame : FrameOn counterWindows c.σ.mem after.σ.mem := by
    rw [post.memory]
    exact frameOn_writeLog _ _ _ (counter_log_in _)
  refine { toPrimitivePost := {
    call := post
    data := ?_
    primitives := bindings_frame_log h.primitives h.bindingsOutside post.memory
    platform := ⟨post.good, post.image, stable _ _ frame h.runtime⟩
    loop := post.loop (by
      simp [PreservesLoopRegisters, Layout.reg_dispatchTable, Layout.reg_opcodeBound,
        Layout.reg_pending, Layout.reg_domain, gprReg]) h.loop
    resultRepr := counterWord_repr pl s.world.ooId
    semantics := rfl }, counter := ?_ }
  · simpa only [Val.ofInt, BitVec.ofInt_natCast] using
      ((h.data.frame_log h.outside post.memory post.output).accu_int
        (BitVec.ofNat 63 s.world.ooId)).ooId (s.world.ooId + 1)
  · change bytesT after.σ.mem Layout.sym_oo_last_id 8 = _
    rw [post.memory]
    exact (word_writeLog c.σ.mem Layout.sym_oo_last_id (counterWord s.world.ooId + 2)).trans
      (counterWord_succ s.world.ooId)

end OCaml.Vm.Primitives
