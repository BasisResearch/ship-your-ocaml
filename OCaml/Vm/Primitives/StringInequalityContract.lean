import OCaml.Vm.Primitives.StringInequality

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- The caller supplies native-stack separation from every VM observation and
both canonical arguments. These are allocation/layout facts, not run premises. -/
structure StringNotEqualInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra nativeSp : BitVec 64)
    (l l' a a' : Nat) (bs bs' : List UInt8) (c : Config) : Prop
    extends StringPairInput runtimeOk P s pl cp sp high ra l l' a a' bs bs' c where
  nativeStack : gpr c 2 = some nativeSp
  window : WriteWindow (nativeSp - 8#64) 8
  imageOutside : ImageOutside (savedRaLog nativeSp ra)
  payloadOutside : PayloadOutside (savedRaLog nativeSp ra) P s c pl cp sp
  bindingsOutside : BindingsOutside (savedRaLog nativeSp ra) P c
  leftOutside : ObjectOutside (savedRaLog nativeSp ra) a (.bytes bs)
  rightOutside : ObjectOutside (savedRaLog nativeSp ra) a' (.bytes bs')

def stringInequalityResult (bs bs' : List UInt8) : BitVec 63 :=
  if bs == bs' then 0#63 else 1#63

theorem string_complement (bs bs' : List UInt8) :
    4#64 - tag64 (stringEqualityResult bs bs') = tag64 (stringInequalityResult bs bs') := by
  by_cases same : bs = bs' <;> simp [stringEqualityResult, stringInequalityResult, same, tag64]

structure StringNotEqualPost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra nativeSp : BitVec 64)
    (l l' : Nat) (bs bs' : List UInt8) (before after : Config) : Prop
    extends PrimitivePost runtimeOk P s pl cp sp high "caml_string_notequal" [.ptr l 0, .ptr l' 0]
      (.int (stringInequalityResult bs bs')) (tag64 (stringInequalityResult bs bs')) s.heap s.world
      wrapperWrites (writeLog before.σ.mem (savedRaLog nativeSp ra)) before ra after where
  nativeStack : gpr after 2 = some nativeSp

/-- Native-stack writes preserve the abstract heap/world, primitive bindings,
platform invariant and the interpreter's dedicated registers. -/
theorem string_notequal_contract {runtimeOk P s pl cp sp high ra nativeSp l l' a a' bs bs' c}
    (stable : WindowStable runtimeOk (savedRaWindows nativeSp))
    (h : StringNotEqualInput runtimeOk P s pl cp sp high ra nativeSp l l' a a' bs bs' c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_string_notequal) (fun d => d = c)
      (StringNotEqualPost runtimeOk P s pl cp sp high ra nativeSp l l' bs bs' c) := by
  have S := string_notequal_machine c ra nativeSp a a' bs bs' h.toLeafInput h.nativeStack
    (h.arguments.get (i := 0) rfl (by simp [valWord, h.placed]))
    (h.arguments.get (i := 1) rfl (by simp [valWord, h.placed']))
    h.window h.imageOutside h.canonical h.canonical' h.leftOutside h.rightOutside h.geometry h.geometry'
  rw [string_complement] at S
  apply S.weaken (fun _ h => h)
  intro after post
  have frame : FrameOn (savedRaWindows nativeSp) c.σ.mem after.σ.mem := by
    rw [post.memory]
    exact frameOn_writeLog _ _ _ (savedRa_log_in _ _)
  refine {
    toPrimitivePost := {
      call := post.toEffectPost
      data := (h.data.frame_log h.payloadOutside post.memory post.output).accu_int _
      primitives := bindings_frame_log h.primitives h.bindingsOutside post.memory
      platform := ⟨post.good, post.image, stable _ _ frame h.runtime⟩
      loop := post.toEffectPost.loop (by
        simp [PreservesLoopRegisters, wrapperWrites, Layout.reg_dispatchTable, Layout.reg_opcodeBound,
          Layout.reg_pending, Layout.reg_domain, gprReg]) h.loop
      resultRepr := rfl
      semantics := ?_ }
    nativeStack := gholds_lookup _ post.regs rfl }
  by_cases same : bs = bs' <;>
    simp [primF1Impl, strOf?, h.object, h.object', stringInequalityResult, Val.ofBool, same]

end OCaml.Vm.Primitives
