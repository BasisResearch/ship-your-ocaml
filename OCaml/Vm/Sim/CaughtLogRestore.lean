import OCaml.Vm.Sim.DivisionRaisePayload
import OCaml.Vm.Sim.ReentryHandler
import OCaml.Vm.Primitives.Allocation

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Footprints and saved geometry for restoring represented data after a native raise.
The final store publishes the represented exception; runtime stability concerns only this exact log. -/
structure CaughtLogReady (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (nativeSp sp high dest : Nat) (link extra : BitVec 63) (env : Val) (rest : List Val)
    (c : Config) (log front : List WEntry) (value : BitVec 64) : Prop where
  data : VmPayload P s c pl cp sp high
  bindings : PrimitiveBindings P c
  runtime : L.runtimeOk c
  frame : RaiseFrame s dest link env extra rest
  geometry : CaughtReentryGeometry L P s pl cp nativeSp sp high dest link extra env rest c
  exceptionValue : valWord pl s.accu = some value
  bucketLog : log = front ++ [((word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket, 8, value)]
  payloadOutside : PayloadOutside log P s c pl cp sp
  bindingsOutside : BindingsOutside log P c
  rootsPayloadOutside : PayloadOutside (reentryLog nativeSp c) P s c pl cp sp
  rootsBindingsOutside : BindingsOutside (reentryLog nativeSp c) P c
  savedOutside : ∀ offset ∈ [0, 8, Layout.interpSavedRootsOffset], OutLRange log (nativeSp + offset) 8
  runtimeFrame : AllocationRuntime L.runtimeOk c log

/-- Derive the full represented caught-handler readiness from the concrete memory effect. -/
theorem caught_log_restore {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {nativeSp sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    {c : Config} {log front : List WEntry} {value : BitVec 64}
    (h : CaughtLogReady L P s pl cp nativeSp sp high dest link extra env rest c log front value) :
    CaughtReentryReady L P s pl cp nativeSp sp high dest link extra env rest (nativeMemoryView c log) := by
  have read : ∀ a, OutLRange log a 8 → word (nativeMemoryView c log) a = word c a := by
    intro a outside
    change bytesT (writeLog c.σ.mem log) a 8 = word c a
    exact bytesT_writeLog_out _ outside
  have domain := read _ h.payloadOutside.domain
  have contents := read _ h.bindingsOutside.contents
  have rootsWord := read _ (h.savedOutside Layout.interpSavedRootsOffset (by simp))
  have roots : reentryLog nativeSp (nativeMemoryView c log) = reentryLog nativeSp c := by
    simp only [reentryLog, domain, rootsWord]
  have rootPayload : PayloadOutside (reentryLog nativeSp (nativeMemoryView c log)) P s
      (nativeMemoryView c log) pl cp sp := by
    rw [roots]
    exact { h.rootsPayloadOutside with
      stackHigh := by simpa only [domain] using h.rootsPayloadOutside.stackHigh
      trapsp := by simpa only [domain] using h.rootsPayloadOutside.trapsp }
  have rootBindings : BindingsOutside (reentryLog nativeSp (nativeMemoryView c log)) P (nativeMemoryView c log) := by
    rw [roots]
    exact ⟨h.rootsBindingsOutside.contents, by simpa only [contents] using h.rootsBindingsOutside.entries⟩
  have savedHigh : word (nativeMemoryView c log) nativeSp = word c nativeSp :=
    read _ (by simpa only [Nat.add_zero] using h.savedOutside 0 (by simp))
  have savedSp := read _ (h.savedOutside 8 (by simp))
  refine {
    toRaiseReentryReady := {
      data := h.data.frame_log h.payloadOutside rfl rfl
      bindings := bindings_frame_log h.bindings h.bindingsOutside rfl
      runtime := h.runtimeFrame _ rfl h.runtime
      frame := h.frame
      exceptionWord := ?_
      outside := rootPayload, bindingsOutside := rootBindings }
    toCaughtReentryGeometry := h.geometry.frame_observations domain contents savedHigh savedSp roots }
  rw [domain, native_memory_last_word h.bucketLog]
  exact h.exceptionValue

end OCaml.Vm.Sim
