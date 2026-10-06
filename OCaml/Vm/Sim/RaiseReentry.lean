import OCaml.Vm.Sim.LongjmpReentry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The local-roots store is the only memory mutation in quiet re-entry. -/
def reentryWindows (c : Config) : List W :=
  [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_local_roots,
    (word c Layout.sym_Caml_state).toNat + Layout.off_local_roots + 8⟩]

/-- Represented exception memory at a native raising continuation.
The raising helper supplies the exception bucket and heap/world effects;
the invocation invariant supplies separation from the local-roots slot. -/
structure RaiseReentryReady (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (nativeSp sp high dest : Nat) (link extra : BitVec 63) (env : Val) (rest : List Val) (c : Config) : Prop where
  data : VmPayload P s c pl cp sp high
  bindings : PrimitiveBindings P c
  runtime : L.runtimeOk c
  frame : RaiseFrame s dest link env extra rest
  exceptionWord : valWord pl s.accu = some (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_exn_bucket))
  outside : PayloadOutside (reentryLog nativeSp c) P s c pl cp sp
  bindingsOutside : BindingsOutside (reentryLog nativeSp c) P c
  /-- the VM stack geometry (`Invariant.lean`) -/
  geometry : OCaml.LoopGeometry L P s c pl cp high
  /-- the native invocation, held while the C stack unwinds (`InvariantUse.lean`) -/
  native : NativeHeld nativeSp c
  /-- the HTIF device is idle -/
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = some 0#4

/-- The native re-entry observations restore the represented common exception-check input. -/
theorem raise_reentry_restore {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {nativeSp sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c after : Config}
    (h : RaiseReentryReady L P s pl cp nativeSp sp high dest link extra env rest c)
    (stable : WindowStable L.runtimeOk (reentryWindows c))
    (post : ReentryControl nativeSp c after) :
    RaiseCheckInput L P s pl cp sp high dest link env extra rest after := by
  have domain : word after Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    Reloc.bytesT_congr (copied_of_writeLog post.memory h.outside.domain)
  have trap : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) =
      BitVec.ofNat 64 (high - 8 * s.trap) := by
    rw [← h.data.trapsp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have memoryFrame : FrameOn (reentryWindows c) c.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simp only [reentryWindows, reentryLog, LogInW, InsideW, or_false, and_true]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine {
    toRaiseContext := {
      data := h.data.frame_log h.outside post.memory post.output
      bindings := bindings_frame_log h.bindings h.bindingsOutside post.memory
      platform := ⟨post.good, post.image, stable c after memoryFrame h.runtime⟩
      frame := h.frame
      accu := ⟨_, post.exceptionValue, h.exceptionWord⟩
      tick := post.tick
      geometry := h.geometry.frame_vm rfl rfl h.outside.domain h.bindingsOutside.contents
        (ws := reentryWindows c)
        (by simp only [reentryWindows, reentryLog, LogInW, InsideW, or_false, and_true]
            exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
        (fun w hw => by
          simp only [reentryWindows, List.mem_singleton] at hw
          subst hw
          exact Or.inr ⟨Layout.off_local_roots, by simp [vmDomainOffsets], rfl⟩)
        post.memory
      native := h.native.frame_log h.outside.domain
        (h.native.region_of_arena (logInW_arena (ws := [⟨(word c Layout.sym_Caml_state).toNat +
            Layout.off_local_roots, (word c Layout.sym_Caml_state).toNat + Layout.off_local_roots + 8⟩])
          (by simp only [List.mem_singleton, forall_eq]
              exact h.geometry.domain_below (off := Layout.off_local_roots + 8) (by decide))
          (by simp only [reentryLog, LogInW, InsideW, or_false, and_true]; omega)))
        post.memory post.nativeStack
      htifIdle := post.htif.trans h.htifIdle }
    pc := post.pc
    trapReg := post.trap.trans (congrArg some trap)
    domainReg := ?_ }
  simpa only [domain] using post.domain

end OCaml.Vm.Sim
