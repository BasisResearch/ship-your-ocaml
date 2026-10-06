import OCaml.Vm.Sim.CcallReturn
import OCaml.Vm.Primitives.GprsKept

/-!
# Writing primitives at the C_CALL return boundary

A writing primitive's post frames memory outside its footprint log
(`∀ x, OutL footprint x → byte after x = byte before x`). When the footprint
misses the caller's saved C-call words (`CcallSavedOutside`) and lies in the
allocator arena (below the native frames), the saved frame and the native
invocation survive, and the primitive's post becomes the arm's `CcallReturn`.
The arm geometry after the call is the caller's premise: it depends on how
the primitive changes the heap (`ArmGeometry.frame_log`/`transport`/`alloc_log`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- A footprint frame keeps every word it misses. -/
theorem word_of_outside {c c' : Config} {log : List WEntry} {a : Nat}
    (memory : ∀ x, OutL log x → byte c' x = byte c x) (outside : OutLRange log a 8) :
    word c' a = word c a :=
  Reloc.bytesT_congr (copied_of_outsideLog memory outside)

/-- **The native invocation across a footprint in the arena.** -/
theorem NativePlaced.frame_outside {c c' : Config} {log : List WEntry} (n : NativePlaced c)
    (inside : LogInW [arenaWindow] log) (domain : OutLRange log Layout.sym_Caml_state 8)
    (external : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8)
    (memory : ∀ x, OutL log x → byte c' x = byte c x) (stack : gpr c' 2 = gpr c 2) : NativePlaced c' := by
  obtain ⟨D, inv, valid⟩ := n
  rw [inv.domain] at external
  refine ⟨D, inv.frame ⟨domain, fun r _ => outLRange_of_windows inside ⟨?_, trivial⟩, external⟩ memory stack, valid⟩
  have := valid.low
  exact Or.inr (by simp only [arenaWindow]; omega)

/-- The caller's saved C-call words a primitive footprint must miss. -/
structure CcallSavedOutside (log : List WEntry) (domain frameSp : BitVec 64) : Prop where
  domainPtr : OutLRange log Layout.sym_Caml_state 8
  externSp : OutLRange log (domain + BitVec.ofNat 64 Layout.off_extern_sp).toNat 8
  env : OutLRange log frameSp.toNat 8
  /-- the interpreter's `external_raise` (the invocation's jump buffer) -/
  externalRaise : OutLRange log (domain.toNat + Layout.off_external_raise) 8

/-- **The saved C-call frame across a footprint.** -/
theorem Ccall1Saved.frame_outside {s : St} {pl : Place} {sp : Nat} {domain frameSp env : BitVec 64}
    {before after : Config} {log : List WEntry} (h : Ccall1Saved s pl sp domain frameSp env before)
    (outside : CcallSavedOutside log domain frameSp)
    (memory : ∀ x, OutL log x → byte after x = byte before x)
    (regs : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r) :
    Ccall1Saved s pl sp domain frameSp env after := { h with
  domainReg := (regs _ (by decide)).trans h.domainReg
  pc := (regs _ (by decide)).trans h.pc
  extra := (regs _ (by decide)).trans h.extra
  domainWord := h.domainWord.trans (word_of_outside memory outside.domainPtr).symm
  savedStack := h.savedStack.trans (word_of_outside memory outside.externSp).symm
  savedEnv := h.savedEnv.trans (word_of_outside memory outside.env).symm }

/-- **Adapt a writing primitive's summary to the C_CALL return boundary.** -/
theorem ccall_writing_summary {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {heap : Heap} {world : World} {domain frameSp result env entry ra : BitVec 64} {pc : Nat}
    {args : List Val} {writes : List Nat} {expected : Std.ExtHashMap Nat (BitVec 8)}
    {footprint : List WEntry} {before : Config}
    (S : FnSummary entry (fun c => c = before)
      (PrimitivePost L.runtimeOk P s pl cp sp high name args v result heap world writes expected before ra))
    (preserved : ∀ r ∈ callSavedRegs, ∀ n ∈ writes, gprReg n ≠ r)
    (memory : ∀ after : Config, after.σ.mem = expected → ∀ x, OutL footprint x → byte after x = byte before x)
    (saved : Ccall1Saved {s with pc := pc} pl sp domain frameSp env before)
    (outside : CcallSavedOutside footprint domain frameSp)
    (arena : LogInW [arenaWindow] footprint)
    (geometry : ∀ after : Config, (∀ x, OutL footprint x → byte after x = byte before x) →
      OCaml.LoopGeometry L P {s with accu := v, heap := heap, world := world} after pl cp high)
    (native : NativePlaced before) :
    FnSummary entry (fun c => c = before)
      (CcallReturn ra L P {s with pc := pc, accu := v, heap := heap, world := world}
        pl cp sp high domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after post
  have frame := memory after post.call.memory
  have regs : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r :=
    fun r hr => post.call.frame r (preserved r hr) (by revert r; decide)
  exact ccall_primitive_return post (saved.frame_outside outside frame regs) (geometry after frame)
    (native.frame_outside arena outside.domainPtr (saved.domainWord ▸ outside.externalRaise) frame
      (regs _ (by decide)))

/-! ## Framed calls (console output, nested native frames) -/

/-- **The native invocation across a footprint below the native stack
pointer**: the callee's own frames lie below the interpreter's, so the
footprint misses every saved invocation range. -/
theorem NativePlaced.frame_below {c c' : Config} {log : List WEntry} (n : NativePlaced c)
    (below : ∀ sp, gpr c 2 = some (BitVec.ofNat 64 sp) → LogInW [⟨0, sp⟩] log)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (external : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8)
    (memory : ∀ x, OutL log x → byte c' x = byte c x) (stack : gpr c' 2 = gpr c 2) : NativePlaced c' := by
  obtain ⟨D, inv, valid⟩ := n
  have inside := below D.nativeSp inv.stack
  rw [inv.domain] at external
  exact ⟨D, inv.frame ⟨domain, fun r _ => outLRange_of_windows inside ⟨Or.inr (by dsimp only; omega), trivial⟩,
    external⟩ memory stack, valid⟩

/-- **A framed primitive call**: return state, result register, a memory frame
outside the footprint, and the caller-saved VM registers. No output or exact
memory claim (console writes extend the output). -/
structure FramedCall (footprint : List WEntry) (before : Config) (ra w : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some w
  memory : ∀ x, OutL footprint x → byte after x = byte before x
  saved : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r

/-- A represented primitive result after a framed call. -/
structure FramedPrimitivePost (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (v : Val) (w : BitVec 64) (heapAfter : Heap) (worldAfter : World)
    (footprint : List WEntry) (before : Config) (ra : BitVec 64) (after : Config) : Prop where
  call : FramedCall footprint before ra w after
  data : VmPayload P {s with accu := v, heap := heapAfter, world := worldAfter} after pl cp sp high
  primitives : PrimitiveBindings P after
  platform : PlatformOk runtimeOk after
  loop : LoopRegisters after
  resultRepr : valWord pl v = some w
  semantics : primF1Impl name args s.heap s.world = .ok v heapAfter worldAfter
  /-- register presence and `gp` kept, so the C_CALL return re-establishes
  `LoopRegisters.gprs` -/
  gprs : OCaml.Vm.Primitives.GprsKept before after

/-- **Adapt a framed primitive summary to the C_CALL return boundary.** -/
theorem ccall_framed_summary {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {heap : Heap} {world : World} {domain frameSp result env entry ra : BitVec 64} {pc : Nat}
    {args : List Val} {footprint : List WEntry} {before : Config}
    (S : FnSummary entry (fun c => c = before)
      (FramedPrimitivePost L.runtimeOk P s pl cp sp high name args v result heap world footprint before ra))
    (saved : Ccall1Saved {s with pc := pc} pl sp domain frameSp env before)
    (outside : CcallSavedOutside footprint domain frameSp)
    (below : ∀ n, gpr before 2 = some (BitVec.ofNat 64 n) → LogInW [⟨0, n⟩] footprint)
    (geometry : ∀ after : Config, (∀ x, OutL footprint x → byte after x = byte before x) →
      OCaml.LoopGeometry L P {s with accu := v, heap := heap, world := world} after pl cp high)
    (native : NativePlaced before) :
    FnSummary entry (fun c => c = before)
      (CcallReturn ra L P {s with pc := pc, accu := v, heap := heap, world := world}
        pl cp sp high domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after post
  have frame := post.call.memory
  have regs := post.call.saved
  have kept := saved.frame_outside outside frame regs
  exact { toCcall1Saved := { kept with pc := kept.pc }
          toCcallResult :=
            { geometry := (geometry after frame).state rfl rfl
              native := native.frame_below below outside.domainPtr (saved.domainWord ▸ outside.externalRaise)
                frame (regs _ (by decide))
              data := payload_pc post.data pc
              primitives := post.primitives
              platform := post.platform
              loop := post.loop
              tick := post.call.tick
              returnPC := post.call.pc
              resultReg := post.call.result
              resultRepr := post.resultRepr } }

end OCaml.Vm.Sim
