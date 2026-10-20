import OCaml.Vm.Sim.CcallAllocation

/-!
# C_CALL returns across a footprint predicate

`ccall_observed_summary` frames a primitive by a write log. A primitive that
calls into the runtime's own allocators (custom blocks, newlib's heap) writes
bytes no log names: its footprint is a predicate `W`. The C-call frame, the
native invocation and the adapter carry over with "the range misses `W`"
(`Misses`) in place of `OutLRange log`. The log forms are the instance
`W x := ¬ OutL log x` (`Misses.of_outLRange`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The `n` bytes from `a` miss the footprint `W`. -/
def Misses (W : Nat → Prop) (a n : Nat) : Prop := ∀ i, i < n → ¬ W (a + i)

theorem Misses.of_outLRange {log : List WEntry} {a n : Nat} (h : OutLRange log a n) :
    Misses (fun x => ¬ OutL log x) a n :=
  fun _ hi w => w (outL_of_range h (by omega) (by omega))

theorem Misses.word {W : Nat → Prop} {c c' : Config} {a : Nat} (h : Misses W a 8)
    (memory : ∀ x, ¬ W x → byte c' x = byte c x) : word c' a = word c a :=
  Reloc.bytesT_congr fun i hi => memory _ (h i hi)

/-- **The native invocation across a footprint predicate.** -/
theorem Invocation.frame_on {D : InvocationData} {c c' : Config} {W : Nat → Prop} (h : Invocation D c)
    (domain : Misses W Layout.sym_Caml_state 8)
    (region : ∀ r ∈ invocationRanges, Misses W (D.nativeSp + r.1) r.2)
    (externalRaise : Misses W (D.domain.toNat + Layout.off_external_raise) 8)
    (memory : ∀ x, ¬ W x → byte c' x = byte c x) (stack : gpr c' 2 = gpr c 2) : Invocation D c' where
  stack := stack.trans h.stack
  domain := (domain.word memory).trans h.domain
  region r hr i hi := (memory _ (region r hr i hi)).trans (h.region r hr i hi)
  externalRaise := (externalRaise.word memory).trans h.externalRaise

/-- **A footprint below the native stack pointer** keeps the native invocation. -/
theorem NativePlaced.frame_below_on {c c' : Config} {W : Nat → Prop} (n : NativePlaced c)
    (below : ∀ sp, gpr c 2 = some (BitVec.ofNat 64 sp) → ∀ x, W x → x < sp)
    (domain : Misses W Layout.sym_Caml_state 8)
    (external : Misses W ((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise) 8)
    (memory : ∀ x, ¬ W x → byte c' x = byte c x) (stack : gpr c' 2 = gpr c 2) : NativePlaced c' := by
  obtain ⟨D, inv, valid⟩ := n
  have under := below D.nativeSp inv.stack
  rw [inv.domain] at external
  exact ⟨D, inv.frame_on domain (fun r _ i _ w => by have := under _ w; omega) external memory stack, valid⟩

/-- The saved C-call words miss the footprint. -/
structure CcallSavedMisses (W : Nat → Prop) (domain frameSp : BitVec 64) : Prop where
  domainPtr : Misses W Layout.sym_Caml_state 8
  externSp : Misses W (domain + BitVec.ofNat 64 Layout.off_extern_sp).toNat 8
  env : Misses W frameSp.toNat 8
  externalRaise : Misses W (domain.toNat + Layout.off_external_raise) 8

/-- **The saved C-call frame across a footprint predicate.** -/
theorem Ccall1Saved.frame_on {s : St} {pl : Place} {sp : Nat} {domain frameSp env : BitVec 64}
    {before after : Config} {W : Nat → Prop} (h : Ccall1Saved s pl sp domain frameSp env before)
    (outside : CcallSavedMisses W domain frameSp)
    (memory : ∀ x, ¬ W x → byte after x = byte before x)
    (regs : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r) :
    Ccall1Saved s pl sp domain frameSp env after := { h with
  domainReg := (regs _ (by decide)).trans h.domainReg
  pc := (regs _ (by decide)).trans h.pc
  extra := (regs _ (by decide)).trans h.extra
  domainWord := h.domainWord.trans (outside.domainPtr.word memory).symm
  savedStack := h.savedStack.trans (outside.externSp.word memory).symm
  savedEnv := h.savedEnv.trans (outside.env.word memory).symm }

/-- A primitive call's machine facts with a footprint predicate. -/
structure FramedCallOn (W : Nat → Prop) (before : Config) (ra w : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  pc : pcOf after = some ra
  result : gpr after 10 = some w
  memory : ∀ x, ¬ W x → byte after x = byte before x
  saved : ∀ r ∈ callSavedRegs, after.σ.regs.get? r = before.σ.regs.get? r

/-- A represented primitive result after a call framed by a predicate. -/
structure FramedPrimitivePostOn (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (name : String) (args : List Val)
    (v : Val) (w : BitVec 64) (heapAfter : Heap) (worldAfter : World)
    (W : Nat → Prop) (before : Config) (ra : BitVec 64) (after : Config) : Prop where
  call : FramedCallOn W before ra w after
  data : VmPayload P {s with accu := v, heap := heapAfter, world := worldAfter} after pl cp sp high
  primitives : PrimitiveBindings P after
  platform : PlatformOk runtimeOk after
  loop : LoopRegisters after
  resultRepr : valWord pl v = some w
  semantics : primF1Impl name args s.heap s.world = .ok v heapAfter worldAfter
  gprs : GprsKept before after

/-- **Adapt a primitive framed by a footprint predicate to the C_CALL return
boundary**: `ccall_observed_summary` with `Misses` for the saved words and a
footprint below the native stack pointer. -/
theorem ccall_observed_summary_on {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {name : String} {v : Val}
    {heap : Heap} {world : World} {domain frameSp result env entry ra : BitVec 64} {pc : Nat}
    {args : List Val} {W : Nat → Prop} {before : Config}
    (S : FnSummary entry (fun c => c = before) (fun after =>
      FramedPrimitivePostOn L.runtimeOk P s pl cp sp high name args v result heap world W before ra after ∧
        OCaml.LoopGeometry L P {s with accu := v, heap := heap, world := world} after pl cp high))
    (saved : Ccall1Saved {s with pc := pc} pl sp domain frameSp env before)
    (outside : CcallSavedMisses W domain frameSp)
    (below : ∀ n, gpr before 2 = some (BitVec.ofNat 64 n) → ∀ x, W x → x < n)
    (native : NativePlaced before) :
    FnSummary entry (fun c => c = before)
      (CcallReturn ra L P {s with pc := pc, accu := v, heap := heap, world := world}
        pl cp sp high domain frameSp result env) := by
  apply S.weaken (fun _ h => h)
  intro after ⟨post, geometry⟩
  have frame := post.call.memory
  have regs := post.call.saved
  have kept := saved.frame_on outside frame regs
  refine ⟨cp, ?_⟩
  exact { toCcall1Saved := { kept with pc := kept.pc }
          toCcallResult :=
            { geometry := geometry.state rfl rfl
              native := native.frame_below_on below outside.domainPtr
                (saved.domainWord ▸ outside.externalRaise) frame (regs _ (by decide))
              data := payload_pc post.data pc
              primitives := post.primitives
              platform := post.platform
              loop := post.loop
              tick := post.call.tick
              returnPC := post.call.pc
              resultReg := post.call.result
              resultRepr := post.resultRepr } }

end OCaml.Vm.Sim
