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

/-- **`ChanAt` across a footprint that may write the record's refcount**
(`+64`, which `ChanAt` does not read). -/
theorem chanAt_frame {c c' : Config} {a : Nat} {ch : Chan} (h : ChanAt c a ch)
    (same : ∀ j, j < chanOffBuff + ioBufferSize → (j < 64 ∨ 68 ≤ j) → byte c' (a + j) = byte c (a + j)) :
    ChanAt c' a ch := by
  have bf : chanOffBuff + ioBufferSize = 65608 := rfl
  have w8 : ∀ off, (off + 8 ≤ 64 ∨ 68 ≤ off) → off + 8 ≤ 65608 → word c' (a + off) = word c (a + off) :=
    fun off h1 h2 => Reloc.bytesT_congr fun i hi => by
      rw [Nat.add_assoc]; exact same _ (by omega) (by omega)
  have w4 : ∀ off, (off + 4 ≤ 64 ∨ 68 ≤ off) → off + 4 ≤ 65608 → word32 c' (a + off) = word32 c (a + off) :=
    fun off h1 h2 => Reloc.bytesT_congr fun i hi => by
      rw [Nat.add_assoc]; exact same _ (by omega) (by omega)
  obtain ⟨fd, off, curr, max, end_, unbuf, buf, bounds, managed⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, bounds, ?_⟩
  · rw [w4 chanOffFd (by simp [chanOffFd]) (by simp [chanOffFd])]; exact fd
  · rw [w8 chanOffOffset (by simp [chanOffOffset]) (by simp [chanOffOffset])]; exact off
  · rw [w8 chanOffCurr (by simp [chanOffCurr]) (by simp [chanOffCurr])]; exact curr
  · rw [w8 chanOffMax (by simp [chanOffMax]) (by simp [chanOffMax])]; exact max
  · rw [w8 chanOffEnd (by simp [chanOffEnd]) (by simp [chanOffEnd])]; exact end_
  · rw [w4 chanOffFlags (by simp [chanOffFlags]) (by simp [chanOffFlags])]; exact unbuf
  · intro i b hb
    have hi := (List.getElem?_eq_some_iff.mp hb).1
    have := bounds.2.1
    rw [Nat.add_assoc, same _ (by simp only [chanOffBuff, ioBufferSize] at this ⊢; omega)
      (by simp only [chanOffBuff]; omega), ← Nat.add_assoc]
    exact buf i b hb
  · rw [w4 chanOffFlags (by simp [chanOffFlags]) (by simp [chanOffFlags])]; exact managed

/-- The VM payload's words miss the footprint `W` (channel records except
their refcounts). -/
structure PayloadMisses (W : Nat → Prop) (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp : Nat) : Prop where
  domain : Misses W Layout.sym_Caml_state 8
  stackHigh : Misses W ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  trapsp : Misses W ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  codeBase : Misses W Layout.sym_caml_start_code 8
  atomBase : Misses W Layout.sym_caml_atom_table 8
  globals : Misses W Layout.sym_caml_global_data 8
  argv : Misses W Layout.sym_main_argv 8
  ooId : Misses W Layout.sym_oo_last_id 8
  code : ∀ i w, P.code[i]? = some w → Misses W (pl.codeBase + 4 * i) 4
  stack : ∀ i v, s.stack[i]? = some v → Misses W (sp + 8 * i) 8
  header : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o → Misses W (a - 8) 8
  payload : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    Misses W a (8 * o.wosize)
  channels : ∀ id ch a, s.world.chans[id]? = some ch → cp id = some a →
    ∀ j, j < chanOffBuff + ioBufferSize → (j < 64 ∨ 68 ≤ j) → ¬ W (a + j)
  named : ∀ x, NamedPlFoot pl s.world.named x → ¬ W x

/-- **The VM payload across a footprint predicate.** -/
theorem VmPayload.frame_on {P : Prog} {s : St} {c c' : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    {W : Nat → Prop} (h : VmPayload P s c pl cp sp high) (outside : PayloadMisses W P s c pl cp sp)
    (memory : ∀ x, ¬ W x → byte c' x = byte c x) (outputEq : output c'.σ = output c.σ) :
    VmPayload P s c' pl cp sp high := by
  have copy : ∀ a n, Misses W a n → Reloc.Copied c c' a a n := fun a n m i hi => memory _ (m i hi)
  have hw : ∀ a, Misses W a 8 → word c' a = word c a := fun a m => m.word memory
  have domain := hw _ outside.domain
  constructor
  · rw [domain, hw _ outside.stackHigh]; exact h.stackHigh
  · rw [domain, hw _ outside.trapsp]; exact h.trapsp
  · rw [hw _ outside.codeBase]; exact h.codeBase
  · intro i w hi
    have he : word32 c' (pl.codeBase + 4 * i) = word32 c (pl.codeBase + 4 * i) :=
      Reloc.bytesT_congr (copy _ 4 (outside.code i w hi))
    simpa only [he] using h.code i w hi
  · rw [hw _ outside.globals]; exact h.globals
  · refine ⟨h.stack.1, fun i v hi => ?_⟩
    rw [hw _ (outside.stack i v hi)]; exact h.stack.2 i v hi
  · constructor
    · intro l hl
      obtain ⟨a, o, ha, ho, layout⟩ := h.heap.1 l hl
      exact ⟨a, o, ha, ho, object_copied layout (copy _ 8 (outside.header l a o hl ha ho))
        (copy _ _ (outside.payload l a o hl ha ho))⟩
    · exact h.heap.2
  · refine ⟨?_, ?_, ?_⟩
    · rw [outputEq]; exact h.world.output
    · intro id ch hc
      obtain ⟨a, ha, layout⟩ := h.world.chans id ch hc
      exact ⟨a, ha, chanAt_frame layout fun j hj hn => memory _ (outside.channels id ch a hc ha j hj hn)⟩
    · rw [hw _ outside.ooId]; exact h.world.ooId
  · rw [hw _ outside.atomBase]; exact h.atomBase
  · rw [hw _ outside.argv]; exact h.argv
  · obtain ⟨chains, table⟩ := h.named
    exact ⟨chains, table.frame fun x f => memory x (outside.named x (table.foot_sub f))⟩

end OCaml.Vm.Sim
