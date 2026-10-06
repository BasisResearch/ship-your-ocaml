import OCaml.Vm.Sim.RaiseReentry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Trap-store geometry depends only on the domain and primitive-table pointers. -/
theorem TrapWriteOk.frame_observations {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high trap : Nat} {c after : Config} (h : TrapWriteOk P s c pl cp sp high trap)
    (domain : word after Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (contents : word after (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)) :
    TrapWriteOk P s after pl cp sp high trap := by
  refine ⟨h.highNat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [domain] using h.address
  · simpa only [domain] using h.window
  · rw [domain]
    exact {
      toPayloadCoreOutside := { h.payload.toPayloadCoreOutside with stackHigh := by simpa only [domain] using h.payload.stackHigh }
      stack := h.payload.stack, heap := h.payload.heap }
  · simpa only [domain] using h.image
  · exact ⟨by simpa only [domain] using h.young.limit, by simpa only [domain] using h.young.ptr⟩
  · rw [domain]
    exact ⟨h.bindings.contents, by simpa only [contents] using h.bindings.entries⟩

/-- Geometry and runtime preservation for a caught exception after nonlocal return.
All fields describe data or footprints; native execution is proved separately. -/
structure CaughtReentryGeometry (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (nativeSp sp high dest : Nat) (link extra : BitVec 63) (env : Val) (rest : List Val) (c : Config) : Prop where
  highRead : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8
  nativeHighRead : RamReadAt nativeSp 8
  nativeSpRead : RamReadAt (nativeSp + 8) 8
  savedBoundary : word c nativeSp = word c (nativeSp + 8)
  savedHighOutside : OutLRange (reentryLog nativeSp c) nativeSp 8
  savedSpOutside : OutLRange (reentryLog nativeSp c) (nativeSp + 8) 8
  nonnegative : 0 ≤ extra.toInt
  reads : RaiseFrameReads (high - 8 * s.trap)
  space : TrapWriteOk P s c pl cp sp high (s.trap - link.toNat)
  stableRead : MemoryStable L.runtimeOk
  stableRoots : WindowStable L.runtimeOk (reentryWindows c)
  stableTrap : WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
    (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩]

structure CaughtReentryReady (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (nativeSp sp high dest : Nat) (link extra : BitVec 63) (env : Val) (rest : List Val) (c : Config) : Prop
    extends RaiseReentryReady L P s pl cp nativeSp sp high dest link extra env rest c,
      CaughtReentryGeometry L P s pl cp nativeSp sp high dest link extra env rest c

/-- Rebase handler geometry using only the runtime pointers and saved boundary words. -/
theorem CaughtReentryGeometry.frame_observations {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {nativeSp sp high dest : Nat} {link extra : BitVec 63}
    {env : Val} {rest : List Val} {c after : Config}
    (h : CaughtReentryGeometry L P s pl cp nativeSp sp high dest link extra env rest c)
    (domain : word after Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (contents : word after (Layout.sym_caml_prim_table + Layout.off_prim_contents) = word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (savedHigh : word after nativeSp = word c nativeSp)
    (savedSp : word after (nativeSp + 8) = word c (nativeSp + 8))
    (roots : reentryLog nativeSp after = reentryLog nativeSp c) :
    CaughtReentryGeometry L P s pl cp nativeSp sp high dest link extra env rest after := by
  refine {
    h with
    highRead := by simpa only [domain] using h.highRead
    savedBoundary := savedHigh.trans (h.savedBoundary.trans savedSp.symm)
    savedHighOutside := by rw [roots]; exact h.savedHighOutside
    savedSpOutside := by rw [roots]; exact h.savedSpOutside
    space := h.space.frame_observations domain contents
    stableRoots := by simpa only [reentryWindows, domain] using h.stableRoots
    stableTrap := by simpa only [domain] using h.stableTrap }

/-- Complete the caught check and handler after the local-roots restoration. -/
theorem reentry_handler {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {nativeSp sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val} {c middle : Config}
    (h : CaughtReentryReady L P s pl cp nativeSp sp high dest link extra env rest c)
    (post : ReentryControl nativeSp c middle) :
    ∃ count after, StepsN count middle after ∧ Running L P
      {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat} after := by
  have input := raise_reentry_restore h.toRaiseReentryReady h.stableRoots post
  have copy (a : Nat) (outside : OutLRange (reentryLog nativeSp c) a 8) :
      word middle a = word c a := Reloc.bytesT_congr (copied_of_writeLog post.memory outside)
  have domain := copy _ h.outside.domain
  have contents := copy _ h.bindingsOutside.contents
  have saved : RaiseStackFrame nativeSp middle := ⟨post.nativeStack,
    (copy _ h.savedHighOutside).trans (h.savedBoundary.trans (copy _ h.savedSpOutside).symm),
    h.nativeHighRead, h.nativeSpRead⟩
  have highRead : RamReadAt ((word middle Layout.sym_Caml_state).toNat + Layout.off_stack_high) 8 := by
    simpa only [domain] using h.highRead
  obtain ⟨checkCount, handler, checkRun, checked⟩ := raise_check input h.stableRead saved highRead
  have handlerDomain : word handler Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    simpa only [word, checked.memory] using domain
  have stable : WindowStable L.runtimeOk [⟨(word handler Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word handler Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩] := by
    simpa only [handlerDomain] using h.stableTrap
  obtain ⟨handlerCount, after, handlerRun, result⟩ := raise_handler checked.state h.nonnegative stable h.reads
    ((h.space.frame_observations domain contents).frame checked.memory)
  exact ⟨checkCount + handlerCount, after, checkRun.append handlerRun, result⟩

/-- The complete native nonlocal return reaches a represented bytecode handler. -/
theorem longjmp_caught {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {buffer nativeSp sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    {saved : Nat → BitVec 64} {value : BitVec 64} {c : Config}
    (jump : LongjmpInput buffer saved value c) (memory : ReentryMemory nativeSp c)
    (h : CaughtReentryReady L P s pl cp nativeSp sp high dest link extra env rest c)
    (returnPc : saved 1 = 0x80001e80#64) (returnSp : saved 2 = BitVec.ofNat 64 nativeSp) :
    FnSummary (0x80042c8c#64) (fun start => start = c) (Running L P
      {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat}) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, jumpRun, post⟩ := (longjmp_reentry jump memory returnPc returnSp).run c ⟨pc, rfl⟩
  obtain ⟨count, after, run, represented⟩ := reentry_handler h post.toReentryControl
  exact ⟨after, jumpRun.trans run.toSteps, represented⟩

end OCaml.Vm.Sim
