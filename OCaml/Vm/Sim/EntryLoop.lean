import OCaml.Vm.Sim.EntryNative
import OCaml.Vm.Sim.ReadOnly

/-!
# `ArmSim.entry`: from `Loaded` to the loop head

The native entry run (`entry_native`) writes only inside `entryFootprint`:
the interpreter's native frame, `caml_callback_depth` and
`Caml_state->external_raise`. The caller premise (`InterpCaller`) says that
footprint misses everything the initial representation observes, so the
loaded payload frames to the loop head, where the VM registers are those of
`P.init`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- A footprint entry's range misses whatever the footprint misses. -/
theorem outLRange_mem {fp : List WEntry} {f : WEntry} {a n : Nat} (hf : f ∈ fp)
    (h : OutLRange fp a n) : a + n ≤ f.1 ∨ f.1 + f.2.1 ≤ a := by
  induction fp with
  | nil => simp at hf
  | cons g fp ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · exact ih hf h.2

/-- **Cover**: a log whose entries lie inside footprint entries misses whatever
the footprint misses. -/
theorem outLRange_of_cover {log fp : List WEntry} {a n : Nat}
    (cover : ∀ e ∈ log, ∃ f ∈ fp, f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1)
    (h : OutLRange fp a n) : OutLRange log a n := by
  induction log with
  | nil => trivial
  | cons e log ih =>
    obtain ⟨f, hf, lo, hi⟩ := cover e (by simp)
    have := outLRange_mem hf h
    exact ⟨by omega, ih (fun e' he' => cover e' (by simp [he']))⟩

/-- The payload separation transfers along a cover. -/
theorem _root_.OCaml.Vm.Primitives.PayloadOutside.cover {log fp : List WEntry} {P : Prog} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {sp : Nat} (h : PayloadOutside fp P s c pl cp sp)
    (cover : ∀ e ∈ log, ∃ f ∈ fp, f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1) :
    PayloadOutside log P s c pl cp sp where
  domain := outLRange_of_cover cover h.domain
  stackHigh := outLRange_of_cover cover h.stackHigh
  trapsp := outLRange_of_cover cover h.trapsp
  codeBase := outLRange_of_cover cover h.codeBase
  atomBase := outLRange_of_cover cover h.atomBase
  globals := outLRange_of_cover cover h.globals
  code i w hi := outLRange_of_cover cover (h.code i w hi)
  stack i v hi := outLRange_of_cover cover (h.stack i v hi)
  heap l a o hl ha ho := ⟨outLRange_of_cover cover (h.heap l a o hl ha ho).header,
    outLRange_of_cover cover (h.heap l a o hl ha ho).payload⟩
  channels id ch a hc ha := outLRange_of_cover cover (h.channels id ch a hc ha)

/-- Entry writes only inside its footprint. -/
theorem entryLog_cover {sp : Nat} {regs : Nat → BitVec 64} {a0 : BitVec 64} {c : Config}
    (frame : EntryFrame sp) :
    ∀ e ∈ entryLog sp regs a0 c, ∃ f ∈ entryFootprint sp (word c Layout.sym_Caml_state).toNat,
      f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1 := by
  obtain ⟨b1, b2, b3⟩ := frame.nat
  intro e he
  simp only [entryLog, entrySaveLog, entryPrepLog, setjmpLog, entryResumeLog, Layout.interpSavedRegs,
    List.map, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact ⟨(sp - Layout.interpFrameBytes, Layout.interpFrameBytes, 0), by simp [entryFootprint],
        by simp only [Layout.interpFrameBytes, Layout.interpSaveOffset, entryBuffer]; omega,
        by simp only [Layout.interpFrameBytes, Layout.interpSaveOffset, entryBuffer]; omega⟩
    | exact ⟨(Layout.sym_caml_callback_depth, 4, 0), by simp [entryFootprint], Nat.le_refl _, Nat.le_refl _⟩
    | exact ⟨((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise, 8, 0),
        by simp [entryFootprint], Nat.le_refl _, Nat.le_refl _⟩

/-- The windows of a footprint. -/
def footprintWindows (fp : List WEntry) : List W := fp.map fun f => ⟨f.1, f.1 + f.2.1⟩

/-- A covered log stays inside its footprint's windows. -/
theorem logInW_of_cover {log fp : List WEntry}
    (cover : ∀ e ∈ log, ∃ f ∈ fp, f.1 ≤ e.1 ∧ e.1 + e.2.1 ≤ f.1 + f.2.1) :
    LogInW (footprintWindows fp) log := by
  induction log with
  | nil => trivial
  | cons e log ih =>
    refine ⟨?_, ih (fun e' he' => cover e' (by simp [he']))⟩
    obtain ⟨f, hf, lo, hi⟩ := cover e (by simp)
    clear ih cover
    induction fp with
    | nil => simp at hf
    | cons g fp ih' =>
      rcases List.mem_cons.mp hf with rfl | hf
      · exact Or.inl ⟨lo, hi⟩
      · exact Or.inr (ih' hf)

/-- Entry's windows, for the runtime invariant's stability premise. -/
abbrev entryWindows (sp domain : Nat) : List W := footprintWindows (entryFootprint sp domain)

/-- Words of an intact invocation range read as in the snapshot's source. -/
theorem Invocation.word_eq {D : InvocationData} {c c' : Config} (inv : Invocation D c')
    (snap : ∀ x, D.snapshot x = byte c x) {r : Nat × Nat} {off : Nat} (hr : r ∈ invocationRanges)
    (h : off + 8 ≤ r.2) : word c' (D.nativeSp + r.1 + off) = word c (D.nativeSp + r.1 + off) := by
  unfold word
  apply Reloc.bytesT_congr
  intro j hj
  have e := inv.region r hr (off + j) (by omega)
  rw [snap] at e
  simpa only [byte, Nat.add_assoc] using e

/-- The loaded payload at the cut. -/
theorem _root_.OCaml.LoadedAt.payload {L : OCaml.Layout} {P : Prog} {c : Config} {pl : Place} {cp : ChanPlace}
    {high : Nat} (h : OCaml.LoadedAt L P c pl cp high) : VmPayload P P.init c pl cp high high where
  stackHigh := h.stackHigh
  trapsp := by simpa [Prog.init] using h.trapsp
  codeBase := h.codeBase
  code := h.code
  globals := h.globals
  stack := ⟨by simp [Prog.init], fun i v hi => by simp [Prog.init] at hi⟩
  heap := h.heap
  world := h.world
  atomBase := h.atomBase

/-- Close an `OutLRange` goal over the flattened entry log. -/
macro "log_out" : tactic =>
  `(tactic| (simp only [Vsa.Sim.OutLRange, entryLog, entrySaveLog, entryPrepLog, setjmpLog, entryResumeLog,
      OCaml.Vm.Layout.interpSavedRegs, List.map, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero, OCaml.Vm.Layout.interpSaveOffset, OCaml.Vm.Layout.interpFrameBytes,
      OCaml.Vm.Layout.camlMainSaveOffset, OCaml.Vm.Layout.sym_caml_callback_depth,
      OCaml.Vm.Layout.off_external_raise, entryBuffer, and_true]; omega))

/-- **`ArmSim.entry`**: from the loaded cut, the machine reaches the loop head
representing `P.init`, at least one step later. The named premises are the
caller (`InterpCaller`), the stack geometry at the cut, and stability of the
runtime invariant under entry's three write windows. -/
theorem entry_loopAt {L : OCaml.Layout} {P : Prog} {c : Config} {pl : Place} {cp : ChanPlace}
    {high sp : Nat} {callerRegs mainSaved : Nat → BitVec 64}
    (h : OCaml.LoadedAt L P c pl cp high)
    (caller : InterpCaller P c pl cp high sp callerRegs mainSaved)
    (geometry : ArmGeometry P P.init c pl cp high)
    (stable : WindowStable L.runtimeOk (entryWindows sp (word c Layout.sym_Caml_state).toNat)) :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P P.init c' := by
  have frame := EntryFrame.of_caller caller
  obtain ⟨b1, b2, b3⟩ := frame.nat
  have domain : DomainWindow (word c Layout.sym_Caml_state).toNat :=
    ⟨caller.domainLow, caller.domainHigh, caller.domainAligned⟩
  obtain ⟨d1, d2, d3⟩ := domain.nat
  have codeLow := geometry.codeLow
  have codeArena := geometry.codeArena
  simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at codeLow codeArena
  have nonzero : BitVec.ofNat 64 pl.codeBase ≠ 0#64 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  obtain ⟨n, c5, run, p⟩ := entry_native (regs := callerRegs) (a0 := BitVec.ofNat 64 pl.codeBase)
    ⟨⟨h.platform.control, h.platform.image, caller.tick, h.atEntry, caller.stack, caller.regs, h.argCode,
      nonzero, frame⟩, domain⟩
  have cover := entryLog_cover (regs := callerRegs) (a0 := BitVec.ofNat 64 pl.codeBase) (c := c) frame
  -- the loaded payload framed to the loop head
  have payload := h.payload.frame_log (caller.outside.cover cover) p.memory p.output
  have same (a : Nat) (o : OutLRange (entryFootprint sp (word c Layout.sym_Caml_state).toNat) a 8) :
      word c5 a = word c a := word_of_log p.memory (outLRange_of_cover cover o)
  have dom5 := same _ caller.outside.domain
  have prim5 := same _ caller.primTable
  have primitives : PrimitiveBindings P c5 := by
    refine ⟨fun i name hi => ?_⟩
    obtain ⟨entry, he, target⟩ := h.primitives.targets i name hi
    refine ⟨entry, he, ?_⟩
    simp only [primitiveTarget, prim5] at target ⊢
    rw [same _ (caller.primEntries i name hi)]
    exact target
  -- the VM registers of `P.init`
  have regs : VmRegisters P.init pl high c5 := by
    refine ⟨p.head, ?_, ?_, ⟨1#64, p.accu, by simp only [Prog.init, valWord]; decide⟩,
      ⟨word c Layout.sym_caml_atom_table + 8#64, p.env, ?_⟩, ?_⟩
    · show gpr c5 8 = some (BitVec.ofNat 64 (pl.codeBase + 4 * 0))
      simpa only [Nat.mul_zero, Nat.add_zero] using p.vmPc
    · rw [show Layout.reg_sp = 9 from rfl, p.vmSp, domainField, ← h.externSp, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    · simp only [Prog.init, valWord, Option.some.injEq, ← h.atomBase]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] <;> omega
    · show gpr c5 18 = some (BitVec.ofNat 64 0)
      exact p.extra

  -- the native invocation fixed here
  have native : NativePlaced c5 := by
    refine ⟨⟨sp - Layout.interpFrameBytes, word c Layout.sym_Caml_state, fun a => byte c5 a⟩,
      ⟨p.stack, dom5, fun _ _ _ _ => rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · dsimp only; simp only [Layout.interpFrameBytes, Vsa.Sim.DlHeap.heapEnd]; omega
    · dsimp only; simp only [Layout.interpFrameBytes, Layout.camlMainFrameBytes, Layout.sym_stack_top]; omega
    · dsimp only; simp only [Layout.interpFrameBytes]; omega
    · intro c' inv
      have e := inv.word_eq (c := c5) (fun _ => rfl) (r := (200, 440)) (off := 320) (by decide) (by decide)
      simp only [show Layout.interpSaveOffset 1 = 200 + 320 from rfl, ← Nat.add_assoc]
      rw [e, word, p.memory]
      have ra := OCaml.Vm.Gc.word_writeLog_at c.σ.mem (entryLog sp callerRegs (BitVec.ofNat 64 pl.codeBase) c)
        0 (sp - Layout.interpFrameBytes + Layout.interpSaveOffset 1) (callerRegs 1) rfl (by log_out)
      simp only [show Layout.interpSaveOffset 1 = 200 + 320 from rfl, ← Nat.add_assoc] at ra
      rw [ra, caller.ra]
    · intro c' inv
      have e := inv.word_eq (c := c5) (fun _ => rfl) (r := (200, 440)) (off := 432) (by decide) (by decide)
      have addr : sp - Layout.interpFrameBytes + Layout.interpFrameBytes + Layout.camlMainSaveOffset 1 =
          sp - Layout.interpFrameBytes + 200 + 432 := by
            simp only [Layout.interpFrameBytes, Layout.camlMainSaveOffset] <;> omega
      rw [addr, e, ← addr, show sp - Layout.interpFrameBytes + Layout.interpFrameBytes = sp by
        simp only [Layout.interpFrameBytes]; omega]
      rw [word_of_log p.memory (by log_out), caller.mainFrame 1 (by decide), caller.mainReturn]
    · intro c' inv
      have e0 := inv.word_eq (c := c5) (fun _ => rfl) (r := (0, 32)) (off := 0) (by decide) (by decide)
      have e8 := inv.word_eq (c := c5) (fun _ => rfl) (r := (0, 32)) (off := 8) (by decide) (by decide)
      simp only [Nat.add_zero] at e0 e8
      dsimp only
      rw [e0, e8, word, word, p.memory]
      have hi := OCaml.Vm.Gc.word_writeLog_at c.σ.mem (entryLog sp callerRegs (BitVec.ofNat 64 pl.codeBase) c)
        15 (sp - Layout.interpFrameBytes + 0) (domainField c Layout.off_stack_high)
        (by simp only [entryLog, entrySaveLog, entryPrepLog, Layout.interpSavedRegs, List.map, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.add_zero]) (by log_out)
      have ex := OCaml.Vm.Gc.word_writeLog_at c.σ.mem (entryLog sp callerRegs (BitVec.ofNat 64 pl.codeBase) c)
        17 (sp - Layout.interpFrameBytes + 8) (domainField c Layout.off_extern_sp)
        (by simp only [entryLog, entrySaveLog, entryPrepLog, Layout.interpSavedRegs, List.map, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.add_zero]) (by log_out)
      simp only [Nat.add_zero] at hi
      rw [hi, ex]
      apply BitVec.eq_of_toNat_eq
      simp only [domainField]
      rw [h.stackHigh, h.externSp]
  -- the runtime invariant through entry's windows
  have platform : PlatformOk L.runtimeOk c5 :=
    ⟨p.good, p.image, stable c c5 (by rw [p.memory]; exact frameOn_writeLog _ _ _ (logInW_of_cover cover))
      h.platform.runtime⟩
  -- entry's footprint misses the allocation pointers
  have young (off : Nat) (member : off ∈ [Layout.off_young_limit, Layout.off_young_ptr]) :
      word c5 ((word c Layout.sym_Caml_state).toNat + off) =
        word c ((word c Layout.sym_Caml_state).toNat + off) := by
    apply same
    have := caller.domainLow
    have := caller.domainHigh
    have := caller.frameLow
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp only [OutLRange, entryFootprint, interpFrame, Layout.interpFrameBytes, Layout.off_young_limit,
        Layout.off_young_ptr, Layout.off_external_raise, Layout.sym_caml_callback_depth,
        Layout.domainStateBytes, Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd, and_true] at * <;> omega
  have geometry5 := geometry.transport (s' := P.init) (fun l o' ho => ⟨o', ho, rfl⟩) rfl dom5 prim5
    (by simp only [OCaml.Vm.runtimeFields, OCaml.Vm.domainWord, dom5]; rw [young _ (by simp)])
    (by simp only [OCaml.Vm.runtimeFields, OCaml.Vm.domainWord, dom5]; rw [young _ (by simp)])
  refine ⟨c5, ?_, ⟨running_of_payload payload primitives platform regs p.loop geometry5 native, p.tick⟩⟩
  cases n with
  | zero =>
    cases run
    have := h.atEntry.symm.trans p.head
    simp [Layout.sym_caml_interprete, Layout.loopHead] at this
  | succ n => exact ⟨n, run⟩

end OCaml.Vm.Sim
