import OCaml.Vm.Sim.ArgvInput
import OCaml.Vm.Sim.PrimGetConfigReturns

/-!
# `caml_sys_get_argv` at every C_CALL site

The argv instance of `PrimGetConfigReturns`: the contract's input
(`GetArgvInput`) is assembled from the stage inputs of `ArgvInput.lean`, the
copied name is the executable name (`ExeNameAt`), the pair's second field is
`main_argv` (`VmPayload.argv`). The runtime frame is `PrimAllocFrame`, the
geometry two chained reservations (`LoopGeometry.reserve2`), the separation
the four windows `allocWindows N D Y 40`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ArgvTuple
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of)
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Memcpy

/-- The prepare block's loads at the callee entry. -/
def argvBd (c : Config) (R : Nat → BitVec 64) : List (BitVec 8) := (argvPrepareLoads c.σ.mem R).getD 0 []
def argvBe (c : Config) (R : Nat → BitVec 64) : List (BitVec 8) := (argvPrepareLoads c.σ.mem R).getD 1 []
def argvBr (c : Config) (R : Nat → BitVec 64) : List (BitVec 8) := (argvPrepareLoads c.σ.mem R).getD 2 []

/-- The memory after the prepare block, at the callee entry. -/
def argvMem (c : Config) (ra : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog c.σ.mem (prepareLog (cfgR c ra) (bytesVal .ld (argvBd c (cfgR c ra)))
    (bytesVal .ld (argvBr c (cfgR c ra))))

/-- A static word below the native frame reads through the four saves. -/
theorem argv_saved_read {c : Config} {N D Y Lm k : Nat} {ra : BitVec 64} (e : StringAllocEntry c N D Y Lm k)
    {x : Nat} (hx : x + 8 ≤ 0x86800000) :
    bytesVal .ld (read8 (writeLog c.σ.mem (savedLog (cfgR c ra))) x) = word c x := by
  have h2 : cfgR c ra 2 = BitVec.ofNat 64 N := by
    simp only [cfgR, if_neg (show (2 : Nat) ≠ 1 by decide)]; exact regsAt_of e.stack
  have nh := e.nativeHigh; have nl := e.nativeLow
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have hs : Layout.sym_stack_top = 0x88000000 := rfl
  rw [he] at nl; rw [hs] at nh
  simp only [nativeHeadroom] at nl
  rw [read8_value, bytesT_writeLog_out _ (by
    simp only [savedLog, frameSp, h2, frameSp_ofNat (N := N) (by omega) (by omega), ← BitVec.ofNat_add,
      OutLRange, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega)]
  rfl

theorem argvBd_val {c : Config} {N D Y Lm k : Nat} {ra : BitVec 64} (e : StringAllocEntry c N D Y Lm k)
    (wD : word c Layout.sym_Caml_state = BitVec.ofNat 64 D) :
    bytesVal .ld (argvBd c (cfgR c ra)) = BitVec.ofNat 64 D :=
  (argv_saved_read e (by decide)).trans wD

theorem argvBe_val {c : Config} {N D Y Lm k : Nat} {ra : BitVec 64} (e : StringAllocEntry c N D Y Lm k)
    (exe : ExeNamePlaced c) :
    bytesVal .ld (argvBe c (cfgR c ra)) = BitVec.ofNat 64 Gc.exeNameAddr :=
  (argv_saved_read e (by decide)).trans exe.pointer

/-- **`caml_sys_get_argv`'s contract input at the C_CALL callee entry.** -/
theorem argv_input {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env : BitVec 64} {c : Config} {N D Y Lm : Nat}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_sys_get_argv env c)
    (e : StringAllocEntry c N D Y Lm 40) (exe : ExeNamePlaced c)
    (namePlaced : pl.φ (s.heap.alloc (.bytes progExeName)).2 =
      some (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length).toNat)
    (pairPlaced : pl.φ ((afterName s).heap.alloc (argvPair s)).2 =
      some (tupleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64)).toNat)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    GetArgvInput L.runtimeOk P s pl cp sp high s.accu imageLive (argvMem c ra) (List.range' Gc.exeNameAddr 6)
      (cfgR c ra) (argvBd c (cfgR c ra)) (argvBe c (cfgR c ra)) (argvBr c (cfgR c ra)) Gc.exeNameAddr
      (imgM (argvMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) (word c Layout.sym_main_argv) c := by
  have nums := AllocNumbers.of_entry e
  have lr := setup.libraryReady
  have input := setup.input
  have hR1 := cfgR_one c ra
  have h2 : cfgR c ra 2 = BitVec.ofNat 64 N := by
    simp only [cfgR, if_neg (show (2 : Nat) ≠ 1 by decide)]; exact regsAt_of e.stack
  obtain ⟨wD, wY, wL⟩ := e.words
  have bdv := argvBd_val (ra := ra) e wD
  have bev := argvBe_val (ra := ra) e exe
  have nlow := setup.geometry.nursery.nurseryLow
  rw [e.limit] at nlow
  simp only [Gc.minorRegion] at nlow
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have prepIn := argv_prepareLog_in (R := cfgR c ra) (roots := bytesVal .ld (argvBr c (cfgR c ra))) (Y := Y)
    (D := D) (by omega) (by omega) (by omega) h2
  have F := frameSp_eq h2 (by omega) (by omega)
  have nums := AllocNumbers.of_entry e
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  -- the copy stage
  have copy := copy_memory_at prepare_call.link
    (argv_site (R := cfgR c ra) (roots := bytesVal .ld (argvBr c (cfgR c ra))) nums h2 input.image lr.gp
      wD wY wL exe nlow prepIn)
  have regs : GHolds c.σ (prepare_input (cfgR c ra)) := by
    simp only [prepare_input, GHolds]
    refine ⟨?_, cfgR_gpr (by decide) (lr.gprs 2 (by decide) (by decide)),
      cfgR_gpr (by decide) (lr.gprs 8 (by decide) (by decide)), cfgR_gpr (by decide) (lr.gprs 9 (by decide) (by decide)),
      cfgR_gpr (by decide) (lr.gprs 18 (by decide) (by decide)), trivial⟩
    rw [hR1]; exact input.raReg
  have layout : PrepareLayout (cfgR c ra) (bytesVal .ld ((argvPrepareLoads c.σ.mem (cfgR c ra)).getD 0 [])) := by
    have bdv' : bytesVal .ld ((argvPrepareLoads c.σ.mem (cfgR c ra)).getD 0 []) = BitVec.ofNat 64 D := bdv
    rw [bdv']
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rw [F]; exact frame_above_window (by rw [show Vsa.Sim.DlHeap.heapEnd = 0x86800000 from rfl]; omega) e.nativeHigh na (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rw [F]; exact frame_above_window (by rw [show Vsa.Sim.DlHeap.heapEnd = 0x86800000 from rfl]; omega) e.nativeHigh na (by omega) (by omega)
    · exact (window_of_nat (n := 0x80064d08) (by rw [tohost]; omega) (by omega) (by decide)).read
    · rw [show (288#64 : BitVec 64) = BitVec.ofNat 64 288 from rfl, ofNat_add_small]
      exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  have access : AccessPlan c.σ.mem (prepare_input (cfgR c ra))
      [argvBd c (cfgR c ra), argvBe c (cfgR c ra), argvBr c (cfgR c ra)] prepare_body :=
    argv_prepare_access c.σ.mem (cfgR c ra) layout
      (window_of_nat (n := 0x80064c18) (by rw [tohost]; omega) (by omega) (by decide)).read
  have stage : CopyStageInput imageLive (argvMem c ra) (List.range' Gc.exeNameAddr 6) (cfgR c ra)
      (argvBd c (cfgR c ra)) (argvBe c (cfgR c ra)) (argvBr c (cfgR c ra)) Gc.exeNameAddr progExeName.length
      (imgM (argvMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm) c := by
    refine { toLeafInput := hR1 ▸ input.toLeafInput
             libraryGood := ⟨input.good, input.tick, lr.gprs, imageLive_present input.image, lr.htifIdle⟩
             regs, access, outside := ?_, source := bev, copyMemory := ?_ }
    · rw [bdv]
      apply imageOutside_of_above
      intro x hx
      have := logInW_mem prepIn hx
      simp only [allocWindows, InsideW, Layout.off_young_ptr, Layout.off_local_roots] at this
      simp only [Layout.sym_bss_end]
      rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      · omega
      · omega
      · omega
      · omega
      · exact h.elim
    · simp only [argvMem, bdv, F, progExeName_length]; exact copy
  -- the pair's allocation stage
  obtain ⟨strOut, slotOut, resImage⟩ := argv_afterCopy (R := cfgR c ra) nums h2
  have small := argv_small (R := cfgR c ra) (roots := bytesVal .ld (argvBr c (cfgR c ra)))
    (g := imgM (argvMem c ra)) (a := Gc.exeNameAddr) nums h2 wD wL
  have allocStage : AllocateStageInput imageLive (argvMem c ra) (List.range' Gc.exeNameAddr 6) (cfgR c ra)
      (argvBd c (cfgR c ra)) (argvBe c (cfgR c ra)) (argvBr c (cfgR c ra)) Gc.exeNameAddr progExeName.length
      (imgM (argvMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) c := by
    refine { stage with resultSlot := ?_, resultImage := resImage, small := ?_, stringOutside := ?_ }
    · rw [F]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [bdv]; exact small
    · rw [bdv]; exact strOut
  -- the pair's finishing stage
  have BY := argvBlockYoung_eq Y (by omega) (by omega)
  have TW := tupleWord_eq Y (by omega) (by omega)
  have RW := argvResultWord_eq Y (by omega) (by omega)
  have SH := smallHeader2 Y (by omega) (by omega)
  have logIn := getArgvLog_in (R := cfgR c ra) (roots := bytesVal .ld (argvBr c (cfgR c ra)))
    (g := imgM (argvMem c ra)) (a := Gc.exeNameAddr) (argv := word c Layout.sym_main_argv) (D := D) (Y := Y)
    (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have finish : FinishStageInput imageLive (argvMem c ra) (List.range' Gc.exeNameAddr 6) (cfgR c ra)
      (argvBd c (cfgR c ra)) (argvBe c (cfgR c ra)) (argvBr c (cfgR c ra)) Gc.exeNameAddr progExeName.length
      (imgM (argvMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64) (word c Layout.sym_main_argv) c := by
    refine { allocStage with layout := ?_, argvValue := rfl, argvAllocated := ?_, stringSlotOutside := ?_,
                             savedTail := ?_, stringOutsideTuple := ?_, headerOutsideTuple := ?_ }
    · rw [F, bdv, BY, TW, RW]; exact argv_finish_layout nums
    · rw [bdv]
      simp only [getArgvLog] at logIn
      exact outLRange_of_windows (logInW_prefix logIn) (by
        simp only [allocWindows, OutWRange, argvGlobal, Layout.sym_main_argv, Layout.off_young_ptr,
          Layout.off_local_roots, BitVec.toNat_ofNat, Nat.reducePow, and_true]
        omega)
    · rw [bdv]; exact slotOut
    · rw [bdv]; exact argv_savedTail nums h2
    · rw [F, bdv, BY, TW, RW, progExeName_length, nat _ (by omega)]; exact argv_stringOutsideTuple nums
    · rw [F, bdv, BY, TW, RW, SH, nat _ (by omega)]; exact argv_headerOutsideTuple nums
  -- the represented call
  have ng := setup.geometry.nursery
  have sg := setup.geometry.toStackGeometry
  have stack := input.data.stack
  have space := stack_space stack (by omega)
  have lw := e.logWindows (log := getArgvLog (cfgR c ra) (BitVec.ofNat 64 D) (bytesVal .ld (argvBr c (cfgR c ra)))
    (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64)
    (word c Layout.sym_main_argv) Gc.exeNameAddr progExeName.length (imgM (argvMem c ra)))
    sg ng (top := sp - 16) (by have := stack.1; omega) logIn
  have low : ∀ x, 0x8007d700 ≤ x → x < 0x8007d706 → (argvMem c ra)[x]? = c.σ.mem[x]? := fun x lo hx => by
    have xa := exe.domainApart
    rw [wD, nat _ (by omega)] at xa
    simp only [Layout.domainStateBytes, Gc.exeNameAddr] at xa
    simp only [argvMem, bdv]
    exact writeLog_out _ _ _ (outL_of_range (outLRange_of_windows (a := x) (n := 1) prepIn (by
      simp only [allocWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega))
      (Nat.le_refl _) (by omega))
  have young := e.young
  have limit := e.limit
  refine { (hR1 ▸ input : ImmediateInput L.runtimeOk P s pl cp sp high (cfgR c ra 1) [s.accu] c) with
           machine := finish, sourceBytes := ?_, argvRepr := input.data.argv, namePlaced, nameSeparate := ?_,
           pairPlaced, pairSeparate := ?_, payloadOutside := ?_, bindingsOutside := ?_ }
  · intro i x hx
    have hi : i < 5 := (List.getElem?_eq_some_iff.1 hx).1
    have b := exe.bytes ⟨i, by omega⟩
    rw [byte_total] at b
    simp only [imgM]
    rw [low _ (by simp only [Gc.exeNameAddr]; omega) (by simp only [Gc.exeNameAddr]; omega), b]
    match i, hx with
    | 0, hx => simp only [progExeName] at hx; cases hx; rfl
    | 1, hx => simp only [progExeName] at hx; cases hx; rfl
    | 2, hx => simp only [progExeName] at hx; cases hx; rfl
    | 3, hx => simp only [progExeName] at hx; cases hx; rfl
    | 4, hx => simp only [progExeName] at hx; cases hx; rfl
    | n + 5, _ => omega
  · rw [RW, nat _ (by omega)]
    exact ng.allocationOutside (count := 1) (by rw [young]; omega) (by rw [limit]; omega) (by omega) (by decide)
  · rw [BY, TW, nat _ (by omega)]
    intro l b old _ placed got
    rcases heap_alloc_get got with old' | ⟨rfl, rfl⟩
    · have apart := Gc.apart_of_inside (ng.heap l b old placed old') (y := Y - 40) (k := 24)
        (by rw [limit]; omega) (by rw [young]; omega)
      have w : (argvPair s).wosize = 2 := rfl
      rw [w]; omega
    · have hb : b = Y - 8 := by
        have := placed.symm.trans namePlaced
        rw [RW, nat _ (by omega)] at this
        exact Option.some.inj this
      have w : (argvPair s).wosize = 2 := rfl
      rw [w, hb]; left; omega
  · rw [bdv]
    exact lw.payload stack.1 space (by omega) (by decide) (by decide)
  · rw [bdv]; exact lw.bindings

/-- **`caml_sys_get_argv` at the C_CALL callee entry.** -/
theorem get_argv_entry {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {env : BitVec 64} {c : Config}
    (frame : PrimAllocFrame L) (exeAt : ExeNameAt L)
    (budget : ((afterName s).heap.alloc (argvPair s)).1.words ≤ L.budget.heapWords)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_sys_get_argv env c)
    (namePlaced : pl.φ (s.heap.alloc (.bytes progExeName)).2 =
      some (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length).toNat)
    (pairPlaced : pl.φ ((afterName s).heap.alloc (argvPair s)).2 =
      some (tupleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length
        - 8#64)).toNat) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_argv) (fun x => x = c)
      (CcallReturn ra L P { s with pc := s.pc + 2, accu := Val.ptr ((afterName s).heap.alloc (argvPair s)).2 0,
                                   heap := ((afterName s).heap.alloc (argvPair s)).1, world := s.world }
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16))
        (tupleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length - 8#64))
        env) := by
  have w1 : (Obj.bytes progExeName).wosize = 1 := rfl
  have w2 : (argvPair s).wosize = 2 := rfl
  have words : s.heap.words + 5 ≤ L.budget.heapWords := by
    simp only [afterName, Heap.words_alloc, w1, w2] at budget; omega
  have input := setup.input
  have exe := exeAt.placed c input.runtime
  obtain ⟨N, e⟩ := StringAllocEntry.of_setup setup words
  generalize hD : (word c Layout.sym_Caml_state).toNat = D at e
  generalize hY : (runtimeFields c).youngPtr = Y at e namePlaced pairPlaced ⊢
  generalize hL : (runtimeFields c).youngLimit = Lm at e
  have h := argv_input (ra := ra) setup e exe namePlaced pairPlaced stackFits
  have nums := AllocNumbers.of_entry e
  have lr := setup.libraryReady
  have hR1 := cfgR_one c ra
  have h2 : cfgR c ra 2 = BitVec.ofNat 64 N := by
    simp only [cfgR, if_neg (show (2 : Nat) ≠ 1 by decide)]; exact regsAt_of e.stack
  obtain ⟨wD, wY, wL⟩ := e.words
  have bdv := argvBd_val (ra := ra) e wD
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have ng := setup.geometry.nursery
  have sg := setup.geometry.toStackGeometry
  have stack := input.data.stack
  have space := stack_space stack (by omega)
  let log := getArgvLog (cfgR c ra) (BitVec.ofNat 64 D) (bytesVal .ld (argvBr c (cfgR c ra)))
    (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64)
    (word c Layout.sym_main_argv) Gc.exeNameAddr progExeName.length (imgM (argvMem c ra))
  have logIn : LogInW (allocWindows N D Y 40) log :=
    getArgvLog_in (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have lw := e.logWindows (log := log) sg ng (top := sp - 16) (by have := stack.1; omega) logIn
  have youngW : bytesT (writeLog c.σ.mem log) (D + Layout.off_young_ptr) 8 = BitVec.ofNat 64 (Y - 40) :=
    getArgv_young (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h2
  -- the runtime frame
  have runtime : ObservationRuntime L.runtimeOk c (fun x => ((writeLog c.σ.mem
      (getArgvLog (cfgR c ra) (bytesVal .ld (argvBd c (cfgR c ra))) (bytesVal .ld (argvBr c (cfgR c ra)))
        (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64)
        (word c Layout.sym_main_argv) Gc.exeNameAddr progExeName.length (imgM (argvMem c ra))))[x]?).getD 0) := by
    rw [bdv]
    refine frame.allocW P s c pl cp high log input.runtime ng (e.entries logIn) fun after mem => ?_
    have yw : word after ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) = BitVec.ofNat 64 (Y - 40) := by
      rw [hD]; change bytesT after.σ.mem _ 8 = _; rw [mem]; exact youngW
    rw [yw, toNat_ofNat_small (by omega), hY, hL]
    omega
  have S := get_argv_contract h runtime
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have RW := argvResultWord_eq Y (by omega) (by omega)
  have BY := argvBlockYoung_eq Y (by omega) (by omega)
  have TW := tupleWord_eq Y (by omega) (by omega)
  have expect : ∀ (after : Config), Vsa.Densify.MemEqv after.σ.mem (writeLog c.σ.mem
      (allocatedLog (cfgR c ra) (bytesVal .ld (argvBd c (cfgR c ra))) (bytesVal .ld (argvBr c (cfgR c ra)))
        (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64)
        Gc.exeNameAddr progExeName.length (imgM (argvMem c ra)) ++
      tupleLog (frameSp (cfgR c ra 2))
        (tupleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length - 8#64))
        (StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length) (word c Layout.sym_main_argv)
        (bytesVal .ld (argvBd c (cfgR c ra))) (bytesVal .ld (argvBr c (cfgR c ra))))) →
      ∀ x, byte after x = ((writeLog c.σ.mem log)[x]?).getD 0 := by
    intro after mem x
    rw [byte_total]
    have := mem x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    rw [this, bdv]; rfl
  refine ccall_observed_summary (name := "caml_sys_get_argv") (args := [s.accu]) (footprint := log)
    (expected := fun x => ((writeLog c.σ.mem log)[x]?).getD 0)
    (S.weaken (fun _ h => h) fun after post => ?_) setup.saved ?_ (e.below logIn) ?_ setup.native
  · have obs := expect after post.memory
    have pr := post.toLibraryPrimitivePost
    rw [hR1] at pr
    refine ⟨framed_of_library pr post.libraryGood.gpr obs ?_ ?_, obs⟩
    · intro r hr
      simp only [callSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact post.registers 25 (by decide) (by decide) (by decide)
      · change gprGet after.σ 8 = gprGet c.σ 8
        exact post.s0.trans (cfgR_gpr (by decide) (lr.gprs 8 (by decide) (by decide))).symm
      · change gprGet after.σ 18 = gprGet c.σ 18
        exact post.s2.trans (cfgR_gpr (by decide) (lr.gprs 18 (by decide) (by decide))).symm
      · change gprGet after.σ 2 = gprGet c.σ 2
        exact post.stack.trans (cfgR_gpr (by decide) (lr.gprs 2 (by decide) (by decide))).symm
    · exact post.registers 3 (by decide) (by decide) (by decide)
  · have st := stack.1
    have sb : Layout.stackBytes = 32768 := rfl
    rw [sb] at stackFits
    have stt := sg.statics
    rw [sb] at stt
    exact lw.savedOutside setup.saved.domainWord (by rw [sb]; omega) (by omega) (by have := sg.top; omega)
  · intro after obs
    have kept : GeometryWordsKept log s c cp :=
      ⟨lw.static (by decide), lw.static (by decide), lw.static (by decide),
        lw.domainField (by decide) (by decide), fun _ _ _ hc hp => lw.channel hc hp⟩
    have mem : ∀ x, OutLRange log x 8 → word after x = word c x := fun x out => by
      rw [word_of_expected obs, bytesT_writeLog_out _ out]; rfl
    have young : (runtimeFields after).youngPtr = (runtimeFields c).youngPtr - 8 * ((Obj.bytes progExeName).wosize + 1)
        - 8 * ((argvPair s).wosize + 1) := by
      have dom := mem _ (lw.static (a := Layout.sym_Caml_state) (by decide))
      simp only [runtimeFields, domainWord, dom, hD, w1, w2]
      rw [word_of_expected obs, youngW, wY, nat _ (by omega), nat _ (by omega)]
      omega
    have g := setup.geometry.reserve2 (o1 := .bytes progExeName) (o2 := argvPair s) (after := after)
      (by rw [w1, w2]; omega)
      (by rw [namePlaced, hY, RW, nat _ (by omega), w1, Nat.mul_one])
      (by
        have tp : pl.φ ((afterName s).heap.alloc (argvPair s)).2 = _ := pairPlaced
        simp only [afterName] at tp
        rw [tp, hY, BY, TW, nat _ (by omega), w1, w2, show Y - 8 * (1 + 1) - 8 * 2 = Y - 32 by omega])
      kept mem young
    exact g.state rfl rfl

/-- **`caml_sys_get_argv` at every `C_CALL` site**, given the executable
name's placement (`ExeNameAt`; F1: `f1_exeNameAt`). -/
theorem prim_caml_sys_get_argv_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (frame : PrimAllocFrame L) (exeName : ExeNameAt L) :
    PrimReturnsAt L P op ra k "caml_sys_get_argv" := by
  intro s c0 pl cp sp high table entry value env index v heap world _reach ready sem words
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  have model : primF1Impl "caml_sys_get_argv" [s.accu] s.heap s.world =
      .ok (.ptr ((afterName s).heap.alloc (argvPair s)).2 0) ((afterName s).heap.alloc (argvPair s)).1
        s.world := rfl
  rw [model] at sem
  cases sem
  have hentry : entry = Layout.sym_caml_sys_get_argv :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_sys_get_argv)
  subst hentry
  have places : ∀ young : BitVec 64, allocPlaces "caml_sys_get_argv" s young =
      [((s.heap.alloc (.bytes progExeName)).2, (StringCopy.resultWord young progExeName.length).toNat),
       (((afterName s).heap.alloc (argvPair s)).2,
        (tupleWord (StringCopy.resultWord young progExeName.length - 8#64)).toNat)] := fun _ => rfl
  have head := ready.allocPlaced _ (by rw [places]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine ⟨tupleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c0).youngPtr) progExeName.length - 8#64),
    ⟨by decide, model, fun c setup placedAt => ?_⟩⟩
  have name := placedAt _ (by rw [places]; exact List.mem_cons_self)
  have pair := placedAt _ (by rw [places]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have same : tupleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c0).youngPtr) progExeName.length - 8#64) =
      tupleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length - 8#64) :=
    BitVec.eq_of_toNat_eq (Option.some.inj (head.symm.trans pair))
  rw [same]
  exact get_argv_entry frame exeName words ready.stackFits setup name pair

end OCaml.Vm.Sim
