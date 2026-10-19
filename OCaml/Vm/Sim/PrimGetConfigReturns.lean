import OCaml.Vm.Sim.ConfigInput
import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Sim.LibraryEntry
import OCaml.Vm.Primitives.Named.NamedHash

/-!
# `caml_sys_get_config` at every C_CALL site

At the callee entry, the generated contract's input (`GetConfigInput`) is
assembled from the stage inputs of `ConfigInput.lean`; the post is a
library-style return whose memory is the exact effect of `getConfigLog`.
Its runtime frame is `PrimAllocFrame`, its geometry two chained reservations
(`LoopGeometry.reserve2`), its separation the four windows of the log
(`StringAllocEntry.logWindows`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ConfigTuple
open ArgvTuple (frameSp memoryView)
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of)
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Memcpy

/-- The registers at the callee entry, with the return address. -/
def cfgR (c : Config) (ra : BitVec 64) : Nat → BitVec 64 := fun k => if k = 1 then ra else regsAt c k

/-- The prepare block's loads at the callee entry. -/
def cfgBd (c : Config) (R : Nat → BitVec 64) : List (BitVec 8) := (prepareLoads c.σ.mem R).getD 0 []
def cfgBr (c : Config) (R : Nat → BitVec 64) : List (BitVec 8) := (prepareLoads c.σ.mem R).getD 1 []

theorem cfgBd_val {c : Config} {N D Y Lm k : Nat} {ra : BitVec 64} (e : StringAllocEntry c N D Y Lm k)
    (wD : word c Layout.sym_Caml_state = BitVec.ofNat 64 D) :
    bytesVal .ld (cfgBd c (cfgR c ra)) = BitVec.ofNat 64 D := by
  have h2 : cfgR c ra 2 = BitVec.ofNat 64 N := by
    simp only [cfgR, if_neg (show (2 : Nat) ≠ 1 by decide)]; exact regsAt_of e.stack
  have nh := e.nativeHigh; have nl := e.nativeLow
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have hs : Layout.sym_stack_top = 0x88000000 := rfl
  rw [he] at nl; rw [hs] at nh
  simp only [nativeHeadroom] at nl
  simp only [cfgBd, prepareLoads, List.getD_cons_zero, read8_value]
  rw [bytesT_writeLog_out _ (by
    simp only [savedLog, frameSp, h2, frameSp_ofNat (N := N) (by omega) (by omega), ← BitVec.ofNat_add,
      DoubleAllocation.domainGlobal, Layout.sym_Caml_state, OutLRange, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega)]
  exact wD

/-- The memory after the prepare block, at the callee entry. -/
def cfgMem (c : Config) (ra : BitVec 64) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog c.σ.mem (prepareLog (cfgR c ra) (bytesVal .ld (cfgBd c (cfgR c ra)))
    (bytesVal .ld (cfgBr c (cfgR c ra))))

theorem cfgR_one (c : Config) (ra : BitVec 64) : cfgR c ra 1 = ra := by simp [cfgR]

theorem cfgR_gpr {c : Config} {ra : BitVec 64} {k : Nat} (hk : k ≠ 1) (present : (gprGet c.σ k).isSome) :
    gprGet c.σ k = some (cfgR c ra k) := by
  simp only [cfgR, if_neg hk]
  exact OCaml.Vm.Primitives.Named.NamedValue.gpr_some present

/-- **`caml_sys_get_config`'s contract input at the C_CALL callee entry.** -/
theorem config_input {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env : BitVec 64} {c : Config} {N D Y Lm : Nat}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_sys_get_config env c)
    (e : StringAllocEntry c N D Y Lm 48)
    (namePlaced : pl.φ (s.heap.alloc (.bytes osType)).2 =
      some (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length).toNat)
    (triplePlaced : pl.φ ((afterOsType s).heap.alloc (configTriple s)).2 =
      some (tripleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64)).toNat)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    GetConfigInput L.runtimeOk P s pl cp sp high s.accu imageLive (cfgMem c ra) osTypeData (cfgR c ra)
      (cfgBd c (cfgR c ra)) (cfgBr c (cfgR c ra)) (imgM (cfgMem c ra)) (BitVec.ofNat 64 Y)
      (BitVec.ofNat 64 Lm) (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) c := by
  have nums := ConfigNumbers.of_entry e
  have lr := setup.libraryReady
  have input := setup.input
  have hR1 := cfgR_one c ra
  have h2 : cfgR c ra 2 = BitVec.ofNat 64 N := by
    simp only [cfgR, if_neg (show (2 : Nat) ≠ 1 by decide)]; exact regsAt_of e.stack
  obtain ⟨wD, wY, wL⟩ := e.words
  have bdv := cfgBd_val (ra := ra) e wD
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have prepIn := prepareLog_in (R := cfgR c ra) (roots := bytesVal .ld (cfgBr c (cfgR c ra))) (Y := Y) (D := D)
    (by omega) (by omega) (by omega) h2
  have F := frameSp_eq h2 (by omega) (by omega)
  have nums := ConfigNumbers.of_entry e
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  -- the copy stage
  have copy := copy_memory_at prepare_call.link
    (config_site (R := cfgR c ra) (roots := bytesVal .ld (cfgBr c (cfgR c ra))) nums h2 input.image lr.gp wD wY wL prepIn)
  have regs : GHolds c.σ (prepare_input (cfgR c ra)) := by
    simp only [prepare_input, GHolds]
    refine ⟨?_, cfgR_gpr (by decide) (lr.gprs 2 (by decide) (by decide)),
      cfgR_gpr (by decide) (lr.gprs 8 (by decide) (by decide)), cfgR_gpr (by decide) (lr.gprs 9 (by decide) (by decide)),
      cfgR_gpr (by decide) (lr.gprs 18 (by decide) (by decide)), trivial⟩
    rw [hR1]; exact input.raReg
  have layout : PrepareLayout (cfgR c ra) (bytesVal .ld ((prepareLoads c.σ.mem (cfgR c ra)).getD 0 [])) := by
    have bdv' : bytesVal .ld ((prepareLoads c.σ.mem (cfgR c ra)).getD 0 []) = BitVec.ofNat 64 D := bdv
    rw [bdv']
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rw [F]; exact frame_above_window (by rw [show Vsa.Sim.DlHeap.heapEnd = 0x86800000 from rfl]; omega) e.nativeHigh na (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rw [F]; exact frame_above_window (by rw [show Vsa.Sim.DlHeap.heapEnd = 0x86800000 from rfl]; omega) e.nativeHigh na (by omega) (by omega)
    · exact (window_of_nat (n := 0x80064d08) (by rw [tohost]; omega) (by omega) (by decide)).read
    · rw [show (288#64 : BitVec 64) = BitVec.ofNat 64 288 from rfl, ofNat_add_small]
      exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  have access : AccessPlan c.σ.mem (prepare_input (cfgR c ra)) [cfgBd c (cfgR c ra), cfgBr c (cfgR c ra)]
      prepare_body := prepare_access c.σ.mem (cfgR c ra) layout
  have stage : CopyStageInput imageLive (cfgMem c ra) osTypeData (cfgR c ra) (cfgBd c (cfgR c ra))
      (cfgBr c (cfgR c ra)) osType.length (imgM (cfgMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm) c := by
    refine { toLeafInput := hR1 ▸ input.toLeafInput
             libraryGood := ⟨input.good, input.tick, lr.gprs, imageLive_present input.image, lr.htifIdle⟩
             regs, access, outside := ?_, copyMemory := ?_ }
    · rw [bdv]
      apply imageOutside_of_above
      intro x hx
      have := logInW_mem prepIn hx
      simp only [configWindows, InsideW, Layout.off_young_ptr, Layout.off_local_roots] at this
      simp only [Layout.sym_bss_end]
      rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      · omega
      · omega
      · omega
      · omega
      · exact h.elim
    · simp only [cfgMem, bdv, F, osType_length]; exact copy
  -- the triple's allocation stage
  obtain ⟨strOut, slotOut, resImage⟩ := config_afterCopy (R := cfgR c ra) nums h2
  have small := config_small (R := cfgR c ra) (roots := bytesVal .ld (cfgBr c (cfgR c ra)))
    (g := imgM (cfgMem c ra)) nums h2 wD wL
  have allocStage : AllocateStageInput imageLive (cfgMem c ra) osTypeData (cfgR c ra) (cfgBd c (cfgR c ra))
      (cfgBr c (cfgR c ra)) osType.length (imgM (cfgMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) c := by
    refine { stage with resultSlot := ?_, resultImage := resImage, small := ?_, stringOutside := ?_ }
    · rw [F]; exact frame_above_window (by rw [show Vsa.Sim.DlHeap.heapEnd = 0x86800000 from rfl]; omega)
        e.nativeHigh na (by omega) (by omega)
    · rw [bdv]; exact small
    · rw [bdv]; exact strOut
  -- the triple's finishing stage
  have BY := blockYoung_eq Y (by omega) (by omega)
  have TW := tripleWord_eq Y (by omega) (by omega)
  have RW := resultWord4 Y (by omega) (by omega)
  have SH := smallHeader Y (by omega) (by omega)
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have finish : FinishStageInput imageLive (cfgMem c ra) osTypeData (cfgR c ra) (cfgBd c (cfgR c ra))
      (cfgBr c (cfgR c ra)) osType.length (imgM (cfgMem c ra)) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) c := by
    refine { allocStage with layout := ?_, stringSlotOutside := ?_, savedTail := ?_,
                             stringOutsideTriple := ?_, headerOutsideTriple := ?_ }
    · rw [F, bdv, BY, TW, osType_length, RW]; exact config_finish_layout nums
    · rw [bdv]; exact slotOut
    · rw [bdv]; exact config_savedTail nums h2
    · rw [F, bdv, BY, TW, osType_length, RW, nat _ (by omega)]; exact config_stringOutsideTriple nums
    · rw [F, bdv, BY, TW, osType_length, RW, SH, nat _ (by omega)]; exact config_headerOutsideTriple nums
  -- the represented call
  have ng := setup.geometry.nursery
  have sg := setup.geometry.toStackGeometry
  have stack := input.data.stack
  have space := stack_space stack (by omega)
  have logIn := getConfigLog_in (R := cfgR c ra) (roots := bytesVal .ld (cfgBr c (cfgR c ra)))
    (g := imgM (cfgMem c ra)) (D := D) (Y := Y) (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have lw := e.logWindows (log := getConfigLog (cfgR c ra) (BitVec.ofNat 64 D) (bytesVal .ld (cfgBr c (cfgR c ra)))
    (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) (imgM (cfgMem c ra)))
    (by decide) sg ng (top := sp - 16) (by have := stack.1; omega) logIn
  have low : ∀ x, x < 0x8007d138 → (cfgMem c ra)[x]? = c.σ.mem[x]? := fun x hx => by
    simp only [cfgMem, bdv]
    exact writeLog_out _ _ _ (outL_of_range (outLRange_of_windows (a := x) (n := 1) prepIn (by
      simp only [configWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega))
      (Nat.le_refl _) (by omega))
  have young := e.young
  have limit := e.limit
  refine { (hR1 ▸ input : ImmediateInput L.runtimeOk P s pl cp sp high (cfgR c ra 1) [s.accu] c) with
           machine := finish, sourceBytes := ?_, namePlaced, nameSeparate := ?_, triplePlaced,
           tripleSeparate := ?_, payloadOutside := ?_, bindingsOutside := ?_ }
  · intro i x hx
    have hi : i < 4 := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simpa only [osType_length] using this
    simp only [imgM]
    rw [low _ (by rw [show osTypeAddress.toNat = 0x80055c78 from rfl]; omega),
      osType_rodata input.image i (by omega)]
    rcases i with _ | _ | _ | _ | i
    · simp only [osType] at hx; cases hx; decide
    · simp only [osType] at hx; cases hx; decide
    · simp only [osType] at hx; cases hx; decide
    · simp only [osType] at hx; cases hx; decide
    · omega
  · rw [osType_length, RW, nat _ (by omega)]
    exact ng.allocationOutside (count := 1) (by rw [young]; omega) (by rw [limit]; omega) (by omega) (by decide)
  · rw [BY, TW, nat _ (by omega)]
    intro l b old _ placed got
    rcases heap_alloc_get got with old' | ⟨rfl, rfl⟩
    · have apart := Gc.apart_of_inside (ng.heap l b old placed old') (y := Y - 48) (k := 32)
        (by rw [limit]; omega) (by rw [young]; omega)
      have w : (configTriple s).wosize = 3 := rfl
      rw [w]; omega
    · have hb : b = Y - 8 := by
        have := placed.symm.trans namePlaced
        rw [osType_length, RW, nat _ (by omega)] at this
        exact Option.some.inj this
      have w : (configTriple s).wosize = 3 := rfl
      rw [w, hb]; left; omega
  · rw [bdv]
    exact lw.payload stack.1 space (by omega) (by decide) (by decide)
  · rw [bdv]; exact lw.bindings

/-- Bytes as predicted give words as predicted. -/
theorem word_of_expected {after : Config} {m : Std.ExtHashMap Nat (BitVec 8)}
    (same : ∀ x, byte after x = (m[x]?).getD 0) (a : Nat) : word after a = bytesT m a 8 :=
  word_of_bytes (c := memoryView after m) (fun x => (same x).trans (byte_total (memoryView after m) x).symm) a

/-- **`caml_sys_get_config` at the C_CALL callee entry.** -/
theorem get_config_entry {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {env : BitVec 64} {c : Config}
    (frame : PrimAllocFrame L)
    (budget : ((afterOsType s).heap.alloc (configTriple s)).1.words ≤ L.budget.heapWords)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_sys_get_config env c)
    (namePlaced : pl.φ (s.heap.alloc (.bytes osType)).2 =
      some (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) osType.length).toNat)
    (triplePlaced : pl.φ ((afterOsType s).heap.alloc (configTriple s)).2 =
      some (tripleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) osType.length
        - 8#64)).toNat) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_config) (fun x => x = c)
      (CcallReturn ra L P { s with pc := s.pc + 2, accu := Val.ptr ((afterOsType s).heap.alloc (configTriple s)).2 0, heap := ((afterOsType s).heap.alloc (configTriple s)).1, world := s.world }
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16))
        (tripleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) osType.length - 8#64))
        env) := by
  have w1 : (Obj.bytes osType).wosize = 1 := rfl
  have w2 : (configTriple s).wosize = 3 := rfl
  have words : s.heap.words + 6 ≤ L.budget.heapWords := by
    simp only [afterOsType, Heap.words_alloc, w1, w2] at budget; omega
  obtain ⟨N, e⟩ := StringAllocEntry.of_setup setup words
  generalize hD : (word c Layout.sym_Caml_state).toNat = D at e
  generalize hY : (runtimeFields c).youngPtr = Y at e namePlaced triplePlaced ⊢
  generalize hL : (runtimeFields c).youngLimit = Lm at e
  have h := config_input (ra := ra) setup e namePlaced triplePlaced stackFits
  have nums := ConfigNumbers.of_entry e
  have lr := setup.libraryReady
  have input := setup.input
  have hR1 := cfgR_one c ra
  have h2 : cfgR c ra 2 = BitVec.ofNat 64 N := by
    simp only [cfgR, if_neg (show (2 : Nat) ≠ 1 by decide)]; exact regsAt_of e.stack
  obtain ⟨wD, wY, wL⟩ := e.words
  have bdv := cfgBd_val (ra := ra) e wD
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have ng := setup.geometry.nursery
  have sg := setup.geometry.toStackGeometry
  have stack := input.data.stack
  have space := stack_space stack (by omega)
  let log := getConfigLog (cfgR c ra) (BitVec.ofNat 64 D) (bytesVal .ld (cfgBr c (cfgR c ra)))
    (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) (imgM (cfgMem c ra))
  have logIn : LogInW (configWindows N D Y) log :=
    getConfigLog_in (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have lw := e.logWindows (log := log) (by decide) sg ng (top := sp - 16) (by have := stack.1; omega) logIn
  have youngW : bytesT (writeLog c.σ.mem log) (D + Layout.off_young_ptr) 8 = BitVec.ofNat 64 (Y - 48) :=
    getConfig_young (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h2
  -- the runtime frame
  have runtime : ObservationRuntime L.runtimeOk c (fun x => ((writeLog c.σ.mem
      (getConfigLog (cfgR c ra) (bytesVal .ld (cfgBd c (cfgR c ra))) (bytesVal .ld (cfgBr c (cfgR c ra)))
        (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64)
        (imgM (cfgMem c ra))))[x]?).getD 0) := by
    rw [bdv]
    refine frame.allocW P s c pl cp high log input.runtime ng (e.entries (by decide) logIn) fun after mem => ?_
    have yw : word after ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) = BitVec.ofNat 64 (Y - 48) := by
      rw [hD]; change bytesT after.σ.mem _ 8 = _; rw [mem]; exact youngW
    rw [yw, toNat_ofNat_small (by omega), hY, hL]
    omega
  have S := get_config_contract h runtime
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have RW := resultWord4 Y (by omega) (by omega)
  have BY := blockYoung_eq Y (by omega) (by omega)
  have TW := tripleWord_eq Y (by omega) (by omega)
  have expect : ∀ (after : Config), Vsa.Densify.MemEqv after.σ.mem (writeLog c.σ.mem
      (allocatedLog (cfgR c ra) (bytesVal .ld (cfgBd c (cfgR c ra))) (bytesVal .ld (cfgBr c (cfgR c ra)))
        (BitVec.ofNat 64 Y) (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) osType.length
        (imgM (cfgMem c ra)) ++
      tripleLog (frameSp (cfgR c ra 2)) (tripleWord (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64))
        (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length) (bytesVal .ld (cfgBd c (cfgR c ra)))
        (bytesVal .ld (cfgBr c (cfgR c ra))))) →
      ∀ x, byte after x = ((writeLog c.σ.mem log)[x]?).getD 0 := by
    intro after mem x
    rw [byte_total]
    have := mem x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    rw [this, bdv]; rfl
  refine ccall_observed_summary (name := "caml_sys_get_config") (args := [s.accu]) (footprint := log)
    (expected := fun x => ((writeLog c.σ.mem log)[x]?).getD 0)
    (S.weaken (fun _ h => h) fun after post => ?_) setup.saved ?_ (e.below (by decide) logIn) ?_ setup.native
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
    have young : (runtimeFields after).youngPtr = (runtimeFields c).youngPtr - 8 * ((Obj.bytes osType).wosize + 1)
        - 8 * ((configTriple s).wosize + 1) := by
      have dom := mem _ (lw.static (a := Layout.sym_Caml_state) (by decide))
      simp only [runtimeFields, domainWord, dom, hD, w1, w2]
      rw [word_of_expected obs, youngW, wY, nat _ (by omega), nat _ (by omega)]
      omega
    have g := setup.geometry.reserve2 (o1 := .bytes osType) (o2 := configTriple s) (after := after)
      (by rw [w1, w2]; omega)
      (by rw [namePlaced, hY, osType_length, RW, nat _ (by omega), w1, Nat.mul_one])
      (by
        have tp : pl.φ ((afterOsType s).heap.alloc (configTriple s)).2 = _ := triplePlaced
        simp only [afterOsType] at tp
        rw [tp, hY, BY, TW, nat _ (by omega), w1, w2, show Y - 8 * (1 + 1) - 8 * 3 = Y - 40 by omega])
      kept mem young
    exact g.state rfl rfl

/-- **`caml_sys_get_config` at every `C_CALL` site.** -/
theorem prim_caml_sys_get_config_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (frame : PrimAllocFrame L) :
    PrimReturnsAt L P op ra k "caml_sys_get_config" := by
  intro s c0 pl cp sp high table entry value env index v heap world _reach ready sem words
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  have model : primF1Impl "caml_sys_get_config" [s.accu] s.heap s.world =
      .ok (.ptr ((afterOsType s).heap.alloc (configTriple s)).2 0) ((afterOsType s).heap.alloc (configTriple s)).1
        s.world := rfl
  rw [model] at sem
  cases sem
  have hentry : entry = Layout.sym_caml_sys_get_config :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_sys_get_config)
  subst hentry
  have places : ∀ young : BitVec 64, allocPlaces "caml_sys_get_config" s young =
      [((s.heap.alloc (.bytes osType)).2, (StringCopy.resultWord young osType.length).toNat),
       (((afterOsType s).heap.alloc (configTriple s)).2,
        (tripleWord (StringCopy.resultWord young osType.length - 8#64)).toNat)] := fun _ => rfl
  have head := ready.allocPlaced _ (by rw [places]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine ⟨tripleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c0).youngPtr) osType.length - 8#64),
    ⟨by decide, model, fun c setup placedAt => ?_⟩⟩
  have name := placedAt _ (by rw [places]; exact List.mem_cons_self)
  have triple := placedAt _ (by rw [places]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have same : tripleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c0).youngPtr) osType.length - 8#64) =
      tripleWord (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) osType.length - 8#64) :=
    BitVec.eq_of_toNat_eq (Option.some.inj (head.symm.trans triple))
  rw [same]
  exact get_config_entry frame words ready.stackFits setup name triple

end OCaml.Vm.Sim
