import OCaml.Vm.Sim.CopyStringInput
import OCaml.Vm.Sim.ConfigInput
import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Sim.LibraryEntry
import OCaml.Vm.Primitives.ExecutableNameContract
import OCaml.Vm.Primitives.ByteCopyLog

/-!
# `caml_sys_executable_name` at every C_CALL site

The primitive tail-calls `caml_copy_string` on `caml_exe_name`, so the copy's
inputs hold at the callee entry itself: `copy_memory_at` at the `CopySite`
with the native stack pointer `N` and the 5-byte source at `Gc.exeNameAddr`.
The source is the named premise `ExeNameAt` (F1: `f1_exeNameAt`, from
`F1Pins`). The contract's memory `copyMemory` is the effect of the finite
log `completeLog` (`copyMemory_eq`); the log lies in the four windows
`allocWindows N D Y 16`, which give its runtime frame (`PrimAllocFrame`), its
separation (`StringAllocEntry.logWindows`) and, with one reservation
(`LoopGeometry.reserve1`), the geometry after the call.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Memcpy

/-- **The executable name at a runtime config**: `caml_exe_name` points at
the six bytes `"/prog\0"` at `Gc.exeNameAddr`, apart from the domain record. -/
structure ExeNamePlaced (c : Config) : Prop where
  pointer : word c Layout.sym_caml_exe_name = BitVec.ofNat 64 Gc.exeNameAddr
  bytes : ∀ i : Fin 6, byte c (Gc.exeNameAddr + i.val) = Gc.exeNameBytes.getD i.val 0
  domainApart : Gc.exeNameAddr + 6 ≤ (word c Layout.sym_Caml_state).toNat ∨
    (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ Gc.exeNameAddr

/-- **Every runtime config places the executable name** (named obligation;
F1: `f1_exeNameAt`). -/
structure ExeNameAt (L : OCaml.Layout) : Prop where
  placed : ∀ c, L.runtimeOk c → ExeNamePlaced c

theorem f1_exeNameAt : ExeNameAt Gc.f1Layout := by
  refine ⟨fun c ok => ⟨ok.freeListShape.exeNameWord, ok.freeListShape.exeName, Or.inr ?_⟩⟩
  have dom : (word c Layout.sym_Caml_state).toNat = Gc.f1Domain := Gc.f1_domain ok
  rw [dom]; decide

theorem span5 : StringAllocation.stringSpan (BitVec.ofNat 64 5) = 8#64 := by decide

/-- The contract's memory is the effect of the finite copy log. -/
theorem copyMemory_eq (before : Config) (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young : BitVec 64) :
    StringCopy.copyMemory before ra sp a len g domain young =
      fun x => ((writeLog before.σ.mem (StringCopy.completeLog ra sp a len g domain young))[x]?).getD 0 := by
  funext x
  rw [StringCopy.completeLog, writeLog_append, byteCopyLog_observe]
  rfl

/-- **Every store of `caml_copy_string` called at the native stack pointer
lies in the four windows**, its nursery block 16 bytes. -/
theorem exeLog_in {N D Y : Nat} {ra : BitVec 64} {a : Nat} {g : Nat → BitVec 8}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 16 ≤ Y) (hY' : Y < 2 ^ 32) :
    LogInW (allocWindows N D Y 16) (StringCopy.completeLog ra (BitVec.ofNat 64 N) a 5 g
      (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)) := by
  simp only [StringCopy.completeLog, StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog,
    StringCopy.entryRegisters, StringCopy.sizeLog, StringCopy.lengthRegisters,
    StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
    StringAllocation.initializationLog, StringAllocation.reservedRegisters, StringAllocation.nurseryHeader,
    StringCopy.resultWord, DoubleAllocation.youngSlot, span5, byteCopyLog,
    allocWindows, LogInW, InsideW, List.cons_append, List.nil_append,
    Layout.off_local_roots, Layout.off_young_ptr,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

/-- The copy's footprint lies in the same windows. -/
theorem exeFootprint_in {N D Y : Nat} {ra : BitVec 64} {a : Nat}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (hY : 16 ≤ Y) (hY' : Y < 2 ^ 32) :
    LogInW (allocWindows N D Y 16) (StringCopy.copyFootprint ra (BitVec.ofNat 64 N) a 5
      (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)) := by
  simp only [StringCopy.copyFootprint, StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog,
    StringCopy.entryRegisters, StringCopy.sizeLog, StringCopy.lengthRegisters,
    StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
    StringAllocation.initializationLog, StringAllocation.reservedRegisters, StringAllocation.nurseryHeader,
    StringCopy.resultWord, DoubleAllocation.youngSlot, span5,
    allocWindows, LogInW, InsideW, List.cons_append, List.nil_append,
    Layout.off_local_roots, Layout.off_young_ptr,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

/-- The string's reservation is the last store to the young pointer. -/
theorem completeLog_split (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8) (domain young : BitVec 64) :
    StringCopy.completeLog ra sp a len g domain young =
      (StringCopy.prefixLog ra sp a len ++ savedRaLog (sp - 32#64) StringCopy.size_call.link) ++
      ((DoubleAllocation.youngSlot domain).toNat, 8,
        young - 8#64 - StringAllocation.stringSpan (BitVec.ofNat 64 len)) ::
      (StringAllocation.initializationLog
          (StringAllocation.reservedRegisters StringCopy.size_call.link (sp - 32#64) (BitVec.ofNat 64 len)
            (StringAllocation.nurseryHeader young (BitVec.ofNat 64 len)))
          (StringAllocation.nurseryHeader young (BitVec.ofNat 64 len)) ++
        byteCopyLog (StringCopy.resultWord young len).toNat len (fun i => g (a + i))) := by
  simp only [StringCopy.completeLog, StringCopy.allocationLog, StringAllocation.constructorLog,
    StringAllocation.reservationLog, List.append_assoc, List.cons_append, List.nil_append]

/-- **The young pointer after `caml_sys_executable_name`**: `Y - 16`. -/
theorem exe_young {m : Std.ExtHashMap Nat (BitVec 8)} {N D Y : Nat} {ra : BitVec 64} {a : Nat}
    {g : Nat → BitVec 8} (hD : D + 1000 < 2 ^ 32) (hY : 16 ≤ Y) (hY' : Y < 2 ^ 32)
    (apart : D + 928 ≤ Y - 16 ∨ Y ≤ D) :
    bytesT (writeLog m (StringCopy.completeLog ra (BitVec.ofNat 64 N) a 5 g (BitVec.ofNat 64 D)
      (BitVec.ofNat 64 Y))) (D + Layout.off_young_ptr) 8 = BitVec.ofNat 64 (Y - 16) := by
  have slot : (DoubleAllocation.youngSlot (BitVec.ofNat 64 D)).toNat = D + Layout.off_young_ptr := by
    simp only [DoubleAllocation.youngSlot, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Layout.off_young_ptr]
    omega
  rw [completeLog_split, ← slot, word_last_store]
  · simp only [span5]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  · simp only [StringAllocation.initializationLog, StringAllocation.reservedRegisters,
      StringAllocation.nurseryHeader, StringCopy.resultWord, span5, byteCopyLog, slot,
      List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, OutLRange, Layout.off_young_ptr,
      BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega

/-- `caml_copy_string`'s call site at the callee entry of `caml_sys_executable_name`. -/
theorem exe_site {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain : Nat} {env : BitVec 64} {c : Config} {N D Y Lm : Nat}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_sys_executable_name env c)
    (e : StringAllocEntry c N D Y Lm 16) (exe : ExeNamePlaced c) :
    CopySite c N D Y Lm Gc.exeNameAddr 5 8 := by
  have nl := e.nativeLow; have nh := e.nativeHigh; have dl := e.domainLow; have dh := e.domainHigh
  have yh := e.youngHigh; have ll := e.limitLow; have rm := e.room; have ap := e.domainApart
  have nlow := setup.geometry.nursery.nurseryLow
  rw [e.limit] at nlow
  have da := exe.domainApart
  rw [e.domain] at da
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  simp only [he, nativeHeadroom, Layout.sym_stack_top, Layout.sym_bss_end, Layout.domainStateBytes,
    Gc.minorRegion, Gc.exeNameAddr] at nl nh dl dh yh ll ap nlow da
  obtain ⟨wD, wY, wL⟩ := e.words
  have byte_at : ∀ i : Fin 6, imgM c.σ.mem (Gc.exeNameAddr + i.val) = Gc.exeNameBytes.getD i.val 0 := fun i => by
    rw [← exe.bytes i, byte_total]; rfl
  refine { image := setup.input.image, gp := setup.libraryReady.gp, nativeLow := by omega, nativeHigh := nh,
           nativeAligned := e.nativeAligned, domainLow := dl, domainHigh := dh, domainAligned := e.domainAligned,
           youngHigh := yh, youngAligned := e.youngAligned, limitLow := ll, room := by omega, apart := ap,
           span := span5, spanFits := by decide, small := by decide, wD, wY, wL,
           srcLow := by decide, srcHtif := Or.inr (by decide), srcNursery := by simp only [Gc.exeNameAddr]; omega,
           srcDomain := by simp only [Gc.exeNameAddr]; omega, bytesNz := ?_, bytesNul := ?_ }
  · intro i hi
    have nz : ∀ i, i < 5 → Gc.exeNameBytes.getD i 0 ≠ 0 := by decide
    rw [byte_at ⟨i, by omega⟩]; exact nz i hi
  · exact (byte_at ⟨5, by decide⟩).trans rfl


/-- **`caml_sys_executable_name` at the C_CALL callee entry.** -/
theorem executable_name_entry {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {env : BitVec 64} {c : Config}
    (frame : PrimAllocFrame L) (exeAt : ExeNameAt L)
    (budget : (s.heap.alloc (.bytes progExeName)).1.words ≤ L.budget.heapWords)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain Layout.sym_caml_sys_executable_name env c)
    (placed : pl.φ (s.heap.alloc (.bytes progExeName)).2 =
      some (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length).toNat) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_executable_name) (fun x => x = c)
      (CcallReturn ra L P
        { s with pc := s.pc + 2, accu := Val.ptr (s.heap.alloc (.bytes progExeName)).2 0,
                 heap := (s.heap.alloc (.bytes progExeName)).1, world := s.world }
        pl cp sp high (BitVec.ofNat 64 domain) (BitVec.ofNat 64 (sp - 16))
        (StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length) env) := by
  have w1 : (Obj.bytes progExeName).wosize = 1 := rfl
  have words : s.heap.words + 2 ≤ L.budget.heapWords := by
    simp only [Heap.words_alloc, w1] at budget; omega
  have input := setup.input
  have exe := exeAt.placed c input.runtime
  obtain ⟨N, e⟩ := StringAllocEntry.of_setup setup words
  generalize hD : (word c Layout.sym_Caml_state).toNat = D at e
  generalize hY : (runtimeFields c).youngPtr = Y at e placed ⊢
  generalize hL : (runtimeFields c).youngLimit = Lm at e
  have site := exe_site setup e exe
  have lr := setup.libraryReady
  obtain ⟨wD, wY, wL⟩ := e.words
  have nl := e.nativeLow; have nh := e.nativeHigh; have dl := e.domainLow; have dh := e.domainHigh
  have yh := e.youngHigh; have ll := e.limitLow; have rm := e.room; have ap := e.domainApart
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  simp only [he, nativeHeadroom, Layout.sym_stack_top, Layout.sym_bss_end,
    Layout.domainStateBytes] at nl nh dl dh yh ll ap
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have RW : StringCopy.resultWord (BitVec.ofNat 64 Y) progExeName.length = BitVec.ofNat 64 (Y - 8) :=
    resultWord_eq (len := 5) span5 (by omega) (by omega)
  have ng := setup.geometry.nursery
  have sg := setup.geometry.toStackGeometry
  have stack := input.data.stack
  have space := stack_space stack (by omega)
  let log := StringCopy.completeLog ra (BitVec.ofNat 64 N) Gc.exeNameAddr 5 (imgM c.σ.mem)
    (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)
  have logIn : LogInW (allocWindows N D Y 16) log := exeLog_in (by omega) (by omega) (by omega) (by omega) (by omega)
  have footIn : LogInW (allocWindows N D Y 16)
      (StringCopy.copyFootprint ra (BitVec.ofNat 64 N) Gc.exeNameAddr 5 (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)) :=
    exeFootprint_in (by omega) (by omega) (by omega) (by omega) (by omega)
  have lw := e.logWindows (log := log) sg ng (top := sp - 16) (by have := stack.1; omega) logIn
  have lwF := e.logWindows sg ng (top := sp - 16) (by have := stack.1; omega) footIn
  have youngW : bytesT (writeLog c.σ.mem log) (D + Layout.off_young_ptr) 8 = BitVec.ofNat 64 (Y - 16) :=
    exe_young (by omega) (by omega) (by omega) (by omega)
  -- the contract's input
  have good : VsaOk imageLive c := ⟨input.good, input.tick, lr.gprs, imageLive_present input.image, lr.htifIdle⟩
  have h : ExecutableNameInput L.runtimeOk P s pl cp sp high ra (BitVec.ofNat 64 N) s.accu imageLive c.σ.mem
      (List.range' Gc.exeNameAddr 6) Gc.exeNameAddr (imgM c.σ.mem) (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)
      (BitVec.ofNat 64 Lm) c := by
    have copy := (copy_memory_at ra site).input input.toLeafInput good e.stack
    refine { input with
             copy, source := exe.pointer, sourceBytes := ?_, placed := ?_, separate := ?_,
             payloadOutside := lwF.payload stack.1 space (by omega) (by decide) (by decide),
             bindingsOutside := lwF.bindings }
    · intro i x hx
      have hi : i < 5 := (List.getElem?_eq_some_iff.1 hx).1
      have b := exe.bytes ⟨i, by omega⟩
      rw [byte_total] at b
      change (c.σ.mem[Gc.exeNameAddr + i]?).getD 0 = _
      rw [b]
      match i, hx with
      | 0, hx => simp only [progExeName] at hx; cases hx; rfl
      | 1, hx => simp only [progExeName] at hx; cases hx; rfl
      | 2, hx => simp only [progExeName] at hx; cases hx; rfl
      | 3, hx => simp only [progExeName] at hx; cases hx; rfl
      | 4, hx => simp only [progExeName] at hx; cases hx; rfl
      | n + 5, _ => omega
    · rw [placed, RW]
    · rw [RW, nat _ (by omega)]
      exact ng.allocationOutside (count := 1) (by rw [e.young]; omega) (by rw [e.limit]; omega) (by omega)
        (by decide)
  -- the runtime frame
  have runtime : ObservationRuntime L.runtimeOk c (StringCopy.copyMemory c ra (BitVec.ofNat 64 N) Gc.exeNameAddr
      progExeName.length (imgM c.σ.mem) (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)) := by
    rw [copyMemory_eq]
    refine frame.allocW P s c pl cp high log input.runtime ng (e.entries logIn) fun after mem => ?_
    have yw : word after ((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr) = BitVec.ofNat 64 (Y - 16) := by
      rw [hD]; change bytesT after.σ.mem _ 8 = _; rw [mem]; exact youngW
    have ya := e.youngAligned
    rw [yw, toNat_ofNat_small (by omega), hY, hL]
    omega
  have S := executable_name_contract h runtime
  refine ccall_observed_summary (name := "caml_sys_executable_name") (args := [s.accu]) (footprint := log)
    (expected := fun x => ((writeLog c.σ.mem log)[x]?).getD 0)
    (S.weaken (fun _ h => h) fun after post => ?_) setup.saved ?_ (e.below logIn) ?_ setup.native
  · have obs : ∀ x, byte after x = ((writeLog c.σ.mem log)[x]?).getD 0 := fun x => by
      rw [post.memory_complete x, copyMemory_eq]; rfl
    refine ⟨framed_of_library post.toLibraryPrimitivePost post.libraryGood.gpr obs ?_ ?_, obs⟩
    · intro r hr
      simp only [callSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact post.registers 25 (by decide) (by decide) (by decide)
      · exact post.registers 8 (by decide) (by decide) (by decide)
      · exact post.registers 18 (by decide) (by decide) (by decide)
      · exact post.stack.trans e.stack.symm
    · exact post.registers 3 (by decide) (by decide) (by decide)
  · have sb : Layout.stackBytes = 32768 := rfl
    rw [sb] at stackFits
    have stt := sg.statics
    rw [sb] at stt
    exact lw.savedOutside setup.saved.domainWord (by rw [sb]; have := stack.1; omega) (by have := stack.1; omega)
      (by have := sg.top; omega)
  · intro after obs
    have kept : GeometryWordsKept log s c cp :=
      ⟨lw.static (by decide), lw.static (by decide), lw.static (by decide),
        lw.domainField (by decide) (by decide), fun _ _ _ hc hp => lw.channel hc hp⟩
    have mem : ∀ x, OutLRange log x 8 → word after x = word c x := fun x out => by
      rw [word_of_expected obs, bytesT_writeLog_out _ out]; rfl
    have young : (runtimeFields after).youngPtr = (runtimeFields c).youngPtr - 8 * ((Obj.bytes progExeName).wosize + 1) := by
      have dom := mem _ (lw.static (a := Layout.sym_Caml_state) (by decide))
      simp only [runtimeFields, domainWord, dom, hD, w1]
      rw [word_of_expected obs, youngW, wY, nat _ (by omega), nat _ (by omega)]
    have g := setup.geometry.reserve1 (o := .bytes progExeName) (after := after) (by rw [w1]; omega)
      (by rw [placed, hY, RW, nat _ (by omega), w1]) kept mem young
    exact g.state rfl rfl

/-- **`caml_sys_executable_name` at every `C_CALL` site.** -/
theorem prim_caml_sys_executable_name_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (frame : PrimAllocFrame L) (exeName : ExeNameAt L) :
    PrimReturnsAt L P op ra k "caml_sys_executable_name" := by
  intro s c0 pl cp sp high table entry value env index v heap world _reach ready sem words
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  have model : primF1Impl "caml_sys_executable_name" [s.accu] s.heap s.world =
      .ok (.ptr (s.heap.alloc (.bytes progExeName)).2 0) (s.heap.alloc (.bytes progExeName)).1 s.world := rfl
  rw [model] at sem
  cases sem
  have hentry : entry = Layout.sym_caml_sys_executable_name :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_sys_executable_name)
  subst hentry
  have places : ∀ young : BitVec 64, allocPlaces "caml_sys_executable_name" s young =
      [((s.heap.alloc (.bytes progExeName)).2, (StringCopy.resultWord young progExeName.length).toNat)] :=
    fun _ => rfl
  have head := ready.allocPlaced _ (by rw [places]; exact List.mem_singleton_self _)
  refine ⟨StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c0).youngPtr) progExeName.length,
    ⟨by decide, model, fun c setup placedAt => ?_⟩⟩
  have name := placedAt _ (by rw [places]; exact List.mem_singleton_self _)
  have same : StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c0).youngPtr) progExeName.length =
      StringCopy.resultWord (BitVec.ofNat 64 (runtimeFields c).youngPtr) progExeName.length :=
    BitVec.eq_of_toNat_eq (Option.some.inj (head.symm.trans name))
  rw [same]
  exact executable_name_entry frame exeName words ready.stackFits setup name

end OCaml.Vm.Sim
