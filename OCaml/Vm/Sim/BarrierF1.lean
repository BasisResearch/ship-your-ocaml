import OCaml.Vm.Gc.BarrierRun
import OCaml.Vm.Gc.BarrierGrow
import OCaml.Vm.Sim.ModifyCall
import OCaml.Vm.Sim.BarrierRows
import OCaml.Vm.Sim.CamlModifyImage
import OCaml.Vm.Sim.HeapRows
import OCaml.Vm.Sim.F1RaiseRuntime

/-!
# `caml_modify` from the represented state (the barrier rows' callee)

a6-gc's machine summaries (`Gc.Barrier.barrier_fast`, `barrier_grow`) run
`caml_modify` from its entry facts (`Entry`, `Remembered`). This file builds
those facts from a represented call (`ModifyInput`) and turns the fast path's
outcome (`FastDone`: the young-slot store, the major-slot store, or the
major-slot store plus a remembered-set insertion) back into the represented
return (`ModifyReturn`). The runtime facts the collector owns (an idle
collector, the remembered set's words, an insertion keeping the runtime) are
the per-layout named premise `BarrierRuntime`, discharged for F1 by a6-gc.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- **What the collector keeps for the write barrier** (named premise, per
layout; for F1 a6-gc's `f1_barrierRuntime`). -/
structure BarrierRuntime (L : OCaml.Layout) : Prop where
  /-- the collector is idle at every loop state (`Phase_idle`) -/
  idle : ∀ c, L.runtimeOk c → bytesT c.σ.mem Layout.sym_caml_gc_phase 4 = 3#32
  /-- the remembered set: its words and windows (`Table`); the struct, and the
  entry slot when there is room, are live malloc blocks apart from the payload -/
  table : ∀ c, L.runtimeOk c → ∃ tbl ptr limit,
    Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem ∧
    /- the blocks lie in the allocator arena -/
    (tbl.toNat + 40 ≤ Vsa.Sim.DlHeap.heapEnd ∧
      (ptr.toNat < limit.toNat → ptr.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd)) ∧
    ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (high : Nat), OCaml.LoopGeometry L P s c pl cp high →
      (word c Layout.sym_caml_start_code).toNat = pl.codeBase →
      (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high →
      Gc.WindowSeparated ⟨tbl.toNat, tbl.toNat + 40⟩ P s c pl cp high ∧
      (ptr.toNat < limit.toNat → Gc.WindowSeparated ⟨ptr.toNat, ptr.toNat + 8⟩ P s c pl cp high)
  /-- an insertion with room keeps the runtime -/
  insert : ∀ c tbl ptr limit (slot : BitVec 64), L.runtimeOk c →
    Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem → ptr.toNat < limit.toNat →
    AllocationRuntime L.runtimeOk c (Gc.Barrier.insertLog tbl ptr slot)

/-- The `Caml_state` word at `off` as a native address. -/
theorem domain_addr {P s c pl cp high} (g : ArmGeometry P s c pl cp high) {off : Nat}
    (fits : off + 8 ≤ Layout.domainStateBytes) :
    (word c Layout.sym_Caml_state + BitVec.ofNat 64 off).toNat = (word c Layout.sym_Caml_state).toNat + off :=
  domain_field_nat g fits

/-- The native frame's saved `ra` slot, `sp - 8`. -/
theorem frame_slot_nat {nsp : Nat} (low : 32 ≤ nsp) (small : nsp < 2 ^ 64) :
    ((BitVec.ofNat 64 nsp + -32#64) + BitVec.ofNat 64 24).toNat = nsp - 8 := by
  rw [BitVec.add_assoc, show -32#64 + BitVec.ofNat 64 24 = -8#64 from by decide]
  have e : BitVec.ofNat 64 nsp + -8#64 = BitVec.ofNat 64 (nsp - 8) := by
    rw [show (-8#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl, BitVec.ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_ofNat]
  omega

/-- The slot of a placed block's field as a native address. -/
theorem barrier_slot_nat {a i : Nat} (fits : a + 8 * i < 2 ^ 64) :
    (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat = a + 8 * i := by
  rw [BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- The major-slot stores' addresses: the frame slot and the field. -/
theorem majorLog_addrs {nsp a i : Nat} {ra v : BitVec 64} (low : 32 ≤ nsp) (small : nsp < 2 ^ 64)
    (fits : a + 8 * i < 2 ^ 64) :
    ∀ e ∈ Gc.Barrier.majorLog (BitVec.ofNat 64 nsp) ra (BitVec.ofNat 64 (a + 8 * i)) v,
      (e.1 = nsp - 8 ∨ e.1 = a + 8 * i) ∧ e.2.1 = 8 := by
  intro e he
  simp only [Gc.Barrier.majorLog, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨.inl (frame_slot_nat low small), rfl⟩
  · refine ⟨.inr ?_, rfl⟩
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- **The barrier's entry facts from a represented call** that stores field
`i` of the placed block `l`. -/
theorem barrier_entry {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high codeReg : Nat} {ra codeWord stackWord value : BitVec 64} {c : Config}
    {l a i tag : Nat} {fields : List Val} {D : InvocationData}
    (input : ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord (BitVec.ofNat 64 (a + 8 * i)) value c)
    (br : BarrierRuntime L) (inv : Invocation D c) (v : NativeValid D)
    (placed : pl.φ l = some a) (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length) :
    Gc.Barrier.Entry (BitVec.ofNat 64 (a + 8 * i)) value ra (BitVec.ofNat 64 D.nativeSp)
      (word c Layout.sym_Caml_state)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 32).toNat 8)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 40).toNat 8)
      (bytesT c.σ.mem (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8) c := by
  have g := input.geometry.toArmGeometry
  have low := g.heapLow l a _ placed selected
  have arena := g.heapArena l a _ placed selected
  have aligned := g.words.heap l a placed
  have size : (Obj.block tag fields).wosize = fields.length := rfl
  rw [size] at arena
  have dl := g.domainLow
  have da := g.domainArena
  have dal := g.domainAligned
  have dh := g.domainHeap l a _ placed selected
  rw [size] at dh
  obtain ⟨dh, -⟩ := dh
  dsimp only at dh
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have nlow : 32 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have facts : 0x80000000 ≤ Layout.sym_bss_end ∧ Layout.sym_tohost + 16 ≤ Layout.sym_bss_end ∧
      Vsa.Sim.DlHeap.heapEnd ≤ 0x100000000 ∧ Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_gc_phase + 8 ≤ Layout.sym_bss_end ∧ 0x8000aa98 ≤ Layout.sym_bss_end := by decide
  obtain ⟨fRam, fTohost, fEnd, fDom, fPhase, fCode⟩ := facts
  have sn := barrier_slot_nat (a := a) (i := i) (by omega)
  have fn := frame_slot_nat nlow small
  have d32 := domain_addr g (off := 32) (by decide)
  have d40 := domain_addr g (off := 40) (by decide)
  simp only [Layout.domainStateBytes] at da dh
  refine
    { good := input.good, tick := input.tick, minstret := input.minstret
      code := caml_modify_loaded input.image
      slotReg := input.slot, valueReg := input.value, raReg := input.raReg
      stackReg := inv.stack, raAligned := input.aligned
      domain := rfl, youngStart := rfl, youngEnd := rfl
      startRead := ⟨by rw [d32]; omega, by rw [d32]; omega, Or.inr (by rw [d32]; omega)⟩
      endRead := ⟨by rw [d40]; omega, by rw [d40]; omega, Or.inr (by rw [d40]; omega)⟩
      slotWrite := ⟨by rw [sn]; omega, by rw [sn]; omega, by rw [sn]; omega, by rw [sn]; omega⟩
      oldWord := rfl
      frameWrite := ⟨by rw [fn]; simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega,
        by rw [fn]; simp only [Layout.sym_stack_top] at ht; omega,
        by rw [fn]; simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Layout.sym_tohost] at hh ⊢; omega,
        by rw [fn]; have := v.aligned; omega⟩
      idle := br.idle c input.runtime
      slotFrame := by rw [sn, fn]; left; simp only [nativeHeadroom] at hh; omega
      aboveCode := ?_
      readsApart := ?_ }
  · intro e he
    obtain ⟨addr, -⟩ := majorLog_addrs nlow small (by omega) e he
    simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh da arena
    omega
  · intro x hx e he
    obtain ⟨addr, width⟩ := majorLog_addrs nlow small (by omega) e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh da arena
    rw [width]
    rcases hx with rfl | rfl | rfl | rfl <;> (try rw [d32]) <;> (try rw [d40]) <;> omega

/-- **The remembered set at the barrier's entry**, from the collector's
runtime facts. -/
theorem barrier_remembered {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high codeReg : Nat} {ra codeWord stackWord value : BitVec 64} {c : Config}
    {l a i tag : Nat} {fields : List Val} {D : InvocationData} {tbl ptr limit : BitVec 64}
    (input : ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord (BitVec.ofNat 64 (a + 8 * i)) value c)
    (v : NativeValid D)
    (placed : pl.φ l = some a) (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length)
    (table : Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem)
    (arena : tbl.toNat + 40 ≤ Vsa.Sim.DlHeap.heapEnd ∧
      (ptr.toNat < limit.toNat → ptr.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd))
    (sep : Gc.WindowSeparated ⟨tbl.toNat, tbl.toNat + 40⟩ P s c pl cp high ∧
      (ptr.toNat < limit.toNat → Gc.WindowSeparated ⟨ptr.toNat, ptr.toNat + 8⟩ P s c pl cp high)) :
    Gc.Barrier.Remembered (BitVec.ofNat 64 D.nativeSp) ra (BitVec.ofNat 64 (a + 8 * i)) value
      (word c Layout.sym_Caml_state) tbl ptr limit c := by
  have g := input.geometry.toArmGeometry
  have low := g.heapLow l a _ placed selected
  have objArena := g.heapArena l a _ placed selected
  have size : (Obj.block tag fields).wosize = fields.length := rfl
  rw [size] at objArena
  have dh := g.domainHeap l a _ placed selected
  rw [size] at dh
  obtain ⟨dh, -⟩ := dh
  dsimp only at dh
  have da := g.domainArena
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have nlow : 32 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have d104 := domain_addr g (off := 104) (by decide)
  have tblHeap := (sep.1.heap l a _ placed selected).1
  rw [size] at tblHeap
  dsimp only at tblHeap
  have tblLow := sep.1.statics
  dsimp only at tblLow
  have fCode : 0x8000aa98 ≤ Layout.sym_bss_end := by decide
  obtain ⟨tA, pA⟩ := arena
  have t24 : (tbl + BitVec.ofNat 64 24).toNat = tbl.toNat + 24 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Vsa.Sim.DlHeap.heapEnd] at tA ⊢; omega
  have t32 : (tbl + BitVec.ofNat 64 32).toNat = tbl.toNat + 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Vsa.Sim.DlHeap.heapEnd] at tA ⊢; omega
  simp only [Layout.domainStateBytes, nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at da dh hh tA pA objArena
  refine ⟨table, ?_, ?_, ?_⟩
  · intro x hx e he
    obtain ⟨addr, width⟩ := majorLog_addrs nlow small (by omega) e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [width]
    rcases hx with rfl | rfl | rfl <;> (try rw [d104]) <;> (try rw [t24]) <;> (try rw [t32]) <;> omega
  all_goals
    intro room e he
    have pRoom := pA room
    have pLow := (sep.2 room).statics
    dsimp only at pLow
    have p0 : (ptr + BitVec.ofNat 64 0).toNat = ptr.toNat := by simp
    simp only [Gc.Barrier.insertLog, List.mem_cons, List.not_mem_nil, or_false] at he
  · rw [frame_slot_nat nlow small]
    rcases he with rfl | rfl
    · dsimp only; rw [t24]; omega
    · dsimp only; rw [p0]; omega
  · rcases he with rfl | rfl
    · dsimp only; rw [t24]; omega
    · dsimp only; rw [p0]; omega

/-! ## The represented state across the barrier's stores -/

/-- The represented components the barrier carries between its stores, at a
fixed native invocation `D`. -/
structure BarrierState (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) (D : InvocationData) (c : Config) : Prop where
  data : VmPayload P s c pl cp sp high
  primitives : PrimitiveBindings P c
  image : ExecutableImage c
  runtime : L.runtimeOk c
  geometry : OCaml.LoopGeometry L P s c pl cp high
  invocation : Invocation D c
  /-- the stack fits its allocation -/
  low : high - Layout.stackBytes ≤ sp

/-- **Stores in windows apart from the payload** keep the represented state,
given that the runtime is stable on them and the native invocation misses
them. -/
theorem BarrierState.separated_step {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {D : InvocationData} {c c' : Config} {ws : List W} {log : List WEntry}
    (h : BarrierState L P s pl cp sp high D c)
    (inside : LogInW ws log) (each : ∀ w ∈ ws, Gc.WindowSeparated w P s c pl cp high)
    (runtime : L.runtimeOk c → L.runtimeOk c') (invocation : InvocationOutside D log)
    (memory : c'.σ.mem = writeLog c.σ.mem log) (output : c'.σ.sailOutput = c.σ.sailOutput)
    (stack : gpr c' 2 = gpr c 2) :
    BarrierState L P s pl cp sp high D c' := by
  have sg := h.geometry.toArmGeometry.toStackGeometry
  have hs := h.data.stack.1
  have low := h.low
  have lw : LogWindows log P s c pl cp (high - Layout.stackBytes) high [] :=
    ⟨sg, ⟨ws, inside, fun w hw => .separated (each w hw)⟩, by omega, by simp⟩
  have pay := lw.payload hs low (by omega) (by simp) (by simp)
  have young := lw.young (by simp)
  have binds := lw.bindings
  exact
    { data := h.data.frame_log pay memory output
      primitives := bindings_frame_log h.primitives binds memory
      image := image_of_writeLog h.image lw.image memory
      runtime := runtime h.runtime
      geometry := h.geometry.frame_log rfl rfl pay.domain binds.contents pay.channels pay.openHead young memory
      invocation := h.invocation.frame_log invocation memory stack
      low := low }

/-- **The slot store**: field `i` of the placed block `l` becomes `value`. -/
theorem BarrierState.field_step {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {D : InvocationData} {c c' : Config} {l a i tag : Nat} {fields : List Val}
    {value : Val} {w : BitVec 64}
    (h : BarrierState L P s pl cp sp high D c) (v : NativeValid D)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length)
    (represented : valWord pl value = some w)
    (root : ∀ loc, value.loc? = some loc → Live s.heap (roots P s) loc)
    (stable : WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩])
    (memory : c'.σ.mem = writeLog c.σ.mem (fieldLog a i w)) (output : c'.σ.sailOutput = c.σ.sailOutput)
    (stack : gpr c' 2 = gpr c 2) :
    BarrierState L P {s with heap := s.heap.set l (.block tag (fields.set i value))} pl cp sp high D c' := by
  have g := h.geometry.toArmGeometry
  have hs := h.data.stack.1
  have lowS := h.low
  have space : 8 * s.stack.length ≤ Layout.stackBytes := by omega
  have ok := FieldWriteOk.of_geometry (w := w) g h.data.stack space placed selected bound
  have low := g.heapLow l a _ placed selected
  have arena := g.heapArena l a _ placed selected
  have size : (Obj.block tag fields).wosize = fields.length := rfl
  rw [size] at arena
  have hh := v.headroom
  have external := ok.young.external
  rw [h.invocation.domain] at external
  exact
    { data := payload_field_written h.data live placed selected (by omega) bound represented root
        ok.payload memory output
      primitives := bindings_frame_log h.primitives ok.bindings memory
      image := image_of_writeLog h.image ok.image memory
      runtime := stable c c' (by
        rw [memory]; apply frameOn_writeLog
        simp only [fieldLog, LogInW, InsideW, or_false, and_true]
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩) h.runtime
      geometry := h.geometry.heap_set selected (by simp only [Obj.wosize, List.length_set]) rfl rfl
        ok.payload.domain ok.bindings.contents ok.payload.channels ok.payload.openHead ok.young memory
      invocation := h.invocation.frame_log ⟨ok.payload.domain, fun r _ => by
          simp only [fieldLog, OutLRange, and_true]
          simp only [nativeHeadroom] at hh
          omega, external⟩ memory stack
      low := lowS }

/-! ## The fast path's logs in represented terms -/

/-- A configuration with its memory replaced (registers and output kept). -/
def memAt (c : Config) (m : Std.ExtHashMap Nat (BitVec 8)) : Config := { c with σ := { c.σ with mem := m } }

/-- The young-slot store is the field store. -/
theorem youngLog_eq {a i : Nat} {v : BitVec 64} (fits : a + 8 * i < 2 ^ 64) :
    Gc.Barrier.youngLog (BitVec.ofNat 64 (a + 8 * i)) v = fieldLog a i v := by
  simp only [Gc.Barrier.youngLog, fieldLog, barrier_slot_nat fits]

/-- The major path's field address (offset twice by zero). -/
theorem major_slot_nat {a i : Nat} (fits : a + 8 * i < 2 ^ 64) :
    ((BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0) + BitVec.ofNat 64 0).toNat = a + 8 * i := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The major-slot stores: the frame slot, then the field store. -/
theorem majorLog_eq {nsp a i : Nat} {ra v : BitVec 64} (low : 32 ≤ nsp) (small : nsp < 2 ^ 64)
    (fits : a + 8 * i < 2 ^ 64) :
    Gc.Barrier.majorLog (BitVec.ofNat 64 nsp) ra (BitVec.ofNat 64 (a + 8 * i)) v =
      [(nsp - 8, 8, ra)] ++ fieldLog a i v := by
  simp only [Gc.Barrier.majorLog, fieldLog, frame_slot_nat low small, major_slot_nat fits,
    List.singleton_append]

/-! ## The fast path, represented -/

/-- The registers a `caml_modify` call may change: the ABI's caller-saved
registers and `sp` (the growth path runs newlib's malloc). The interpreter's
loop registers are callee-saved. -/
def barrierClobber : List Nat := [1, 2, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- **The barrier returned**: the represented state with the written field,
and the native return (pc = `ra`, registers outside `barrierClobber`
kept). -/
structure BarrierDone (L : OCaml.Layout) (P : Prog) (s : St) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) (D : InvocationData) (ra : BitVec 64) (before after : Config) : Prop where
  state : BarrierState L P s pl cp sp high D after
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some ra
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ barrierClobber, (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

/-- The native frame store misses the invocation and lies in the native
scratch window. -/
theorem frame_store_ok {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    {D : InvocationData} {ra : BitVec 64} (g : StackGeometry P s c pl cp high) (v : NativeValid D)
    (inv : Invocation D c) :
    LogInW [nativeScratch D] [(D.nativeSp - 8, 8, ra)] ∧ InvocationOutside D [(D.nativeSp - 8, 8, ra)] := by
  have hh := v.headroom
  have da := g.domainArena
  have dl := g.domainLow
  have dom := inv.domain
  have fits : Layout.off_external_raise + 8 ≤ Layout.domainStateBytes ∧
      Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
  rw [dom] at da dl
  simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Layout.domainStateBytes, Layout.sym_bss_end] at hh da dl fits
  refine ⟨?_, ⟨?_, fun r _ => ?_, ?_⟩⟩
  · simp only [nativeScratch, nativeHeadroom, LogInW, InsideW, or_false, and_true]; omega
  · simp only [OutLRange, and_true]; simp only [Layout.sym_Caml_state] at fits ⊢; omega
  · simp only [OutLRange, and_true]; omega
  · simp only [OutLRange, and_true]; omega

/-- **The fast path from a represented call**: the barrier summary's run,
followed through its three possible logs. -/
theorem barrier_core {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high codeReg : Nat} {ra codeWord stackWord value : BitVec 64} {c : Config}
    {l a i tag : Nat} {fields : List Val} {vVal : Val} {D : InvocationData} {tbl ptr limit : BitVec 64}
    {high0 dom0 : Nat}
    (input : ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord (BitVec.ofNat 64 (a + 8 * i)) value c)
    (br : BarrierRuntime L) (rr : RaiseRuntimeFrame L high0 dom0)
    (inv : Invocation D c) (v : NativeValid D) (low : high - Layout.stackBytes ≤ sp)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length)
    (represented : valWord pl vVal = some value)
    (root : ∀ loc, vVal.loc? = some loc → Live s.heap (roots P s) loc)
    (fieldStable : WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩])
    (rem : Gc.Barrier.Remembered (BitVec.ofNat 64 D.nativeSp) ra (BitVec.ofNat 64 (a + 8 * i)) value
      (word c Layout.sym_Caml_state) tbl ptr limit c)
    (noGrow : Gc.Barrier.NoGrow (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 32).toNat 8)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 40).toNat 8)
      (BitVec.ofNat 64 (a + 8 * i)) (bytesT c.σ.mem (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8)
      value ptr limit) :
    FnSummary (0x8000a9a8#64) (fun e => e = c)
      (BarrierDone L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D ra c) := by
  have g := input.geometry.toArmGeometry
  have objArena := g.heapArena l a _ placed selected
  have size : (Obj.block tag fields).wosize = fields.length := rfl
  rw [size] at objArena
  have hh := v.headroom
  have ht := v.high
  have small : D.nativeSp < 2 ^ 64 := by simp only [Layout.sym_stack_top] at ht; omega
  have nlow : 32 ≤ D.nativeSp := by simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh; omega
  have fits : a + 8 * i < 2 ^ 64 := by simp only [Vsa.Sim.DlHeap.heapEnd] at objArena; omega
  have entry := barrier_entry input br inv v placed selected bound
  apply (Gc.Barrier.barrier_fast entry rem noGrow).weaken (fun _ h => h)
  intro after ⟨fd⟩
  obtain ⟨log, which, ret⟩ := fd
  have state0 : BarrierState L P s pl cp sp high D c :=
    ⟨input.data, input.primitives, input.image, input.runtime, input.geometry, inv, low⟩
  have stack : ∀ c' : Config, gpr c' 2 = some (BitVec.ofNat 64 D.nativeSp) → gpr c' 2 = gpr c 2 :=
    fun c' h => h.trans inv.stack.symm
  have afterStack : gpr after 2 = gpr c 2 := stack after ret.stack
  have finish : ∀ st : BarrierState L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))}
      pl cp sp high D after,
      BarrierDone L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D ra c after :=
    fun st => ⟨st, ret.good, ret.tick, ret.minstret, ret.pc, fun r noise out =>
      ret.frame r noise fun n hn => out n (by revert n; decide)⟩
  -- the frame store, shared by both major paths
  have major : ∀ c2 : Config, c2.σ.mem = writeLog c.σ.mem (Gc.Barrier.majorLog
      (BitVec.ofNat 64 D.nativeSp) ra (BitVec.ofNat 64 (a + 8 * i)) value) →
      c2.σ.sailOutput = c.σ.sailOutput → gpr c2 2 = gpr c 2 →
      BarrierState L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D c2 := by
    intro c2 mem2 out2 stack2
    obtain ⟨frameIn, frameOut⟩ := frame_store_ok (ra := ra) g.toStackGeometry v inv
    let c1 := memAt c (writeLog c.σ.mem [(D.nativeSp - 8, 8, ra)])
    have st1 : BarrierState L P s pl cp sp high D c1 :=
      state0.separated_step frameIn
        (fun w hw => by
          simp only [List.mem_singleton] at hw
          subst hw
          exact Gc.WindowSeparated.of_above g.toStackGeometry
            (show _ ≤ D.nativeSp - nativeHeadroom from Nat.le_sub_of_add_le v.headroom))
        (fun ok => rr.scratch [nativeScratch D] D v (fun w hw => .inr (List.mem_singleton.1 hw)) c c1
          (frameOn_writeLog _ _ _ frameIn) ok)
        frameOut rfl rfl rfl
    exact st1.field_step v live placed selected bound represented root fieldStable
      (by rw [mem2, majorLog_eq nlow small fits, writeLog_append]; rfl) out2 stack2
  rcases which with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨notYoung, notOld, young, rfl⟩
  · -- the young slot: the field store alone
    exact finish (state0.field_step v live placed selected bound represented root fieldStable
      (by rw [ret.memory, youngLog_eq fits]) ret.output afterStack)
  · -- the major slot without insertion
    exact finish (major after ret.memory ret.output afterStack)
  · -- the major slot and a remembered-set insertion
    have room : ptr.toNat < limit.toNat := by
      rcases noGrow with h | h | h | h
      · exact absurd h notYoung
      · exact absurd h notOld
      · exact absurd young h
      · exact h
    let c2 := memAt c (writeLog c.σ.mem (Gc.Barrier.majorLog
      (BitVec.ofNat 64 D.nativeSp) ra (BitVec.ofNat 64 (a + 8 * i)) value))
    have st2 := major c2 rfl rfl rfl
    have dom2 : word c2 Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
      st2.invocation.domain.trans inv.domain.symm
    have table2 : Gc.Barrier.Table (word c2 Layout.sym_Caml_state) tbl ptr limit c2.σ.mem := by
      rw [dom2]; exact rem.table.writeLog rem.stored
    obtain ⟨tbl', ptr', limit', table', arena', sepAll⟩ := br.table c2 st2.runtime
    have eT : tbl' = tbl := table'.tableWord.symm.trans table2.tableWord
    rw [eT] at table' arena' sepAll
    have eP : ptr' = ptr := table'.ptrWord.symm.trans table2.ptrWord
    have eL : limit' = limit := table'.limitWord.symm.trans table2.limitWord
    rw [eP, eL] at arena' sepAll
    have sep := sepAll P _ pl cp high st2.geometry st2.data.codeBase st2.data.stackHigh
    obtain ⟨tA, pA⟩ := arena'
    have pA := pA room
    have sepT := sep.1
    have sepP := sep.2 room
    have tLow := sepT.statics
    have pLow := sepP.statics
    dsimp only at tLow pLow
    have t24 : (tbl + BitVec.ofNat 64 24).toNat = tbl.toNat + 24 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Vsa.Sim.DlHeap.heapEnd] at tA ⊢; omega
    have p0 : (ptr + BitVec.ofNat 64 0).toNat = ptr.toNat := by simp
    have inside : LogInW [⟨tbl.toNat, tbl.toNat + 40⟩, ⟨ptr.toNat, ptr.toNat + 8⟩]
        (Gc.Barrier.insertLog tbl ptr (BitVec.ofNat 64 (a + 8 * i))) := by
      simp only [Gc.Barrier.insertLog, LogInW, InsideW, t24, p0, or_false, and_true]
      exact ⟨.inl ⟨by omega, by omega⟩, .inr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
    have dRec := sepT.domain.1
    have dRecP := sepP.domain.1
    rw [dom2] at dRec dRecP
    have dl := g.domainLow
    have fits' : Layout.off_external_raise + 8 ≤ Layout.domainStateBytes ∧
        Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end := by decide
    rw [inv.domain] at dRec dRecP dl
    simp only [nativeHeadroom, Vsa.Sim.DlHeap.heapEnd] at hh tA pA
    have invOut : InvocationOutside D (Gc.Barrier.insertLog tbl ptr (BitVec.ofNat 64 (a + 8 * i))) := by
      simp only [Gc.Barrier.insertLog, t24, p0]
      refine ⟨?_, fun r _ => ?_, ?_⟩ <;> simp only [OutLRange, and_true] <;> dsimp only at dRec dRecP <;>
        simp only [Layout.domainStateBytes, Layout.sym_bss_end, Layout.sym_Caml_state] at fits' dRec dRecP tLow pLow dl ⊢ <;>
        omega
    have memory : after.σ.mem = writeLog c2.σ.mem (Gc.Barrier.insertLog tbl ptr (BitVec.ofNat 64 (a + 8 * i))) := by
      rw [ret.memory, writeLog_append]; rfl
    exact finish (st2.separated_step inside
      (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact sepT
        · exact sepP)
      (fun ok => br.insert c2 tbl ptr limit _ ok table2 room after memory ok)
      invOut memory ret.output afterStack)

/-! ## The represented return -/

/-- **The barrier's represented return** at any caller's target state, given
how the caller's target differs from the written state (pc, accumulator,
consumed stack). -/
theorem modify_return_of_done {L : OCaml.Layout} {P : Prog} {s s' target : St} {pl : Place} {cp : ChanPlace}
    {sp targetSp high codeReg : Nat} {ra codeWord stackWord slot value : BitVec 64} {D : InvocationData}
    {c after : Config}
    (input : ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord slot value c)
    (done : BarrierDone L P s' pl cp sp high D ra c after) (v : NativeValid D)
    (data : VmPayload P s' after pl cp sp high → VmPayload P target after pl cp targetSp high)
    (geometry : OCaml.LoopGeometry L P s' after pl cp high → OCaml.LoopGeometry L P target after pl cp high)
    (env : target.env = s.env) (extra : target.extra = s.extra) (unit : target.accu = .unit)
    (codeLow : 1 ≤ codeReg) (codeHigh : codeReg ≤ 31)
    (codeOut : codeReg ∉ barrierClobber) :
    ModifyReturn L P target pl cp targetSp high codeReg ra codeWord stackWord after := by
  have keep := Gc.Barrier.frame_gpr (by decide) done.frame
  obtain ⟨w, reg, val⟩ := input.env
  exact
    { data := data done.state.data
      primitives := done.state.primitives
      platform := ⟨done.good, done.state.image, done.state.runtime⟩
      loop := loopRegisters_frame (fun r hr => done.frame r (by revert r; decide) (by revert r; decide))
        input.loop
      tick := done.tick
      returnPC := done.pc
      code := (keep codeReg codeLow codeHigh codeOut).trans input.code
      stack := (keep 9 (by decide) (by decide) (by decide)).trans input.stack
      env := ⟨w, (keep 25 (by decide) (by decide) (by decide)).trans reg, by rw [env]; exact val⟩
      extra := by rw [extra]; exact (keep 18 (by decide) (by decide) (by decide)).trans input.extra
      unit := unit
      geometry := geometry done.state.geometry
      native := ⟨D, done.state.invocation, v⟩ }

/-! ## Growth, and the whole barrier -/

/-- **The growth path of an unallocated remembered set** (named premise, GC
lane: a6-gc's `barrier_grow` with the F1 invariants): a call whose empty
remembered set must be allocated also returns with the written field and the
runtime kept. -/
structure BarrierGrowth (L : OCaml.Layout) : Prop where
  grow : ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (sp high codeReg : Nat)
    (ra codeWord stackWord value : BitVec 64) (c : Config) (l a i tag : Nat) (fields : List Val)
    (vVal : Val) (D : InvocationData) (tbl ptr limit : BitVec 64),
    ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord (BitVec.ofNat 64 (a + 8 * i)) value c →
    Invocation D c → NativeValid D → high - Layout.stackBytes ≤ sp →
    Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some (.block tag fields) →
    i < fields.length → valWord pl vVal = some value →
    (∀ loc, vVal.loc? = some loc → Live s.heap (roots P s) loc) →
    WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩] →
    Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem →
    word c (tbl + BitVec.ofNat 64 0).toNat = 0#64 →
    ¬ Gc.Barrier.NoGrow (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 32).toNat 8)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 40).toNat 8)
      (BitVec.ofNat 64 (a + 8 * i)) (bytesT c.σ.mem (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8)
      value ptr limit →
    FnSummary (0x8000a9a8#64) (fun e => e = c)
      (BarrierDone L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D ra c)

/-- **The growth path of a full allocated remembered set** (named premise, GC
lane: `caml_realloc_ref_table`'s realloc branch through newlib's
`_realloc_r`, not yet proved). -/
structure BarrierGrowthFull (L : OCaml.Layout) : Prop where
  grow : ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (sp high codeReg : Nat)
    (ra codeWord stackWord value : BitVec 64) (c : Config) (l a i tag : Nat) (fields : List Val)
    (vVal : Val) (D : InvocationData) (tbl ptr limit : BitVec 64),
    ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord (BitVec.ofNat 64 (a + 8 * i)) value c →
    Invocation D c → NativeValid D → high - Layout.stackBytes ≤ sp →
    Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some (.block tag fields) →
    i < fields.length → valWord pl vVal = some value →
    (∀ loc, vVal.loc? = some loc → Live s.heap (roots P s) loc) →
    WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩] →
    Gc.Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem →
    word c (tbl + BitVec.ofNat 64 0).toNat ≠ 0#64 →
    ¬ Gc.Barrier.NoGrow (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 32).toNat 8)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 40).toNat 8)
      (BitVec.ofNat 64 (a + 8 * i)) (bytesT c.σ.mem (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8)
      value ptr limit →
    FnSummary (0x8000a9a8#64) (fun e => e = c)
      (BarrierDone L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D ra c)

/-- **Both growth paths** of the remembered set (GC lane): the layout-level
premise of the F1 barrier rows. -/
structure BarrierGrowthPaths (L : OCaml.Layout) : Prop where
  empty : BarrierGrowth L
  full : BarrierGrowthFull L

/-- **`caml_modify` from a represented call**, fast or growing. -/
theorem barrier_summary {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high codeReg : Nat} {ra codeWord stackWord value : BitVec 64} {c : Config}
    {l a i tag : Nat} {fields : List Val} {vVal : Val} {high0 dom0 : Nat}
    (br : BarrierRuntime L) (rr : RaiseRuntimeFrame L high0 dom0) (growth : BarrierGrowth L)
    (growthFull : BarrierGrowthFull L)
    (input : ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord (BitVec.ofNat 64 (a + 8 * i)) value c)
    (low : high - Layout.stackBytes ≤ sp)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields)) (bound : i < fields.length)
    (represented : valWord pl vVal = some value)
    (root : ∀ loc, vVal.loc? = some loc → Live s.heap (roots P s) loc)
    (fieldStable : WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩]) :
    FnSummary (0x8000a9a8#64) (fun e => e = c)
      (fun after => ∃ D, NativeValid D ∧
        BarrierDone L P {s with heap := s.heap.set l (.block tag (fields.set i vVal))} pl cp sp high D ra c after) := by
  obtain ⟨D, inv, v⟩ := input.native
  obtain ⟨tbl, ptr, limit, table, arena, sepAll⟩ := br.table c input.runtime
  have rem := barrier_remembered (D := D) input v placed selected bound table arena
    (sepAll P s pl cp high input.geometry input.data.codeBase input.data.stackHigh)
  by_cases noGrow : Gc.Barrier.NoGrow (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 32).toNat 8)
      (bytesT c.σ.mem (word c Layout.sym_Caml_state + BitVec.ofNat 64 40).toNat 8)
      (BitVec.ofNat 64 (a + 8 * i)) (bytesT c.σ.mem (BitVec.ofNat 64 (a + 8 * i) + BitVec.ofNat 64 0).toNat 8)
      value ptr limit
  · exact (barrier_core input br rr inv v low live placed selected bound represented root fieldStable rem
      noGrow).weaken (fun _ h => h) (fun _ done => ⟨D, v, done⟩)
  · by_cases empty : word c (tbl + BitVec.ofNat 64 0).toNat = 0#64
    · exact (growth.grow P s pl cp sp high codeReg ra codeWord stackWord value c l a i tag fields vVal D
        tbl ptr limit input inv v low live placed selected bound represented root fieldStable table
        empty noGrow).weaken (fun _ h => h) (fun _ done => ⟨D, v, done⟩)
    · exact (growthFull.grow P s pl cp sp high codeReg ra codeWord stackWord value c l a i tag fields vVal D
        tbl ptr limit input inv v low live placed selected bound represented root fieldStable table
        empty noGrow).weaken (fun _ h => h) (fun _ done => ⟨D, v, done⟩)

/-! ## The barrier rows' callees for F1 -/

/-- Inverting a successful field store. -/
theorem setField?_inv {h : Heap} {base : Val} {i : Nat} {x : Val} {h' : Heap}
    (e : setField? h base i x = some h') :
    ∃ l k tag fs, base = .ptr l k ∧ h.get? l = some (.block tag fs) ∧ k + i < fs.length ∧
      h' = h.set l (.block tag (fs.set (k + i) x)) := by
  cases base with
  | ptr l k =>
    simp only [setField?] at e
    split at e
    · rename_i tag fs got
      split at e
      · rename_i room
        exact ⟨l, k, tag, fs, rfl, got, room, (Option.some.inj e).symm⟩
      · cases e
    · cases e
  | _ => simp [setField?] at e

/-- **`GlobalBarrier` for the F1 layout**: SETGLOBAL's `caml_modify`, given the
collector's barrier runtime and growth path (GC lane). -/
theorem f1_globalBarrier {P : Prog} (br : BarrierRuntime Gc.f1Layout) (growth : BarrierGrowth Gc.f1Layout)
    (growthFull : BarrierGrowthFull Gc.f1Layout)
    (fits : OCaml.Fits Gc.g1Budget P) (capacity : StackCapacity Gc.g1Budget) :
    GlobalBarrier Gc.f1Layout P where
  callee s c pl cp sp high ofs value heap reach h nonnegative encoded update := by
    obtain ⟨l, k, tag, fs, glob, got, room, heapEq⟩ := setField?_inv update
    have gw := h.toVmReprAt.globals
    rw [glob] at gw
    simp only [valWord, Option.map_eq_some_iff] at gw
    obtain ⟨a, placed, wordEq⟩ := gw
    have slotEq : BitVec.ofNat 64 (8 * ofs.toInt.toNat) + word c Layout.sym_caml_global_data =
        BitVec.ofNat 64 (a + 8 * (k + ofs.toInt.toNat)) := by
      rw [← wordEq, ofNat_add_ofNat']
      congr 1
      omega
    have space := stack_fits fits capacity reach (k := 0)
    simp only [Nat.add_zero] at space
    have ready := (f1_fieldWriteReady h.runtime space).ready pl cp sp high l a (k + ofs.toInt.toNat) tag fs
      value h.toVmReprAt h.geometry placed got room
    have live : Live s.heap (roots P s) l := Live.root (v := .ptr l k) (by simp [roots, glob]) rfl
    have root : ∀ loc, s.accu.loc? = some loc → Live s.heap (roots P s) loc :=
      fun loc hl => Live.root (by simp [roots]) hl
    refine ⟨⟨?_⟩⟩
    rintro before ⟨pc, input⟩
    have hs := input.data.stack.1
    have low : high - Layout.stackBytes ≤ sp := by omega
    rw [slotEq] at input
    obtain ⟨after, run, D, v, done⟩ := (barrier_summary br f1_raiseRuntimeFrame growth growthFull input low live
      placed got room encoded root ready.1).run before ⟨pc, rfl⟩
    subst heapEq
    exact ⟨after, run, modify_return_of_done input done v (fun d => payload_pc (d.accu_int 0) _)
      (fun g => g.state rfl rfl) rfl rfl rfl (by decide) (by decide) (by decide)⟩

/-- **A SETFIELD-shaped `caml_modify` call for F1**: field `j` of the
accumulator's block takes the popped stack top. -/
theorem f1_field_callee {P : Prog} {op : Opcode} (br : BarrierRuntime Gc.f1Layout)
    (growth : BarrierGrowth Gc.f1Layout) (growthFull : BarrierGrowthFull Gc.f1Layout)
    (fits : OCaml.Fits Gc.g1Budget P) (capacity : StackCapacity Gc.g1Budget)
    {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high j codeReg pcNext : Nat}
    {base value ra codeWord stackWord slot : BitVec 64} {v : Val} {rest : List Val} {heap : Heap}
    (reach : Reach P s) (h : ArmInput Gc.f1Layout P s op c pl cp sp high)
    (source : valWord pl s.accu = some base) (stack : s.stack = v :: rest)
    (encoded : valWord pl v = some value) (update : setField? s.heap s.accu j v = some heap)
    (slotEq : slot = base + BitVec.ofNat 64 (8 * j))
    (codeLow : 1 ≤ codeReg) (codeHigh : codeReg ≤ 31) (codeOut : codeReg ∉ barrierClobber) :
    ModifyCallee Gc.f1Layout P s {s with pc := pcNext, accu := .unit, heap := heap, stack := rest} pl cp sp
      (sp + 8) high codeReg ra codeWord stackWord slot value := by
  obtain ⟨l, k, tag, fs, acc, got, room, heapEq⟩ := setField?_inv update
  rw [acc] at source
  simp only [valWord, Option.map_eq_some_iff] at source
  obtain ⟨a, placed, wordEq⟩ := source
  have slotNat : slot = BitVec.ofNat 64 (a + 8 * (k + j)) := by
    rw [slotEq, ← wordEq, ofNat_add_ofNat']
    congr 1
    omega
  have space := stack_fits fits capacity reach (k := 0)
  simp only [Nat.add_zero] at space
  have ready := (f1_fieldWriteReady h.runtime space).ready pl cp sp high l a (k + j) tag fs
    value h.toVmReprAt h.geometry placed got room
  have live : Live s.heap (roots P s) l := Live.root (v := .ptr l k) (by simp [roots, acc]) rfl
  have root : ∀ loc, v.loc? = some loc → Live s.heap (roots P s) loc :=
    fun loc hl => Live.root (by simp [roots, stack]) hl
  refine ⟨⟨?_⟩⟩
  rintro before ⟨pc, input⟩
  have hs := input.data.stack.1
  have low : high - Layout.stackBytes ≤ sp := by omega
  rw [slotNat] at input
  obtain ⟨after, run, D, nv, done⟩ := (barrier_summary br f1_raiseRuntimeFrame growth growthFull input low live
    placed got room encoded root ready.1).run before ⟨pc, rfl⟩
  subst heapEq
  refine ⟨after, run, modify_return_of_done input done nv (fun d => ?_) (fun g => g.state rfl rfl)
    rfl rfl rfl codeLow codeHigh codeOut⟩
  have dropped := payload_stack_drop (n := 1) (payload_pc (d.accu_int 0) pcNext) (by simp [stack])
  simpa only [stack, List.drop_succ_cons, List.drop_zero, Nat.mul_one, Val.unit] using dropped

/-- **`FieldBarrier` for the F1 layout** (SETFIELD n). -/
theorem f1_fieldBarrier {P : Prog} (br : BarrierRuntime Gc.f1Layout) (growth : BarrierGrowth Gc.f1Layout)
    (growthFull : BarrierGrowthFull Gc.f1Layout)
    (fits : OCaml.Fits Gc.g1Budget P) (capacity : StackCapacity Gc.g1Budget) :
    FieldBarrier Gc.f1Layout P where
  callee s c pl cp sp high ofs base value v rest heap reach h _ source stack encoded update :=
    f1_field_callee br growth growthFull fits capacity reach h source stack encoded update (BitVec.add_comm _ _)
      (by decide) (by decide) (by decide)

/-- **`FieldBarrierK` for the F1 layout** (SETFIELD0–3: field `k`, slot offset `8k`). -/
theorem f1_fieldBarrierK {P : Prog} {op : Opcode} {k : Nat} {ra off : BitVec 64}
    (br : BarrierRuntime Gc.f1Layout) (growth : BarrierGrowth Gc.f1Layout)
    (growthFull : BarrierGrowthFull Gc.f1Layout)
    (fits : OCaml.Fits Gc.g1Budget P) (capacity : StackCapacity Gc.g1Budget)
    (offset : off = BitVec.ofNat 64 (8 * k)) :
    FieldBarrierK Gc.f1Layout P op k ra off where
  callee s c pl cp sp high base value v rest heap reach h source stack encoded update :=
    f1_field_callee br growth growthFull fits capacity reach h source stack encoded update (by rw [offset])
      (by decide) (by decide) (by decide)

end OCaml.Vm.Sim
