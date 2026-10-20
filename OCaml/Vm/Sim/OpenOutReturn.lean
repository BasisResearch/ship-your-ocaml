import OCaml.Vm.Sim.OpenOutPayload
import OCaml.Vm.Sim.OpenOutGeometry
import OCaml.Vm.Sim.PrimOpenOutReturns

/-!
# `caml_ml_open_descriptor_out`'s C_CALL return

`open_out_return` assembles `CcallReturnAt` at the primitive's return under
the extended channel placement: the saved C-call frame and the native
invocation are kept (`static_kept`, `domainField_kept`, `vmStack_kept`,
`native_kept`), the bindings read the kept primitive table
(`primTable_kept`), the payload and the geometry are the opened state's
(`open_out_payload`, `open_out_geometry`), and the runtime holds by
`OpenOutRuntime.after`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel LeanRV64DExecutable

/-- **The C_CALL return of `caml_ml_open_descriptor_out`.** -/
theorem open_out_return {ra : BitVec 64} {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place}
    {cp : ChanPlace} {sp high domain entry : Nat} {env : BitVec 64} {c d : Config}
    {fd : Int} {val : Val} {heap' : Heap} {world' : World} {st : TCB.Os.Stream}
    {k : Nat} {H : List (Nat × Nat)} {cap N : Nat} {r0 r1 r2 v head : BitVec 64}
    {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} (rt : OpenOutRuntimeAt L Ready state)
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (o : OpenedOut imageLive Ready state k H (cap - 65616) 65616 (BitVec.ofNat 64 N) ra r0 r1 r2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput imageLive H (cap - 65616) 65616 (BitVec.ofNat 64 N) ra r0 r1 r2 v head c)
    (Nur : OutNursery H (Gc.placedChannels cp s.world.chans.length) c)
    (nsp : gpr c 2 = some (BitVec.ofNat 64 N))
    (fits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes)
    (ok : openChan s.heap s.world fd true = .ok val heap' world')
    (stream : TCB.Os.lookupFd s.world.os fd.toNat = some (.stream st))
    (fdWord : ((fdOf v).setWidth 32).toInt = fd) (open_ : fd ≠ -1)
    (placed : pl.φ (s.heap.alloc (.channel s.world.chans.length)).2 = some o.value.toNat) :
    CcallReturnAt ra L P { s with pc := s.pc + 2, accu := val, heap := heap', world := world' } pl
      (cp.put s.world.chans.length o.opening.record.toNat) sp high (BitVec.ofNat 64 domain)
      (BitVec.ofNat 64 (sp - 16)) o.value env d := by
  have custom := rt.custom
  have runtime := setup.input.runtime
  have pins := rt.pins c runtime
  have data := setup.input.data
  have g := setup.geometry
  have saved := setup.saved
  obtain ⟨vEq, hEq, -, -⟩ := openChan_ok ok
  have wEq := openChan_stream ok stream
  subst vEq hEq wEq
  have fits0 : 8 * s.stack.length ≤ Layout.stackBytes := by omega
  have keepReg (n : Nat) (lo : 19 ≤ n) (hi : n ≤ 27) : gpr d n = gpr c n := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (setup.input.loop.gprs.get n (by omega) (by omega))
    exact (o.keep_upper lo hi hx).trans hx.symm
  obtain ⟨k8, k9, k18⟩ := o.keep_saved
  have word_static (a : Nat) (mem : a ∈ openStatics) : word d a = word c a :=
    word_of_kept fun j hj => static_kept custom o h Nur mem hj
  have domD : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state := o.domain
  have domC := h.domain
  have domNat : (BitVec.ofNat 64 domain).toNat = Boot.WhileMinRuntime.domain := by
    rw [saved.domainWord]; exact domC
  have stackSpan := data.stack.1
  have space := stack_space data.stack fits0
  have stat := g.toStackGeometry.statics
  have hs : high - Layout.stackBytes + 16 ≤ sp := by omega
  have top := g.toStackGeometry.top
  have frameNat : (BitVec.ofNat 64 (sp - 16)).toNat = sp - 16 := toNat_ofNat_small (by omega)
  have externAddr : (BitVec.ofNat 64 domain + BitVec.ofNat 64 Layout.off_extern_sp).toNat =
      Boot.WhileMinRuntime.domain + Layout.off_extern_sp := by
    rw [BitVec.toNat_add, domNat, BitVec.toNat_ofNat]; decide
  refine {
    toCcall1Saved := { saved with
      domainReg := (keepReg Layout.reg_env (by decide) (by decide)).trans saved.domainReg
      pc := (show gpr d 8 = gpr c 8 by
              show gprGet d.σ 8 = gprGet c.σ 8; rw [k8, h.saved0]).trans saved.pc
      extra := (show gpr d 18 = gpr c 18 by
              show gprGet d.σ 18 = gprGet c.σ 18; rw [k18, h.saved2]).trans saved.extra
      domainWord := saved.domainWord.trans domD.symm
      savedStack := by
        rw [saved.savedStack, externAddr]
        exact (word_of_kept fun j hj => domainField_kept custom o h Nur (off := Layout.off_extern_sp)
          (by decide) (by decide) (by decide) (by omega) (by omega)).symm
      savedEnv := by
        rw [saved.savedEnv, frameNat]
        exact (word_of_kept fun j hj => vmStack_kept custom o heap h Nur pins data
          (by omega) (by omega)).symm }
    toCcallResult := {
      data := payload_pc (open_out_payload custom o heap h Nur pins data g fits0 ok fdWord open_ placed) (s.pc + 2)
      primitives := ⟨fun i name hi => by
        obtain ⟨target, he, t⟩ := setup.input.primitives.targets i name hi
        refine ⟨target, he, ?_⟩
        have size : i < P.prims.size := (Array.getElem?_eq_some_iff.mp hi).1
        have fit := g.nursery.primsFit
        have contents := word_static (Layout.sym_caml_prim_table + Layout.off_prim_contents) (by simp [openStatics])
        have base : (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat =
            Boot.WhileMinHeapChunks.primTablePayload := by rw [pins.primsWord]; rfl
        unfold primitiveTarget at t ⊢
        rw [contents, ← t]
        exact word_of_kept fun j hj => primTable_kept custom o heap h Nur (by rw [base]; omega)
          (by rw [base]; omega)⟩
      platform := ⟨o.done.good, o.done.image, rt.after runtime heap o⟩
      loop := {
        dispatchTable := (keepReg Layout.reg_dispatchTable (by decide) (by decide)).trans
          setup.input.loop.dispatchTable
        opcodeBound := (keepReg Layout.reg_opcodeBound (by decide) (by decide)).trans setup.input.loop.opcodeBound
        pending := (keepReg Layout.reg_pending (by decide) (by decide)).trans setup.input.loop.pending
        domain := (keepReg Layout.reg_domain (by decide) (by decide)).trans setup.input.loop.domain
        htifIdle := o.done.idle
        gprs := ⟨fun n lo hi => o.gprs.present n lo (by omega) (setup.input.loop.gprs.get n lo hi)⟩
        gp := o.gprs.gp.trans setup.input.loop.gp }
      tick := o.done.tick
      returnPC := o.done.pc
      resultReg := o.done.result
      resultRepr := by simp [valWord, placed]
      geometry := open_out_geometry custom o heap h Nur pins data g placed rfl rfl
      native := by
        obtain ⟨D, inv, valid⟩ := setup.native
        have spEq : BitVec.ofNat 64 D.nativeSp = BitVec.ofNat 64 N := Option.some.inj (inv.stack.symm.trans nsp)
        have nN : (BitVec.ofNat 64 N).toNat ≤ D.nativeSp := by
          rw [← spEq, BitVec.toNat_ofNat]; exact Nat.mod_le _ _
        have dD : D.domain.toNat = Boot.WhileMinRuntime.domain := by rw [← inv.domain]; exact domC
        refine ⟨D, ⟨?_, domD.trans inv.domain, ?_, ?_⟩, valid⟩
        · exact o.done.stack.trans (congrArg some spEq.symm)
        · intro r hr i hi
          rw [byte_total, native_kept custom o h Nur (by omega), ← byte_total]
          exact inv.region r hr i hi
        · rw [dD, ← inv.externalRaise, dD]
          exact word_of_kept fun j hj => domainField_kept custom o h Nur (off := Layout.off_external_raise)
            (by decide) (by decide) (by decide) (by omega) (by omega) } }

/-- The tagged console descriptor. -/
theorem console_word {n : BitVec 63} (one : n.toInt = 1 ∨ n.toInt = 2) :
    (tag64 n = 3#64 ∨ tag64 n = 5#64) ∧ ((fdOf (tag64 n)).setWidth 32).toInt = n.toInt := by
  rcases one with e | e
  · have : n = 1#63 := BitVec.eq_of_toInt_eq (by rw [e]; decide)
    subst this; decide
  · have : n = 2#63 := BitVec.eq_of_toInt_eq (by rw [e]; decide)
    subst this; decide

/-- **`caml_ml_open_descriptor_out` at every `C_CALL` site** (premises: the
runtime across the opening, `OpenOutRuntime L`, and `GoodF1`'s console
channels). -/
theorem prim_caml_ml_open_descriptor_out_returns {L : OCaml.Layout} {P : Prog} {op : Opcode}
    {ra : BitVec 64} {k : Nat} (runtime : OpenOutRuntime L) (consoles : OCaml.ConsoleChannels P) :
    PrimReturnsAtR L P op ra k "caml_ml_open_descriptor_out" := by
  obtain ⟨Ready, state, rt⟩ := runtime
  intro s c0 pl cp sp high table entry value env index res heap world _reach ready sem words succ
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  have sem0 := sem
  obtain ⟨n, hacc⟩ : ∃ n, s.accu = .int n := by
    cases h : s.accu <;> simp [primF1Impl, h, intArg?] at sem
    exact ⟨_, rfl⟩
  have ok : openChan s.heap s.world n.toInt true = .ok res heap world := by
    simpa [primF1Impl, hacc, intArg?, opt] using sem
  obtain ⟨one, st, stream, -⟩ := open_out_console consoles succ ok
  obtain ⟨vWord, fdWord⟩ := console_word one
  have hentry : entry = Layout.sym_caml_ml_open_descriptor_out :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_ml_open_descriptor_out)
  subst hentry
  have places : ∀ young : BitVec 64, allocPlaces "caml_ml_open_descriptor_out" s young =
      [((s.heap.alloc (.channel s.world.chans.length)).2, (young - 24#64).toNat + 8)] := fun _ => by
    simp only [allocPlaces, hacc]
  have head0 := ready.allocPlaced _ (by rw [places]; exact List.mem_singleton_self _)
  refine ⟨BitVec.ofNat 64 ((BitVec.ofNat 64 (runtimeFields c0).youngPtr - 24#64).toNat + 8),
    ⟨by decide, sem0, fun c setup placedAt => ?_⟩⟩
  have here := placedAt _ (by rw [places]; exact List.mem_singleton_self _)
  have same : (BitVec.ofNat 64 (runtimeFields c0).youngPtr - 24#64).toNat + 8 =
      (BitVec.ofNat 64 (runtimeFields c).youngPtr - 24#64).toNat + 8 :=
    Option.some.inj (head0.symm.trans here)
  rw [same]
  obtain ⟨vRes, hRes⟩ := openChan_ok ok
  have fits : s.heap.words + 3 ≤ L.budget.heapWords := by
    rw [hRes.1, Heap.words_alloc] at words; exact words
  have value : gpr c 10 = some (tag64 n) :=
    setup.input.arguments.get (i := 0) rfl (by simp [valWord, hacc])
  obtain ⟨H, cap, N, kk, r0, r1, r2, heapA, inp, nur, readyK, nsp⟩ :=
    open_out_entry rt setup fits (openChan_bound ok) value vWord
  have S := ml_open_descriptor_out c H (cap - 65616) 65616 (BitVec.ofNat 64 N) ra r0 r1 r2 (tag64 n) _
    rt.custom kk readyK nur inp
  have pcEq : (BitVec.ofNat 64 Layout.sym_caml_ml_open_descriptor_out : BitVec 64) = 0x80015f50#64 := rfl
  rw [pcEq]
  apply S.weaken (fun _ h => h)
  intro d ⟨o⟩
  have block := o.block
  have room := nur.room
  have topY := setup.geometry.nursery.top
  have yNat : (BitVec.ofNat 64 (runtimeFields c).youngPtr - 24#64).toNat + 8 = o.value.toNat := by
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ofNat_sub_small (by omega) (by omega),
      toNat_ofNat_small (by omega)]
    omega
  have placed : pl.φ (s.heap.alloc (.channel s.world.chans.length)).2 = some o.value.toNat := by
    rw [here, yNat]
  have r : BitVec.ofNat 64 o.value.toNat = o.value := by simp
  rw [yNat, r]
  exact ⟨_, open_out_return rt setup o heapA inp nur nsp ready.stackFits ok stream fdWord
    (by rcases one with e | e <;> omega) placed⟩

end OCaml.Vm.Sim
