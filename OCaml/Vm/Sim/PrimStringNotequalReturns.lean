import OCaml.Vm.Sim.PrimStringEqualReturns
import OCaml.Vm.Sim.CcallWriting
import OCaml.Vm.Sim.PayloadWindows
import OCaml.Vm.Sim.LoopGeometry
import OCaml.Vm.Primitives.CamlStringNotequal
import OCaml.Vm.Primitives.Console.Geometry

/-! `caml_string_notequal` at every `C_CALL` site: the word comparison of
`caml_string_equal`, wrapped in a frame whose saved `ra` is the one store, just
below the native stack pointer (above the allocator arena). -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Gc

/-- **The loop geometry across stores above the arena**: the heap and the
world are kept, and every word the geometry reads lies below `heapEnd`. -/
theorem LoopGeometry.of_above {L : OCaml.Layout} {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high : Nat} (g : OCaml.LoopGeometry L P s c pl cp high)
    (heap : s'.heap = s.heap) (chans : s'.world.chans = s.world.chans)
    (memory : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → byte c' x = byte c x) :
    OCaml.LoopGeometry L P s' c' pl cp high := by
  have SG := g.toArmGeometry.toStackGeometry
  have kept : ∀ a, a + 8 ≤ Vsa.Sim.DlHeap.heapEnd → word c' a = word c a :=
    fun a h => Reloc.bytesT_congr fun j hj => memory _ (by omega)
  have hb : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapEnd := by
    rw [show Layout.sym_bss_end = 0x8007d138 from rfl, show Vsa.Sim.DlHeap.heapEnd = 0x86800000 from rfl]; omega
  have stat : ∀ a, a + 8 ≤ Layout.sym_bss_end → word c' a = word c a := fun a h => kept a (by omega)
  have domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    stat _ (by rw [show Layout.sym_Caml_state = 0x80064d08 from rfl, show Layout.sym_bss_end = 0x8007d138 from rfl]; omega)
  have da := SG.domainArena
  rw [show Layout.domainStateBytes = 928 from rfl] at da
  have field : ∀ off, off + 8 ≤ 928 → word c' ((word c Layout.sym_Caml_state).toNat + off) =
      word c ((word c Layout.sym_Caml_state).toNat + off) := fun off h => kept _ (by omega)
  refine g.transport_ids (fun l o' h => ⟨o', by rw [← heap]; exact h, rfl⟩) (fun id => by rw [chans]) domain
    (stat _ (by rw [show Layout.sym_caml_prim_table + Layout.off_prim_contents = 0x8006c0c0 from rfl,
      show Layout.sym_bss_end = 0x8007d138 from rfl]; omega))
    (by simp only [runtimeFields, domainWord]; rw [domain, field _ (by rw [show Layout.off_young_limit = 0 from rfl]; omega)])
    (by simp only [runtimeFields, domainWord]; rw [domain, field _ (by rw [show Layout.off_young_ptr = 8 from rfl]; omega)])
    (stat _ (by rw [show Layout.sym_caml_all_opened_channels = 0x80064b40 from rfl,
      show Layout.sym_bss_end = 0x8007d138 from rfl]; omega))
    (fun id ch a hc hp => by
      have ca := SG.channelArena id ch a hc hp
      rw [show chanOffBuff + OCaml.Bytecode.ioBufferSize = 65608 from rfl] at ca
      exact kept _ (by rw [show Gc.chanOffNext = 48 from rfl]; omega))
    (by rw [heap])

/-- A range below `heapEnd` misses a store at or above it. -/
theorem out_of_above {log : List WEntry} {A n : Nat} (above : ∀ e ∈ log, Vsa.Sim.DlHeap.heapEnd ≤ e.1)
    (h : A + n ≤ Vsa.Sim.DlHeap.heapEnd) : OutLRange log A n := by
  induction log with
  | nil => trivial
  | cons e log ih => exact ⟨.inl (Nat.le_trans h (above e (by simp))), ih fun e' he => above e' (by simp [he])⟩

theorem prim_caml_string_notequal_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    (nativeStable : ∀ lo, Vsa.Sim.DlHeap.heapEnd ≤ lo → WindowStable L.runtimeOk [⟨lo, lo + 8⟩]) :
    PrimReturnsAt L P op ra k "caml_string_notequal" := by
  intro s c0 pl cp sp high table entry value env index v heap world reach ready sem _words
  obtain ⟨y, args⟩ : ∃ y, s.accu :: s.stack.take k = [s.accu, y] ∧ y ∈ s.stack := by
    cases e : s.stack.take k with
    | nil => rw [e] at sem; simp [primF1Impl] at sem
    | cons y ys =>
      cases ys with
      | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
      | nil => exact ⟨y, rfl, List.mem_of_mem_take (by rw [e]; simp)⟩
  obtain ⟨args, ymem⟩ := args
  rw [args] at sem
  obtain ⟨bs, hx, bs', hy, rfl, rfl, rfl⟩ : ∃ bs, strOf? s.heap s.accu = some bs ∧ ∃ bs',
      strOf? s.heap y = some bs' ∧ v = Val.ofBool (bs != bs') ∧ heap = s.heap ∧ world = s.world := by
    cases ex : strOf? s.heap s.accu <;> cases ey : strOf? s.heap y <;>
      simp [primF1Impl, ex, ey] at sem
    obtain ⟨rfl, rfl, rfl⟩ := sem
    exact ⟨_, rfl, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨l, a, o, hxl, placed, ho, live, geom⟩ := string_arg ready (by simp [roots]) hx
  rw [hxl] at hx
  obtain ⟨l', a', o', rfl, placed', ho', live', geom'⟩ := string_arg ready (by simp [roots, ymem]) hy
  have hentry : entry = Layout.sym_caml_string_notequal :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_string_notequal)
  subst hentry
  have result : Val.ofBool (bs != bs') = .int (stringInequalityResult bs bs') := by
    unfold Val.ofBool stringInequalityResult; by_cases h : bs = bs' <;> simp [h]
  have model : primF1Impl "caml_string_notequal" [.ptr l 0, .ptr l' 0] s.heap s.world =
      .ok (.int (stringInequalityResult bs bs')) s.heap s.world := by
    simp [primF1Impl, hx, hy, ← result]
  rw [args, result, hxl]
  refine ⟨tag64 (stringInequalityResult bs bs'), by decide, model, fun c setup _ => ?_⟩
  obtain ⟨D, inv, valid⟩ := setup.native
  -- the saved-ra store sits just below the native stack pointer, above the arena
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have nl : 0x86800000 + 4096 ≤ D.nativeSp := by
    have := valid.headroom; rw [he, show nativeHeadroom = 4096 from rfl] at this; exact this
  have nhi : D.nativeSp < 2 ^ 64 := by have := valid.high; simp only [Layout.sym_stack_top] at this; omega
  have hn : (BitVec.ofNat 64 D.nativeSp).toNat = D.nativeSp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nhi]
  have n8 : (BitVec.ofNat 64 D.nativeSp - 8#64).toNat = D.nativeSp - 8 := by
    rw [ConsoleWrite.bv_sub_toNat (by rw [hn]; omega), hn]
  let F := savedRaLog (BitVec.ofNat 64 D.nativeSp) ra
  have above : ∀ e ∈ F, Vsa.Sim.DlHeap.heapEnd ≤ e.1 := by
    intro e he'; simp only [F, savedRaLog, List.mem_singleton] at he'; subst he'; dsimp only; rw [n8, he]; omega
  have g := setup.geometry.toArmGeometry.toStackGeometry
  have stk := setup.input.data.stack.1
  have fits := ready.stackFits
  have low : high - Layout.stackBytes ≤ sp := by
    rw [← stk]; rw [show Layout.stackBytes = 32768 from rfl] at fits ⊢; omega
  have win : WindowSeparated ⟨D.nativeSp - 8, D.nativeSp⟩ P s c pl cp high :=
    WindowSeparated.of_above g (by dsimp only; rw [he]; omega)
  have inside : LogInW [⟨D.nativeSp - 8, D.nativeSp⟩] F := by
    simp only [F, savedRaLog, LogInW, InsideW]; rw [n8]; exact ⟨.inl ⟨by omega, by omega⟩, trivial⟩
  have each : ∀ w ∈ [(⟨D.nativeSp - 8, D.nativeSp⟩ : W)], PayloadWindow P s c pl cp sp high w := by
    intro w hw; simp only [List.mem_singleton] at hw; subst hw; exact .separated win
  have objOut : ∀ {la : Nat} {lo : Nat} {ob : Obj} (b : List UInt8), pl.φ lo = some la → s.heap.get? lo = some ob →
      ob.wosize = (Obj.bytes b).wosize → ObjectOutside F la (.bytes b) := by
    intro la lo ob b hp hob hw
    have hl := g.heapLow lo la ob hp hob
    have ha := g.heapArena lo la ob hp hob
    rw [hw] at ha
    exact ⟨out_of_above above (by omega), out_of_above above (by omega)⟩
  have wsz : ∀ {lo : Nat} {ob : Obj} {b : List UInt8}, s.heap.get? lo = some ob →
      strOf? s.heap (.ptr lo 0) = some b → ob.wosize = (Obj.bytes b).wosize := by
    intro lo ob b hob hs
    cases ob with
    | bytes b0 => simp only [strOf?, hob, Option.some.injEq] at hs; subst hs; rfl
    | partialBytes b0 =>
      simp only [strOf?, hob] at hs
      have := mapM_id_length _ _ hs; simp only [Obj.wosize]; omega
    | _ => simp [strOf?, hob] at hs
  have stable := nativeStable (D.nativeSp - 8) (by rw [he]; omega)
  have S := caml_string_notequal_primitive (nativeSp := BitVec.ofNat 64 D.nativeSp)
    (by simp only [savedRaWindows]; rw [n8]; exact stable)
    { setup.input with
      placed := placed, placed' := placed', str := hx, str' := hy
      canonical := paddedString_of_objAt (setup.input.data.object_at live placed ho) ho hx
      canonical' := paddedString_of_objAt (setup.input.data.object_at live' placed' ho') ho' hy
      geometry := geom, geometry' := geom'
      nativeStack := inv.stack
      window := by
        have w := ConsoleWrite.frame_window (b := D.nativeSp) (s := BitVec.ofNat 64 D.nativeSp)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nhi]) (by omega)
          (by have := valid.high; simp only [Layout.sym_stack_top] at this; omega) (k := 0) (off := 8)
          (by omega) (by have := valid.aligned; omega)
        simpa using w
      imageOutside := ⟨out_of_above above (by decide), out_of_above above (by decide)⟩
      payloadOutside := PayloadOutside.of_windows g stk low inside each
      bindingsOutside := BindingsOutside.of_windows g (by omega) inside each
      leftOutside := objOut bs placed ho (wsz ho hx)
      rightOutside := objOut bs' placed' ho' (wsz ho' hy) }
  have SG0 := ready.geometry.toArmGeometry.toStackGeometry
  have dl := SG0.domainLow; have da := SG0.domainArena
  rw [show Layout.domainStateBytes = 928 from rfl] at da
  have dn : (word c0 Layout.sym_Caml_state).toNat < 2 ^ 64 := (word c0 Layout.sym_Caml_state).isLt
  have st := SG0.statics; have ar := SG0.arena
  refine ccall_writing_summary_below S (fun _ p => p.toPrimitivePost)
    (fun after p r hr => by
      simp only [callSavedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact p.call.frame _ (by decide) (by decide)
      · exact p.call.frame _ (by decide) (by decide)
      · exact p.call.frame _ (by decide) (by decide)
      · exact p.nativeStack.trans inv.stack.symm)
    (fun after m x hx => by rw [byte_total, byte_total, m, writeLog_out _ _ _ hx]) setup.saved ?_ ?_ ?_
    (Exists.intro D ⟨inv, valid⟩)
  · refine ⟨out_of_above above (by rw [show Layout.sym_Caml_state = 0x80064d08 from rfl]; omega), ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show Layout.off_extern_sp = 160 from rfl]
      simp only [domainAt]
      exact out_of_above above (by omega)
    · rw [BitVec.toNat_ofNat]
      exact out_of_above above (by rw [show Layout.stackBytes = 32768 from rfl] at st; omega)
    · simp only [domainAt]
      rw [BitVec.toNat_ofNat, show Layout.off_external_raise = 184 from rfl]
      exact out_of_above above (by omega)
  · intro n hn
    have e := Option.some.inj (hn.symm.trans inv.stack)
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt nhi] at this
    simp only [F, savedRaLog, LogInW, InsideW]; rw [n8]
    exact ⟨.inl ⟨by omega, by omega⟩, trivial⟩
  · intro after frame
    exact LoopGeometry.of_above setup.geometry rfl rfl fun x hx =>
      frame x (outL_of_range (out_of_above above (A := x) (n := 1) (by omega)) (by omega) (by omega))

end OCaml.Vm.Sim
