import OCaml.Vm.Sim.ImmediateRows
import OCaml.Vm.Sim.AccRows
import OCaml.Vm.Sim.Offsetref
import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Sim.StackRows

/-!
# Unconditional rows: in-place heap updates

OFFSETREF adds to an integer field of the accumulator's block. The
semantic inversion and the represented field (block, placement, selected
integer, room above `.bss`) come from the step and the loop-head witness.
The field write's framing is `FieldWriteReady`, discharged for the F1 layout
by `f1_fieldWriteReady` (`FieldWriteOk.of_geometry` from the arm geometry,
the object window from `Gc.f1_objectField`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **Field-write readiness** (named obligation, a1-arms' invariant): one-word
writes to a field of a placed block are runtime-stable and miss the rest of
the represented payload. -/
structure FieldWriteReady (L : OCaml.Layout) (P : Prog) (s : St) (c : Config) : Prop where
  ready : ∀ (pl : Place) (cp : ChanPlace) (sp high l a k tag : Nat) (fields : List Val)
    (w : BitVec 64), VmReprAt P s c pl cp sp high → OCaml.LoopGeometry L P s c pl cp high →
    pl.φ l = some a → s.heap.get? l = some (.block tag fields) → k < fields.length →
    WindowStable L.runtimeOk [⟨a + 8 * k, a + 8 * k + 8⟩] ∧ FieldWriteOk P s c pl cp sp a k w

/-- A field write misses everything below `.bss`'s end. -/
theorem field_static {a k A n : Nat} {w : BitVec 64} (low : Layout.sym_bss_end + 8 ≤ a)
    (static : A + n ≤ Layout.sym_bss_end) : OutLRange (fieldLog a k w) A n := by
  simp only [fieldLog, OutLRange, and_true]; omega

/-- A field write misses a window its whole object is apart from. -/
theorem field_apart {a k wo lo hi A n : Nat} {w : BitVec 64} (bound : k < wo) (room : 8 ≤ a)
    (apart : OutWRange [⟨lo, hi⟩] (a - 8) (8 * wo + 8)) (low : lo ≤ A) (high : A + n ≤ hi) :
    OutLRange (fieldLog a k w) A n := by
  simp only [OutWRange, and_true] at apart
  simp only [fieldLog, OutLRange, and_true]; omega

/-- **A field of a placed block is writable and misses the rest of the
represented payload**, from the arm geometry and the stack budget. -/
theorem FieldWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a k tag : Nat} {fields : List Val} {w : BitVec 64}
    (g : ArmGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (placed : pl.φ l = some a) (object : s.heap.get? l = some (.block tag fields))
    (bound : k < fields.length) : FieldWriteOk P s c pl cp sp a k w := by
  have low := g.heapLow l a _ placed object
  have arena := g.heapArena l a _ placed object
  have aligned := g.words.heap l a placed
  have size : (Obj.block tag fields).wosize = fields.length := rfl
  rw [size] at arena
  have facts : Image.textBase + Image.textSize ≤ Layout.sym_bss_end ∧
      Image.rodataBase + Image.rodataSize ≤ Layout.sym_bss_end ∧
      Layout.sym_Caml_state + 8 ≤ Layout.sym_bss_end ∧ Layout.sym_caml_start_code + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_atom_table + 8 ≤ Layout.sym_bss_end ∧ Layout.sym_caml_global_data + 8 ≤ Layout.sym_bss_end ∧
      Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Layout.sym_bss_end ∧
      Layout.off_stack_high + 8 ≤ Layout.domainStateBytes ∧ Layout.off_trapsp + 8 ≤ Layout.domainStateBytes ∧
      0x80000000 ≤ Layout.sym_bss_end ∧ Layout.sym_tohost + 16 ≤ Layout.sym_bss_end ∧
      Vsa.Sim.DlHeap.heapEnd ≤ 0x100000000 := by decide
  obtain ⟨fText, fRo, fDom, fCode, fAtom, fGlob, fPrim, fHigh, fTrap, fRam, fTohost, fEnd⟩ := facts
  have room : 8 ≤ a := by omega
  have domain := g.nursery.heapDomain l a _ placed object
  rw [size] at domain
  have inDomain : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      OutLRange (fieldLog a k w) ((word c Layout.sym_Caml_state).toNat + off) 8 :=
    fun off fits => field_apart bound room domain (by omega) (by omega)
  have stackLow := stack_space stack space
  have hn : (BitVec.ofNat 64 (a + 8 * k)).toNat = a + 8 * k := Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_⟩, ⟨⟨field_static low fDom, inDomain _ fHigh, field_static low fCode,
    field_static low fAtom, field_static low fGlob, ?_, ?_⟩, inDomain _ fTrap, ?_⟩,
    ⟨field_static low fText, field_static low fRo⟩, ⟨?_, ?_⟩,
    ⟨field_static low fPrim, ?_⟩⟩
  · rw [hn]; omega
  · rw [hn]; omega
  · rw [hn]; omega
  · rw [hn]; omega
  · intro i v fetch
    have hi := (Array.getElem?_eq_some_iff.mp fetch).1
    have code := g.heapCode l a _ placed object
    rw [size] at code
    exact field_apart bound room code (by omega) (by omega)
  · intro id ch b found at_
    have chan := g.heapChannels l a _ placed object id ch b found at_
    rw [size] at chan
    exact field_apart bound room chan (by omega) (by omega)
  · intro i v found
    have hi := (List.getElem?_eq_some_iff.mp found).1
    have apart := g.heap l a _ placed object
    rw [size] at apart
    simp only [stackWindow] at apart
    have top := stack.1
    exact field_apart bound room apart (by omega) (by omega)
  · exact inDomain _ (young_field_offsets _ (by simp)).1
  · exact inDomain _ (young_field_offsets _ (by simp)).1
  · intro i name found
    have prim := g.heapPrims l a _ placed object i name found
    rw [size] at prim
    exact field_apart bound room prim (by omega) (by omega)

/-- **`FieldWriteReady` for the F1 layout**: the field window is stable under
`f1Runtime` (`Gc.f1_objectField`), and the write facts are
`FieldWriteOk.of_geometry`, given the stack budget. -/
theorem f1_fieldWriteReady {P : Prog} {s : St} {c : Config} (ok : Gc.f1Runtime c)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) : FieldWriteReady Gc.f1Layout P s c where
  ready pl cp sp high l a k tag fields w repr g placed object bound := by
    have g' := g.toArmGeometry
    have low := g'.heapLow l a _ placed object
    refine ⟨Gc.f1_objectField g'.nursery ok placed object low (by omega) ?_,
      FieldWriteOk.of_geometry g' repr.stack space placed object bound⟩
    show a + 8 * k + 8 ≤ a + 8 * fields.length
    omega

/-- A selected field 0 of a value: the value is a pointer into a block. -/
theorem field_zero {h : Heap} {v x : Val} (sel : field? h v 0 = some x) :
    ∃ l k tag fields, v = .ptr l k ∧ h.get? l = some (.block tag fields) ∧ fields[k]? = some x := by
  cases v with
  | ptr l k =>
    simp only [field?] at sel
    split at sel
    · rename_i tag fields found
      exact ⟨l, k, tag, fields, rfl, found, by simpa using sel⟩
    · cases sel
  | int | code | atom | raw => simp [field?] at sel

/-- **OFFSETREF from the loop head.** -/
theorem offsetref_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .OFFSETREF)
    (fetch : P.code[s.pc + 1]? = some w) (field : FieldWriteReady L P s c)
    (step : stepI P s ⟨.OFFSETREF, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, sel, rest⟩ := opt_next step
  obtain ⟨l, k, tag, fields, pointer, object, selected⟩ := field_zero sel
  cases v with
  | int n =>
    obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
    obtain ⟨x, -, word⟩ := input.accu
    rw [pointer] at word
    simp only [valWord, Option.map_eq_some_iff] at word
    obtain ⟨a, placed, -⟩ := word
    have low := input.geometry.heapLow l a _ placed object
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    obtain ⟨stable, space⟩ := field.ready pl cp sp high l a k tag fields
      (tag64 n + offsetintOperand w) input.toVmReprAt input.geometry placed object bound
    obtain ⟨c', run, running⟩ := offsetref_step_arm stable input
      (OperandAt.of_fetch input.geometry.toArmGeometry fetch) pointer placed object selected (by omega) space step
    exact ⟨c', run, h.of_plus run running⟩
  | ptr | code | atom | raw => cases rest

end OCaml.Vm.Sim
