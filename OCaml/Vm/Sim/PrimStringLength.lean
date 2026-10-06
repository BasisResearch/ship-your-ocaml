import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Primitives.CamlMlStringLength

/-! `caml_ml_string_length` at a `C_CALL1` site: its represented read-only
summary, from the call-site contract and the heap geometry of the string. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

theorem prim_caml_ml_string_length_returns {L : OCaml.Layout} {P : Prog} {ra : BitVec 64}
    (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P .C_CALL1 ra 0 "caml_ml_string_length" := by
  intro s c pl cp sp high table entry value env index v heap world reach ready sem
  simp only [List.take_zero] at sem ⊢
  obtain ⟨l, o, n, hx, ho, hn, rfl, rfl, rfl⟩ := string_length_inv (Or.inl rfl) sem
  have hentry : entry = Layout.sym_caml_ml_string_length := by
    exact Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_ml_string_length)
  subst hentry
  have live : Live s.heap (roots P s) l := Live.root (v := .ptr l 0) (by simp [roots, hx]) rfl
  obtain ⟨a, o', placed, obj', -⟩ := ready.heap.1 l live
  have oo : o' = o := Option.some.inj (obj'.symm.trans ho)
  subst oo
  have g := ready.geometry
  have low := g.heapLow l a o' placed ho
  have up := g.heapArena l a o' placed ho
  have wos : o'.wosize = (n + 8) / 8 := by
    cases o' <;> simp_all [Obj.byteLength?, Obj.wosize] <;> omega
  have t1 : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have t2 : 0x80000000 ≤ Layout.sym_tohost := by decide
  have he : Vsa.Sim.DlHeap.heapEnd ≤ 0x100000000 := by decide
  have geom : StringGeometry a n := ⟨by omega, by rw [wos] at up; omega, Or.inr (by omega)⟩
  have ofInt : Val.ofInt (n : Int) = .int (BitVec.ofNat 63 n) := by simp [Val.ofInt]
  rw [ofInt]
  refine ⟨tag64 (BitVec.ofNat 63 n), ?_⟩
  have model : primF1Impl "caml_ml_string_length" [s.accu] s.heap s.world =
      .ok (.int (BitVec.ofNat 63 n)) s.heap s.world := by
    rw [hx, string_length_semantics ho hn (Or.inl rfl), ofInt]
  apply ccall_callee_of_readOnly (writes := [10, 14, 15]) (by decide) model (by decide)
  intro c' input
  rw [hx] at input ⊢
  exact caml_ml_string_length_primitive stable
    { input with accu := hx, placed := placed, heapObject := ho, length := hn, geometry := geom }

end OCaml.Vm.Sim
