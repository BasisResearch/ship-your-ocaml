import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Primitives.CamlMlStringLength
import OCaml.Vm.Primitives.CamlMlBytesLength

/-! `caml_ml_string_length` and `caml_ml_bytes_length` at every `C_CALL`
site: the represented read-only summary, from the call-site contract and the
heap geometry of the string. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **A length primitive returns at every `C_CALL` site.** -/
theorem prim_length_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    {name : String} {sym : Nat}
    (nameOk : name = "caml_ml_string_length" ∨ name = "caml_ml_bytes_length")
    (lookup : PrimitiveEntries.lookup name = some sym)
    (prim : ∀ {P s pl cp sp high ra l o n a c},
      StringInput L.runtimeOk P s pl cp sp high ra l o n a c →
      FnSummary (BitVec.ofNat 64 sym) (fun x => x = c)
        (OCaml.Vm.Primitives.ImmediatePost L.runtimeOk P s pl cp sp high name [.ptr l 0] (BitVec.ofNat 63 n) [10, 14, 15] c ra)) :
    PrimReturnsAt L P op ra k name := by
  intro s c pl cp sp high table entry value env index v heap world reach ready sem
  have one : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons y ys =>
      rw [e] at sem
      rcases nameOk with rfl | rfl <;> cases ys <;> simp [primF1Impl] at sem
  rw [one] at sem ⊢
  obtain ⟨l, o, n, hx, ho, hn, rfl, rfl, rfl⟩ := string_length_inv nameOk sem
  have hentry : entry = sym := Option.some.inj (ready.entryName.symm.trans lookup)
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
  have model : primF1Impl name [s.accu] s.heap s.world =
      .ok (.int (BitVec.ofNat 63 n)) s.heap s.world := by
    rw [hx, string_length_semantics ho hn nameOk, ofInt]
  apply ccall_callee_of_readOnly (writes := [10, 14, 15]) (by rcases nameOk with rfl | rfl <;> decide) model
    (by decide)
  intro c' input
  rw [hx] at input ⊢
  exact prim
    { input with accu := hx, placed := placed, heapObject := ho, length := hn, geometry := geom }

theorem prim_caml_ml_string_length_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_ml_string_length" :=
  prim_length_returns (Or.inl rfl) PrimitiveEntries.entry_caml_ml_string_length
    (caml_ml_string_length_primitive stable)

theorem prim_caml_ml_bytes_length_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_ml_bytes_length" :=
  prim_length_returns (Or.inr rfl) PrimitiveEntries.entry_caml_ml_bytes_length
    (caml_ml_bytes_length_primitive stable)

end OCaml.Vm.Sim
