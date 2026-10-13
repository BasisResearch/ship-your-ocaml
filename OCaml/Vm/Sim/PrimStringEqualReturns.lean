import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Primitives.CamlStringEqual

/-! `caml_string_equal` at every `C_CALL` site: two placed strings, their
canonical (zero-padded) layout from `ObjAt`, the read-only word comparison. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **A represented string is canonically padded**: its model contents (an
initialized `.bytes` or `.partialBytes` block) lie in a `PaddedString`. -/
theorem paddedString_of_objAt {c : Config} {pl : Place} {cp : ChanPlace} {a l : Nat} {o : Obj} {h : Heap}
    {bs : List UInt8} (layout : ObjAt c pl cp a o) (obj : h.get? l = some o)
    (str : strOf? h (.ptr l 0) = some bs) : PaddedString c a bs := by
  cases o with
  | bytes b =>
    simp only [strOf?, obj, Option.some.injEq] at str
    subst str
    obtain ⟨header, data, pad, zero⟩ := layout
    have hw : (Obj.bytes b).wosize = (b.length + 8) / 8 := by simp only [Obj.wosize]; omega
    exact ⟨⟨by simpa only [hw] using header.2, by simpa only [hw] using pad⟩, data,
      by simpa only [hw] using zero⟩
  | partialBytes b =>
    simp only [strOf?, obj] at str
    obtain ⟨header, data, pad, zero⟩ := layout
    have len := mapM_id_length _ _ str
    have hw : (Obj.partialBytes b).wosize = (bs.length + 8) / 8 := by simp only [Obj.wosize]; omega
    refine ⟨⟨by simpa only [hw] using header.2, by simpa only [hw, len] using pad⟩,
      fun i x hx => data i (some x) (mapM_id_get _ _ str i x hx) x rfl, ?_⟩
    intro i lo hi
    exact zero i (by omega) (by rw [hw]; omega)
  | _ => simp [strOf?, obj] at str

/-- The string a placed, live argument points to, with its address and
geometry at the call. -/
theorem string_arg {L : OCaml.Layout} {P : Prog} {op : Opcode} {s : St} {c : Config} {pl : Place}
    {cp : ChanPlace} {sp high table entry : Nat} {value env : BitVec 64} {index : BitVec 32} {name : String}
    {x : Val} {bs : List UInt8}
    (ready : CcallReady op L P s c pl cp sp high (domainAt c) table entry value env index name)
    (root : x ∈ roots P s) (str : strOf? s.heap x = some bs) :
    ∃ l a o, x = .ptr l 0 ∧ pl.φ l = some a ∧ s.heap.get? l = some o ∧ Live s.heap (roots P s) l ∧
      StringGeometry a bs.length := by
  match x, str with
  | .ptr l 0, str =>
    obtain ⟨o, ho⟩ : ∃ o, s.heap.get? l = some o := by
      cases e : s.heap.get? l with
      | none => simp [strOf?, e] at str
      | some o => exact ⟨o, rfl⟩
    have live : Live s.heap (roots P s) l := Live.root root rfl
    obtain ⟨a, o', placed, obj', -⟩ := ready.heap.1 l live
    have oo : o' = o := Option.some.inj (obj'.symm.trans ho)
    subst oo
    have g := ready.geometry
    have low := g.heapLow l a o' placed ho
    have up := g.heapArena l a o' placed ho
    have wos : o'.wosize = (bs.length + 8) / 8 := by
      cases o' with
      | bytes b => simp only [strOf?, ho, Option.some.injEq] at str; subst str; simp only [Obj.wosize]; omega
      | partialBytes b =>
        simp only [strOf?, ho] at str
        have := mapM_id_length _ _ str; simp only [Obj.wosize]; omega
      | _ => simp [strOf?, ho] at str
    have t1 : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
    have t2 : 0x80000000 ≤ Layout.sym_tohost := by decide
    have he : Vsa.Sim.DlHeap.heapEnd ≤ 0x100000000 := by decide
    exact ⟨l, a, o', rfl, placed, ho, live, ⟨by omega, by rw [wos] at up; omega, Or.inr (by omega)⟩⟩
  | .ptr _ (_ + 1), str => simp [strOf?] at str
  | .int _, str | .code _, str | .atom _, str | .raw _, str => simp [strOf?] at str

theorem prim_caml_string_equal_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_string_equal" := by
  intro s c0 pl cp sp high table entry value env index v heap world reach ready sem
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
      strOf? s.heap y = some bs' ∧ v = Val.ofBool (bs == bs') ∧ heap = s.heap ∧ world = s.world := by
    cases ex : strOf? s.heap s.accu <;> cases ey : strOf? s.heap y <;>
      simp [primF1Impl, ex, ey] at sem
    obtain ⟨rfl, rfl, rfl⟩ := sem
    exact ⟨_, rfl, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨l, a, o, hxl, placed, ho, live, geom⟩ := string_arg ready (by simp [roots]) hx
  rw [hxl] at hx
  obtain ⟨l', a', o', rfl, placed', ho', live', geom'⟩ :=
    string_arg ready (by simp [roots, ymem]) hy
  have hentry : entry = Layout.sym_caml_string_equal :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_string_equal)
  subst hentry
  have result : Val.ofBool (bs == bs') = .int (stringEqualityResult bs bs') := by
    unfold Val.ofBool stringEqualityResult; split <;> rfl
  have model : primF1Impl "caml_string_equal" [.ptr l 0, .ptr l' 0] s.heap s.world =
      .ok (.int (stringEqualityResult bs bs')) s.heap s.world := by
    simp [primF1Impl, hx, hy, ← result]
  rw [args, result, hxl]
  exact ⟨_, ccall_callee_of_readOnly (writes := StringScan.scanWrites) (by decide) model (by decide)
    fun c input => caml_string_equal_primitive stable
      { input with
        placed := placed, placed' := placed', str := hx, str' := hy
        canonical := paddedString_of_objAt (input.data.object_at live placed ho) ho hx
        canonical' := paddedString_of_objAt (input.data.object_at live' placed' ho') ho' hy
        geometry := geom, geometry' := geom' }⟩

end OCaml.Vm.Sim
