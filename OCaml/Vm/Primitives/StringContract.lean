import OCaml.Vm.Primitives.StringRead
import OCaml.Vm.Primitives.ImmediateContract

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- The byte length of a string-like object (initialized or not). -/
def _root_.OCaml.Bytecode.Obj.byteLength? : Obj → Option Nat
  | .bytes b => some b.length
  | .partialBytes b => some b.length
  | _ => none

theorem mapM_id_length : ∀ (cells : List (Option UInt8)) (bs : List UInt8),
    cells.mapM id = some bs → bs.length = cells.length
  | [], bs, h => by simp at h; subst h; rfl
  | x :: xs, bs, h => by
    cases x with
    | none => simp at h
    | some y =>
      cases e : xs.mapM id with
      | none => simp [e] at h
      | some ys => simp [e] at h; subst h; simp [mapM_id_length xs ys e]

/-- `caml_ml_string_length` / `caml_ml_bytes_length` on a string-like object. -/
theorem string_length_semantics {h : Heap} {w : World} {l n : Nat} {o : Obj} {name : String}
    (object : h.get? l = some o) (len : o.byteLength? = some n)
    (nameOk : name = "caml_ml_string_length" ∨ name = "caml_ml_bytes_length") :
    primF1Impl name [.ptr l 0] h w = .ok (Val.ofInt n) h w := by
  cases o with
  | bytes b =>
    simp only [Obj.byteLength?, Option.some.injEq] at len; subst len
    rcases nameOk with rfl | rfl <;> simp [primF1Impl, strOf?, object]
  | partialBytes cells =>
    simp only [Obj.byteLength?, Option.some.injEq] at len; subst len
    cases e : cells.mapM id with
    | some bs =>
      rcases nameOk with rfl | rfl <;> simp [primF1Impl, strOf?, object, e, mapM_id_length cells bs e]
    | none =>
      rcases nameOk with rfl | rfl <;> simp [primF1Impl, strOf?, byteCells?, object, e]
  | _ => simp [Obj.byteLength?] at len

/-- A successful string-length call reads a string-like object and changes nothing. -/
theorem string_length_inv {h h' : Heap} {w w' : World} {x v : Val} {name : String}
    (nameOk : name = "caml_ml_string_length" ∨ name = "caml_ml_bytes_length")
    (ok : primF1Impl name [x] h w = .ok v h' w') :
    ∃ l o n, x = .ptr l 0 ∧ h.get? l = some o ∧ o.byteLength? = some n ∧
      v = Val.ofInt n ∧ h' = h ∧ w' = w := by
  have go : primF1Impl name [x] h w = (match strOf? h x with
      | some b => PRes.ok (Val.ofInt b.length) h w
      | none => match byteCells? h x with
        | some b => PRes.ok (Val.ofInt b.length) h w
        | none => PRes.unsupported) := by
    rcases nameOk with rfl | rfl <;> simp only [primF1Impl] <;> split <;> rename_i hb <;> simp [hb] <;> cases byteCells? h x <;> rfl
  rw [go] at ok
  cases x with
  | ptr l k =>
    cases k with
    | succ k => simp [strOf?, byteCells?] at ok
    | zero =>
      cases e : h.get? l with
      | none => simp [strOf?, byteCells?, e] at ok
      | some o =>
        cases o with
        | bytes b =>
          simp only [strOf?, e] at ok
          injection ok with hv hh hw
          exact ⟨l, _, _, rfl, e, rfl, hv.symm, hh.symm, hw.symm⟩
        | partialBytes cells =>
          cases m : cells.mapM id with
          | some bs =>
            simp only [strOf?, e, m] at ok
            injection ok with hv hh hw
            refine ⟨l, _, _, rfl, e, rfl, ?_, hh.symm, hw.symm⟩
            rw [← hv, mapM_id_length cells bs m]
          | none =>
            simp only [strOf?, byteCells?, e, m] at ok
            injection ok with hv hh hw
            exact ⟨l, _, _, rfl, e, rfl, hv.symm, hh.symm, hw.symm⟩
        | _ => simp [strOf?, byteCells?, e] at ok
  | _ => simp [strOf?, byteCells?] at ok

/-- A represented string argument with the RAM geometry needed by its loads. -/
structure StringInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (l : Nat) (o : Obj) (n : Nat) (a : Nat) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high ra [.ptr l 0] c where
  accu : s.accu = .ptr l 0
  placed : pl.φ l = some a
  heapObject : s.heap.get? l = some o
  length : o.byteLength? = some n
  geometry : StringGeometry a n

structure StringShape (c : Config) (a : Nat) (n : Nat) : Prop where
  headerSize : (word c (a - 8)).toNat / 1024 = (n + 8) / 8
  padding : (byte c (a + 8 * ((n + 8) / 8) - 1)).toNat =
    8 * ((n + 8) / 8) - 1 - n

theorem StringInput.shape {runtimeOk P s pl cp sp high ra l o n a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l o n a c) : StringShape c a n := by
  have live : Live s.heap (roots P s) l := Live.root (v := .ptr l 0) (by simp [roots, h.accu]) rfl
  have layout := h.data.object_at live h.placed h.heapObject
  have len := h.length
  cases o with
  | bytes b =>
    simp only [Obj.byteLength?, Option.some.injEq] at len; subst len
    obtain ⟨header, _, padding⟩ := layout
    have hw : (Obj.bytes b).wosize = (b.length + 8) / 8 := by simp only [Obj.wosize]; omega
    exact ⟨by simpa only [hw] using header.2, by simpa only [hw] using padding⟩
  | partialBytes b =>
    simp only [Obj.byteLength?, Option.some.injEq] at len; subst len
    obtain ⟨header, _, padding⟩ := layout
    have hw : (Obj.partialBytes b).wosize = (b.length + 8) / 8 := by simp only [Obj.wosize]; omega
    exact ⟨by simpa only [hw] using header.2, by simpa only [hw] using padding⟩
  | _ => simp [Obj.byteLength?] at len

theorem StringInput.header {runtimeOk P s pl cp sp high ra l o n a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l o n a c) :
    stringHeader c (BitVec.ofNat 64 a) = word c (a - 8) := by
  unfold stringHeader
  rw [string_header_address h.geometry]

theorem StringInput.padding {runtimeOk P s pl cp sp high ra l o n a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l o n a c) :
    stringPadding c (BitVec.ofNat 64 a) = byte c (a + 8 * ((n + 8) / 8) - 1) := by
  unfold stringPadding
  rw [h.header, string_padding_address h.geometry h.shape.headerSize]

theorem StringInput.result {runtimeOk P s pl cp sp high ra l o n a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l o n a c) :
    stringLengthWord (stringHeader c (BitVec.ofNat 64 a)) (stringPadding c (BitVec.ofNat 64 a)) =
      tag64 (BitVec.ofNat 63 n) := by
  rw [h.header, h.padding]
  exact stringLengthWord_tag _ _ _ h.shape.headerSize h.shape.padding

theorem string_length_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P s pl cp sp high ra l o n a c} {entry : BitVec 64} {name : String}
    (h : StringInput runtimeOk P s pl cp sp high ra l o n a c)
    (S : FnSummary entry (fun x => x = c) (RegisterPost [10, 14, 15] c ra
      (stringLengthWord (stringHeader c (BitVec.ofNat 64 a)) (stringPadding c (BitVec.ofNat 64 a)))))
    (nameOk : name = "caml_ml_string_length" ∨ name = "caml_ml_bytes_length") :
    FnSummary entry (fun x => x = c)
      (ImmediatePost runtimeOk P s pl cp sp high name [.ptr l 0]
        (BitVec.ofNat 63 n) [10, 14, 15] c ra) := by
  rw [h.result] at S
  apply immediate_contract stable h.toImmediateInput S
  · simp [PreservesLoopRegisters, Layout.reg_dispatchTable, Layout.reg_opcodeBound,
      Layout.reg_pending, Layout.reg_domain, gprReg]
  · rw [string_length_semantics h.heapObject h.length nameOk]; rfl

end OCaml.Vm.Primitives
