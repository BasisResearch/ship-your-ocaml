import OCaml.Vm.Primitives.StringRead
import OCaml.Vm.Primitives.ImmediateContract

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- A represented string argument with the RAM geometry needed by its loads. -/
structure StringInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (l : Nat) (b : List UInt8) (a : Nat) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high ra [.ptr l 0] c where
  accu : s.accu = .ptr l 0
  placed : pl.φ l = some a
  heapObject : s.heap.get? l = some (.bytes b)
  geometry : StringGeometry a b.length

structure StringShape (c : Config) (a : Nat) (b : List UInt8) : Prop where
  headerSize : (word c (a - 8)).toNat / 1024 = (b.length + 8) / 8
  padding : (byte c (a + 8 * ((b.length + 8) / 8) - 1)).toNat =
    8 * ((b.length + 8) / 8) - 1 - b.length

theorem StringInput.shape {runtimeOk P s pl cp sp high ra l b a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l b a c) : StringShape c a b := by
  have live : Live s.heap (roots P s) l := Live.root (v := .ptr l 0) (by simp [roots, h.accu]) rfl
  have layout := h.data.object_at live h.placed h.heapObject
  obtain ⟨header, _, padding⟩ := layout
  have hw : (Obj.bytes b).wosize = (b.length + 8) / 8 := by
    simp only [Obj.wosize]
    omega
  constructor
  · simpa only [hw] using header.2
  · simpa only [hw] using padding

theorem StringInput.header {runtimeOk P s pl cp sp high ra l b a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l b a c) :
    stringHeader c (BitVec.ofNat 64 a) = word c (a - 8) := by
  unfold stringHeader
  rw [string_header_address h.geometry]

theorem StringInput.padding {runtimeOk P s pl cp sp high ra l b a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l b a c) :
    stringPadding c (BitVec.ofNat 64 a) = byte c (a + 8 * ((b.length + 8) / 8) - 1) := by
  unfold stringPadding
  rw [h.header, string_padding_address h.geometry h.shape.headerSize]

theorem StringInput.result {runtimeOk P s pl cp sp high ra l b a c}
    (h : StringInput runtimeOk P s pl cp sp high ra l b a c) :
    stringLengthWord (stringHeader c (BitVec.ofNat 64 a)) (stringPadding c (BitVec.ofNat 64 a)) =
      tag64 (BitVec.ofNat 63 b.length) := by
  rw [h.header, h.padding]
  exact stringLengthWord_tag _ _ _ h.shape.headerSize h.shape.padding

theorem string_length_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P s pl cp sp high ra l b a c} {entry : BitVec 64} {name : String}
    (h : StringInput runtimeOk P s pl cp sp high ra l b a c)
    (S : FnSummary entry (fun x => x = c) (RegisterPost [10, 14, 15] c ra
      (stringLengthWord (stringHeader c (BitVec.ofNat 64 a)) (stringPadding c (BitVec.ofNat 64 a)))))
    (nameOk : name = "caml_ml_string_length" ∨ name = "caml_ml_bytes_length") :
    FnSummary entry (fun x => x = c)
      (ImmediatePost runtimeOk P s pl cp sp high name [.ptr l 0]
        (BitVec.ofNat 63 b.length) [10, 14, 15] c ra) := by
  rw [h.result] at S
  apply immediate_contract stable h.toImmediateInput S
  · simp [PreservesLoopRegisters, Layout.reg_dispatchTable, Layout.reg_opcodeBound,
      Layout.reg_pending, Layout.reg_domain, gprReg]
  · rcases nameOk with rfl | rfl <;>
      simp [primF1Impl, strOf?, h.heapObject, Val.ofInt]

end OCaml.Vm.Primitives
