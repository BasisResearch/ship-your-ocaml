import OCaml.Vm.Primitives.Int64FloatTail
import OCaml.Vm.Primitives.DoubleLayout

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim
open DoubleAllocation

/-- The C primitive loads the int64 payload and tail-calls the proved nursery
allocator. The allocation-room premise is the G1 budget supplier's duty. -/
theorem int64_float_machine (c : Config) (ra arg bits domain young limit : BitVec 64)
    (h : LeafInput ra c) (ha : gpr c 10 = some arg)
    (window : ReadWindow (arg + 8#64) 8) (value : word c (arg + 8#64).toNat = bits)
    (memory : FastMemory bits domain young limit c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_int64_float_of_bits) (fun d => d = c)
      (WritePost doubleWrites (allocationLog domain young bits) c ra (young - 16#64 + 8#64)) := by
  have S := Int64FloatTail.summary c ra arg (read8 c.σ.mem (arg + 8#64).toNat)
    h ha window (read8_pins _ _)
  have loaded : bytesVal .ld (read8 c.σ.mem (arg + 8#64).toNat) = bits :=
    (read8_value _ _).trans value
  rw [loaded] at S
  let pre := BoundaryPost [10] c ra (BitVec.ofNat 64 Layout.sym_caml_copy_double)
    [(10, bits), (1, ra)]
  have callee : FnSummary (BitVec.ofNat 64 Layout.sym_caml_copy_double) pre
      (WritePost doubleWrites (allocationLog domain young bits) c ra (young - 16#64 + 8#64)) := by
    constructor
    rintro d ⟨pc, p⟩
    have call := copy_double_fast d ra bits domain young limit
      ⟨p.toLeafInput, memory.frame p.memory, gholds_lookup _ p.regs rfl⟩
    have packed := call.weaken (fun _ h => h) (Post' := WritePost doubleWrites
        (allocationLog domain young bits) c ra (young - 16#64 + 8#64)) (by
      intro after post
      exact (p.then_write post).widen (by decide))
    exact packed.run d ⟨pc, rfl⟩
  exact FnSummary.tailJump S.run callee (fun _ p => ⟨p.pc, p⟩)

/-- G1 int64-to-double input: represented boxed argument, fresh reserved result
placement, and sufficient nursery room. Native integer registers carry bits;
the ELF has no floating-point instruction on this path. -/
structure Int64FloatInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (l a : Nat) (bits domain young limit : BitVec 64) (c : Config) : Prop
    extends AllocationInput runtimeOk P s pl cp sp high ra [.ptr l 0] (.double bits)
      ((young - 16#64).toNat + 8) (allocationLog domain young bits) c where
  accu : s.accu = .ptr l 0
  argumentPlace : pl.φ l = some a
  argumentObject : s.heap.get? l = some (.int64 bits)
  argumentBound : a + 16 ≤ 0x100000000
  argumentRead : ReadWindow (BitVec.ofNat 64 (a + 8)) 8
  nursery : FastMemory bits domain young limit c

theorem int64_float_contract {runtimeOk P s pl cp sp high ra l a bits domain young limit c}
    (h : Int64FloatInput runtimeOk P s pl cp sp high ra l a bits domain young limit c)
    (runtime : AllocationRuntime runtimeOk c (allocationLog domain young bits)) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_int64_float_of_bits) (fun d => d = c)
      (PrimitivePost runtimeOk P s pl cp sp high "caml_int64_float_of_bits" [.ptr l 0]
        (.ptr (s.heap.alloc (.double bits)).2 0) (BitVec.ofNat 64 ((young - 16#64).toNat + 8))
        (s.heap.alloc (.double bits)).1 s.world doubleWrites
        (writeLog c.σ.mem (allocationLog domain young bits)) c ra) := by
  have live : Live s.heap (roots P s) l := Live.root (v := .ptr l 0) (by simp [roots, h.accu]) rfl
  have object := h.data.object_at live h.argumentPlace h.argumentObject
  have addr : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
    rw [BitVec.ofNat_add]
  have address : (BitVec.ofNat 64 a + 8#64).toNat = a + 8 := by
    rw [addr, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have bound := h.argumentBound
    omega
  have S := int64_float_machine c ra (BitVec.ofNat 64 a) bits domain young limit h.toLeafInput
    (h.arguments.get (i := 0) rfl (by simp [valWord, h.argumentPlace]))
    (by rw [addr]; exact h.argumentRead) (by rw [address]; exact object.2.2) h.nursery
  have result : young - 16#64 + 8#64 = BitVec.ofNat 64 ((young - 16#64).toNat + 8) := by
    simp only [← field_address h.nursery.headerWrite, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [result] at S
  apply allocation_contract h.toAllocationInput S
  · intro after hm
    exact double_layout h.nursery.headerWrite hm
  · exact runtime
  · simp [PreservesLoopRegisters, doubleWrites, Layout.reg_dispatchTable, Layout.reg_opcodeBound,
      Layout.reg_pending, Layout.reg_domain, gprReg]
  · simp [primF1Impl, h.argumentObject]

end OCaml.Vm.Primitives
