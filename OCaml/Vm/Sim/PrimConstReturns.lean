import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Primitives.CamlSysConstNakedPointersChecked
import OCaml.Vm.Primitives.CamlSysConstBigEndian
import OCaml.Vm.Primitives.CamlSysConstWordSize
import OCaml.Vm.Primitives.CamlSysConstIntSize
import OCaml.Vm.Primitives.CamlSysConstMaxWosize
import OCaml.Vm.Primitives.CamlSysConstOstypeUnix
import OCaml.Vm.Primitives.CamlSysConstOstypeWin32
import OCaml.Vm.Primitives.CamlSysConstOstypeCygwin
import OCaml.Vm.Primitives.CamlSysConstBackendType

/-! The constant primitives (`caml_sys_const_*`) at every `C_CALL` site: one
leaf function writing `a0`, a model that ignores its unit argument. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A leaf function's post is a register post writing only `a0`. -/
theorem _root_.OCaml.Vm.Primitives.LeafPost.toRegisterPost {c d : Config} {ra v : BitVec 64} (p : LeafPost c ra v d) :
    RegisterPost [10] c ra v d :=
  ⟨p.good, p.image, p.minstret, p.tick, p.pc, p.result, p.memory, p.output,
    fun r hr hq => p.frame r (fun e => hr 10 (by simp) (by rw [e]; rfl)) hq, p.kept⟩

/-- **A constant primitive returns at every `C_CALL` site**: its model is
defined on one argument only, with a fixed `int` result, and its machine
function is a leaf writing that result's word. -/
theorem prim_constant_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    {name : String} {entry0 : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk) (fragment : name ∈ primsF1)
    (lookup : PrimitiveEntries.lookup name = some entry0)
    (shape : ∀ args h w v h' w', primF1Impl name args h w = .ok v h' w' →
      (∃ x, args = [x]) ∧ v = .int n ∧ h' = h ∧ w' = w)
    (summary : ∀ c ra', LeafInput ra' c →
      FnSummary (BitVec.ofNat 64 entry0) (fun x => x = c) (LeafPost c ra' (tag64 n))) :
    PrimReturnsAt L P op ra k name := by
  intro s c0 pl cp sp high table entry value env index v heap world reach ready sem
  obtain ⟨-, rfl, rfl, rfl⟩ := shape _ _ _ _ _ _ sem
  have hentry : entry = entry0 := Option.some.inj (ready.entryName.symm.trans lookup)
  subst hentry
  exact ⟨tag64 n, ccall_callee_of_readOnly (writes := [10]) fragment sem (by decide) fun c input =>
    readOnly_contract stable input ((summary c ra input.toLeafInput).weaken (fun _ h => h)
      fun _ p => p.toRegisterPost)
      (by simp [PreservesLoopRegisters, Layout.reg_dispatchTable, Layout.reg_opcodeBound,
        Layout.reg_pending, Layout.reg_domain, gprReg])
      (fun l h => by simp [Val.loc?] at h) rfl sem⟩

/-- A constant primitive's model: one argument, a fixed `int`, heap and world kept. -/
macro "const_shape" : tactic => `(tactic| (
  intro args h w v h' w' e
  match args, e with
  | [x], e =>
    simp [primF1Impl, Val.ofInt, Val.ofBool] at e
    obtain ⟨e1, e2, e3⟩ := e
    subst e1 e2 e3
    exact ⟨⟨x, rfl⟩, rfl, rfl, rfl⟩
  | [], e => simp [primF1Impl] at e
  | _ :: _ :: _, e => simp [primF1Impl] at e))

theorem prim_caml_sys_const_naked_pointers_checked_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_naked_pointers_checked" :=
  prim_constant_returns (n := 0#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_naked_pointers_checked
    (by const_shape) caml_sys_const_naked_pointers_checked_summary

theorem prim_caml_sys_const_big_endian_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_big_endian" :=
  prim_constant_returns (n := 0#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_big_endian
    (by const_shape) caml_sys_const_big_endian_summary

theorem prim_caml_sys_const_word_size_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_word_size" :=
  prim_constant_returns (n := 64#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_word_size
    (by const_shape) caml_sys_const_word_size_summary

theorem prim_caml_sys_const_int_size_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_int_size" :=
  prim_constant_returns (n := 63#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_int_size
    (by const_shape) caml_sys_const_int_size_summary

theorem prim_caml_sys_const_max_wosize_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_max_wosize" :=
  prim_constant_returns (n := 18014398509481983#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_max_wosize
    (by const_shape) caml_sys_const_max_wosize_summary

theorem prim_caml_sys_const_ostype_unix_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_ostype_unix" :=
  prim_constant_returns (n := 1#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_ostype_unix
    (by const_shape) caml_sys_const_ostype_unix_summary

theorem prim_caml_sys_const_ostype_win32_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_ostype_win32" :=
  prim_constant_returns (n := 0#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_ostype_win32
    (by const_shape) caml_sys_const_ostype_win32_summary

theorem prim_caml_sys_const_ostype_cygwin_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_ostype_cygwin" :=
  prim_constant_returns (n := 0#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_ostype_cygwin
    (by const_shape) caml_sys_const_ostype_cygwin_summary

theorem prim_caml_sys_const_backend_type_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_const_backend_type" :=
  prim_constant_returns (n := 1#63) stable (by decide) PrimitiveEntries.entry_caml_sys_const_backend_type
    (by const_shape) caml_sys_const_backend_type_summary

end OCaml.Vm.Sim
