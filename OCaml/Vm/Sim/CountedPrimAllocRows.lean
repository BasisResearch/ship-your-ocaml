import OCaml.Vm.Sim.CountedAllocFrame
import OCaml.Vm.Sim.PrimGetConfigReturns
import OCaml.Vm.Sim.PrimGetArgvReturns

/-! Allocating primitive return summaries at the local counted layout. These
are callee contracts for later C_CALL composition, not complete opcode rows.
All extra runtime facts have producers from the existing entry runtime. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- The executable-name producer projects the actual base runtime. -/
theorem counted_exeNameAt {Customs : Config → Nat → Prop} {cp : ChanPlace} {world : World} :
    ExeNameAt (countedLayout Gc.f1Layout Customs cp world) :=
  ⟨fun c runtime => f1_exeNameAt.placed c runtime.1⟩

/-- Config allocation has no runtime requirement beyond the produced frame. -/
theorem counted_prim_caml_sys_get_config_returns {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    {cp : ChanPlace} {world : World} (custom : Gc.CustomMemCall Ready state Customs) :
    PrimReturnsAt (countedLayout Gc.f1Layout Customs cp world) P op ra k "caml_sys_get_config" :=
  prim_caml_sys_get_config_returns (counted_primAllocFrame custom)

/-- Executable-name allocation reuses the existing physical name producer. -/
theorem counted_prim_caml_sys_executable_name_returns {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    {cp : ChanPlace} {world : World} (custom : Gc.CustomMemCall Ready state Customs) :
    PrimReturnsAt (countedLayout Gc.f1Layout Customs cp world) P op ra k "caml_sys_executable_name" :=
  prim_caml_sys_executable_name_returns (counted_primAllocFrame custom) counted_exeNameAt

/-- Argv allocation shares the produced allocation and executable-name frames. -/
theorem counted_prim_caml_sys_get_argv_returns {P : Prog} {op : Opcode} {ra : BitVec 64}
    {k : Nat} {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    {cp : ChanPlace} {world : World} (custom : Gc.CustomMemCall Ready state Customs) :
    PrimReturnsAt (countedLayout Gc.f1Layout Customs cp world) P op ra k "caml_sys_get_argv" :=
  prim_caml_sys_get_argv_returns (counted_primAllocFrame custom) counted_exeNameAt

end OCaml.Vm.Sim
