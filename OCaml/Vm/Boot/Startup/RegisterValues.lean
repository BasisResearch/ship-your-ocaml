import OCaml.Vm.Boot.Startup.Reset
import Vsa.Sim.NormalizeSail

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Sail ConcurrencyInterfaceV1

/-- The runner's choice source is deterministic and does not change state. -/
theorem choose_pure (p : Sail.Primitive) :
    (PreSail.choose p : SailM p.reflect) = pure (trivialChoiceSource.choose p ()) := by
  funext s
  cases s with
  | mk regs choice mem tags cycles out => cases choice; rfl

-- Keep `trivialChoiceSource` folded here: unfolding it changes the state type
-- before the simplifier matches `choose_pure`. Its chosen values reduce to zero.
#normalize_sail registersFactored as registerValues (elf : ELF64File) : registersFactored elf using [
  choose_pure, pure_bind,
  Functions.undefined_CountSmcntrpmf, Functions.undefined_Counteren,
  Functions.undefined_Counterin, Functions.undefined_Fcsr,
  Functions.undefined_Mcause, Functions.undefined_Medeleg,
  Functions.undefined_Minterrupts, Functions.undefined_Mtvec,
  Functions.undefined_Pmpcfg_ent, Functions.undefined_Privilege,
  Functions.undefined_RVFI_DII_Execution_Packet_Ext_Integer,
  Functions.undefined_RVFI_DII_Execution_Packet_Ext_MemAccess,
  Functions.undefined_RVFI_DII_Execution_Packet_InstMetaData,
  Functions.undefined_RVFI_DII_Execution_Packet_PC,
  Functions.undefined_RVFI_DII_Instruction_Packet,
  Functions.undefined_Vcsr, Functions.undefined_Vtype,
  LeanRV64DExecutable.undefined_bitvector, PreSail.undefined_bitvector,
  LeanRV64DExecutable.undefined_bool, PreSail.undefined_bool,
  LeanRV64DExecutable.undefined_bit, PreSail.undefined_bit,
  LeanRV64DExecutable.undefined_vector, PreSail.undefined_vector,
  LeanRV64DExecutable.internal_pick, PreSail.internal_pick]

/-- Source register initialization equals the normalized header and write fragments.
This is a program equality, not yet the reset GoodState or existence theorem. -/
theorem initializeRegisters_values : initializeRegisters = registerValues := by
  funext elf
  exact (congrFun registersFactored.eq elf).trans (registerValues.eq elf)

end OCaml.Vm.Boot.Startup
