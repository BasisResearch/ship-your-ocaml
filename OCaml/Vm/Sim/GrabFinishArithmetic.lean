import OCaml.Vm.Sim.GrabInitArithmetic
import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- GRAB's captured code pointer is the preceding RESTART instruction. -/
theorem grab_restart_pc (base pc : Nat) (positive : 0 < pc) :
    BitVec.ofNat 64 (base + 4 * pc) + sign_extend (m := 64) (0xffc#12) =
      BitVec.ofNat 64 (base + 4 * (pc - 1)) := by
  rw [show sign_extend (m := 64) (0xffc#12) = -(BitVec.ofNat 64 4) from by decide,
    ← BitVec.sub_eq_add_neg, BitVec.ofNat_sub_ofNat_of_le _ 4 (by decide) (by omega)]
  congr 1
  omega

/-- Three saved caller slots lie immediately below the final GRAB stack pointer. -/
theorem grab_saved_address (sp extra slot : Nat) (slotBound : slot < 3) :
    BitVec.ofNat 64 (sp + 8 * (extra + 4)) - BitVec.ofNat 64 (8 * (3 - slot)) =
      BitVec.ofNat 64 (sp + 8 * (1 + extra) + 8 * slot) := by
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  congr 1
  omega

end OCaml.Vm.Sim
