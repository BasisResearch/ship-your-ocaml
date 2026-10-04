import OCaml.Vm.Sim.PendingRootState
import OCaml.Vm.Sim.PendingRootRows
import OCaml.Vm.Sim.PendingRootImage
import OCaml.Vm.Sim.ComparisonArithmetic
import OCaml.Vm.Primitives.Control
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

def pendingRootBlocks : List BBlock :=
  caml_process_pending_actions_with_root_exnXd6ecFSeg ++ caml_process_pending_actions_with_root_exnXd704Seg

def pendingRootInitial (sp ra value : BitVec 64) : GRegs := [(2, sp), (1, ra), (10, value)]

def pendingRootLoads (c : Config) (sp : BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8)) : List (List (BitVec 8)) :=
  [read4 c.σ.mem Layout.sym_caml_something_to_do, read8 mem (pendingRootRa sp).toNat]

/-- Normalize the stack adjustment against the ELF-derived frame size. -/
theorem pending_root_stack (sp : BitVec 64) :
    sp + sign_extend (m := 64) (0xf90#12) = pendingRootStack sp := by
  rw [show sign_extend (m := 64) (0xf90#12) = -(BitVec.ofNat 64 Layout.pendingRootFrameBytes) from by decide]
  exact (BitVec.sub_eq_add_neg sp _).symm

/-- The register evaluator is independent of the two observed memory values. -/
theorem pending_root_regs (sp ra value : BitVec 64) (pending saved : List (BitVec 8)) :
    (evalBlocks pendingRootBlocks (SegEvalState.init (pendingRootInitial sp ra value) [pending, saved])).regs =
      [(2, sp), (1, bytesVal .ld saved), (15, bytesVal .lw pending), (10, value)] := by
  change [(2, (sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x070#12)),
    (1, bytesVal .ld saved), (15, bytesVal .lw pending), (10, value)] = _
  rw [pending_root_stack]
  change [(2, (sp - BitVec.ofNat 64 Layout.pendingRootFrameBytes) + BitVec.ofNat 64 Layout.pendingRootFrameBytes),
    (1, bytesVal .ld saved), (15, bytesVal .lw pending), (10, value)] = _
  rw [BitVec.sub_add_cancel]

/-- The CFG's reflected memory effect is exactly the two saved words. -/
theorem pending_root_log (sp ra value : BitVec 64) (pending saved : List (BitVec 8)) :
    (evalBlocks pendingRootBlocks (SegEvalState.init (pendingRootInitial sp ra value) [pending, saved])).log =
      pendingRootLog sp ra value := by
  change [(((sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x068#12)).toNat, 8, ra),
    (((sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x018#12)).toNat, 8, value)] = _
  rw [pending_root_stack]
  rfl

/-- All loads and stores of the no-pending path, including return-slot readback. -/
theorem pending_root_input {sp ra value : BitVec 64} {c : Config} {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : PendingRootInput sp ra value c) (memory : mem = writeLog c.σ.mem (pendingRootLog sp ra value)) :
    BlockInput pendingRootBlocks 0x8000d6ec#64 (pendingRootInitial sp ra value) (pendingRootLoads c sp mem) c := by
  have saved : bytesT mem (pendingRootRa sp).toNat 8 = ra := by
    rw [memory]; exact pending_root_return_word h
  have pending : bytesVal .lw (read4 c.σ.mem Layout.sym_caml_something_to_do) = 0#64 := by
    rw [read4_value]
    change sign_extend (m := 64) (word32 c Layout.sym_caml_something_to_do) = 0#64
    rw [h.pending]; rfl
  refine ⟨h.good, h.good.minstret, ⟨h.stack, h.returnReg, h.argument, trivial⟩, ?_, ?_, ?_, h.tick⟩
  · change KeysOK [2, 1, 10]; decide
  · have code := caml_process_pending_actions_with_root_exn_loaded h.image
    chain_facts code with "Vsa.Sim.Code.caml_process_pending_actions_with_root_exn_at_"
    · apply ReadWindow.lw (x := BitVec.ofNat 64 Layout.sym_caml_something_to_do)
        (by constructor <;> decide) rfl
        (by change (0x8000d6ec#64 + sign_extend (m := 64) ((0x00057#20) +++ 0#12)) + sign_extend (m := 64) (0x444#12) = BitVec.ofNat 64 Layout.sym_caml_something_to_do; decide)
      change LPins4 c.σ.mem Layout.sym_caml_something_to_do (read4 c.σ.mem Layout.sym_caml_something_to_do)
      exact read4_pins _ _
    · apply h.raWrite.sd rfl
      change (sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x068#12) = pendingRootRa sp
      rw [pending_root_stack]
      rfl
    · apply h.valueWrite.sd rfl
      change (sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x018#12) = pendingRootValue sp
      rw [pending_root_stack]
      rfl
    · change (bytesVal .lw (read4 c.σ.mem Layout.sym_caml_something_to_do) != 0#64) = false
      rw [pending]; decide
    · apply h.raWrite.read.ld rfl
        (by change (sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x068#12) = pendingRootRa sp; rw [pending_root_stack]; rfl)
      change LPins8 (writeLog c.σ.mem
        ([(((sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x068#12)).toNat, 8, ra),
          (((sp + sign_extend (m := 64) (0xf90#12)) + sign_extend (m := 64) (0x018#12)).toNat, 8, value)]))
        (pendingRootRa sp).toNat (read8 mem (pendingRootRa sp).toNat)
      rw [pending_root_stack]
      change LPins8 (writeLog c.σ.mem (pendingRootLog sp ra value)) _ _
      rw [← memory]
      exact read8_pins _ _
    · change (Sail.BitVec.update (bytesVal .ld (read8 mem (pendingRootRa sp).toNat) + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [read8_value, saved, ret_tgt ra h.aligned]
      exact h.aligned
  · change ChainOK 0x8000d6ec#64 [2, 1, 10] pendingRootBlocks; decide

end OCaml.Vm.Sim
