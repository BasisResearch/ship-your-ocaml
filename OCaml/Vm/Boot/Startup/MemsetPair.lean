import OCaml.Vm.Boot.Startup.MemsetLoopNormalized
import OCaml.Vm.Boot.Startup.MemsetPrefix
import OCaml.Vm.Primitives.Effects
import OCaml.Vm.Primitives.Write
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def memsetPairBlocks (taken : Bool) : List BBlock :=
  if taken then memsetX2790TSeg else memsetX2790FSeg

def memsetPairInput (dest p limit : BitVec 64) : GRegs := [(11, 0#64), (14, p), (13, limit), (10, dest)]

def memsetPairLog (p : BitVec 64) : List WEntry :=
  [(p.toNat, 8, 0#64), ((p + 8#64).toNat, 8, 0#64)]

def memsetPairRegs (dest p limit : BitVec 64) : GRegs := [(14, p + 16#64), (11, 0#64), (13, limit), (10, dest)]

structure MemsetPairInput (dest p limit ra : BitVec 64) (taken : Bool) (c : Config) : Prop
    extends LeafInput ra c where
  destination : gprGet c.σ 10 = some dest
  zero : gprGet c.σ 11 = some 0#64
  cursor : gprGet c.σ 14 = some p
  limitReg : gprGet c.σ 13 = some limit
  window0 : WriteWindow p 8
  window8 : WriteWindow (p + 8#64) 8
  outside : ImageOutside (memsetPairLog p)
  branch : guardB bop.BLTU (p + 16#64) limit = taken

theorem memsetPair_input {dest p limit ra : BitVec 64} {taken : Bool} {c : Config}
    (h : MemsetPairInput dest p limit ra taken c) :
    BlockInput (memsetPairBlocks taken) 0x80042790#64 (memsetPairInput dest p limit) [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.zero, h.cursor, h.limitReg, h.destination, trivial⟩
  keys := by change KeysOK [11, 14, 13, 10]; decide
  shape := by cases taken <;> change ChainOK _ [11, 14, 13, 10] _ <;> decide
  tick := h.tick
  facts := by
    have code := memsetPrefix_code h.image
    have branch := h.branch
    cases taken <;> (chain_facts code with "Vsa.Sim.Code.memset_at_")
    all_goals first
      | exact h.window0.sd rfl (by change p + 0#64 = p; exact BitVec.add_zero p)
      | exact h.window8.sd rfl rfl
      | exact branch

theorem memsetPair_log (dest p limit : BitVec 64) (taken : Bool) :
    (evalBlocks (memsetPairBlocks taken) (SegEvalState.init (memsetPairInput dest p limit) [])).log =
      memsetPairLog p := by
  cases taken <;>
    change [((p + 0#64).toNat, 8, 0#64), ((p + 8#64).toNat, 8, 0#64)] = _
  all_goals rw [BitVec.add_zero]; rfl

theorem memsetPair_regs (dest p limit : BitVec 64) (taken : Bool) :
    (evalBlocks (memsetPairBlocks taken) (SegEvalState.init (memsetPairInput dest p limit) [])).regs =
      memsetPairRegs dest p limit := by cases taken <;> rfl

/-- One generated word-loop iteration writes sixteen zero bytes and either
branches back or exits. The total loop is composed separately with loopFromBody. -/
theorem memset_pair (c : Config) (dest p limit ra : BitVec 64) (taken : Bool)
    (h : MemsetPairInput dest p limit ra taken c) :
    FnSummary 0x80042790#64 (fun d => d = c)
      (WriteRegistersPost [14] (memsetPairLog p) c
        (if taken then 0x80042790#64 else 0x800427a0#64) dest (memsetPairRegs dest p limit)) := by
  apply registers_of_blocks h.image h.outside (block_summary _ _ _ _ _ (memsetPair_input h))
  · exact memsetPair_log _ _ _ _
  · cases taken <;> rfl
  · exact memsetPair_regs _ _ _ _
  · rfl
  · cases taken <;> decide
end OCaml.Vm.Boot.Startup
