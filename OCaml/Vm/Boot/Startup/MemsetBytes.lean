import OCaml.Vm.Boot.Startup.MemsetBytesNormalized
import OCaml.Vm.Boot.Startup.MemsetPair
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def memsetBytesInput (dest p ra : BitVec 64) : GRegs :=
  [(11, 0#64), (14, p), (1, ra), (10, dest)]

def memsetBytesLog (p : BitVec 64) : List WEntry :=
  [((p + 7#64).toNat, 1, 0#64), ((p + 6#64).toNat, 1, 0#64),
   ((p + 5#64).toNat, 1, 0#64), ((p + 4#64).toNat, 1, 0#64),
   ((p + 3#64).toNat, 1, 0#64), ((p + 2#64).toNat, 1, 0#64),
   ((p + 1#64).toNat, 1, 0#64), (p.toNat, 1, 0#64)]

structure MemsetBytesInput (dest p ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  destination : gprGet c.σ 10 = some dest
  cursor : gprGet c.σ 14 = some p
  zero : gprGet c.σ 11 = some 0#64
  windows : ∀ i : Nat, i < 8 → WriteWindow (p + BitVec.ofNat 64 i) 1
  outside : ImageOutside (memsetBytesLog p)

theorem memsetBytes_input {dest p ra c} (h : MemsetBytesInput dest p ra c) :
    BlockInput memsetX27d8Seg 0x800427d8#64 (memsetBytesInput dest p ra) [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.zero, h.cursor, h.raReg, h.destination, trivial⟩
  keys := by change KeysOK [11, 14, 1, 10]; decide
  shape := by change ChainOK _ [11, 14, 1, 10] _; decide
  tick := h.tick
  facts := by
    have code := memsetPrefix_code h.image
    chain_facts code with "Vsa.Sim.Code.memset_at_"
    all_goals first
      | exact (h.windows 7 (by decide)).sb rfl rfl
      | exact (h.windows 6 (by decide)).sb rfl rfl
      | exact (h.windows 5 (by decide)).sb rfl rfl
      | exact (h.windows 4 (by decide)).sb rfl rfl
      | exact (h.windows 3 (by decide)).sb rfl rfl
      | exact (h.windows 2 (by decide)).sb rfl rfl
      | exact (h.windows 1 (by decide)).sb rfl rfl
      | exact (h.windows 0 (by decide)).sb rfl rfl
      | (change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
         rw [ret_tgt ra h.aligned]; exact h.aligned)

theorem memsetBytes_log (dest p ra : BitVec 64) :
    (evalBlocks memsetX27d8Seg (SegEvalState.init (memsetBytesInput dest p ra) [])).log =
      memsetBytesLog p := by
  change [((p + 7#64).toNat, 1, 0#64), ((p + 6#64).toNat, 1, 0#64),
   ((p + 5#64).toNat, 1, 0#64), ((p + 4#64).toNat, 1, 0#64),
   ((p + 3#64).toNat, 1, 0#64), ((p + 2#64).toNat, 1, 0#64),
   ((p + 1#64).toNat, 1, 0#64), ((p + 0#64).toNat, 1, 0#64)] = _
  rw [BitVec.add_zero]
  rfl

/-- The eight-byte tail clears the remainder and returns to the caller. -/
theorem memset_bytes (c : Config) (dest p ra : BitVec 64) (h : MemsetBytesInput dest p ra c) :
    FnSummary 0x800427d8#64 (fun d => d = c)
      (WriteRegistersPost [] (memsetBytesLog p) c ra dest (memsetBytesInput dest p ra)) := by
  apply registers_of_blocks h.image h.outside (block_summary _ _ _ _ _ (memsetBytes_input h))
  · exact memsetBytes_log _ _ _
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    exact ret_tgt ra h.aligned
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
