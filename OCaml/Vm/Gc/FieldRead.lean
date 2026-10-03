import OCaml.Vm.Gc.FieldCopyAccess
import Vsa.Sim.GRegsFrame
import OCaml.Vm.Gc.YoungAccess

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def immediate (slot : BitVec 64) (c : Config) : Bool :=
  guardB .BNE (word c slot.toNat &&& 1#64) 0

def readLoads (slot : BitVec 64) (c : Config) := [read8 c.σ.mem slot.toNat]

theorem read_access (slot delta target index : BitVec 64) (c : Config)
    (window : ReadWindow slot 8) :
    ChainAccess c.σ.mem (regs slot delta target index) (readLoads slot c)
      (readBlocks (immediate slot c)) := by
  generalize choice : immediate slot c = branch
  cases branch <;> apply ChainAccess.cons ?_ ChainAccess.nil
  all_goals constructor
  all_goals first
    | exact head_access_bytes slot delta target index c _ window (read8_pins _ _)
    | (simpa [immediate, readLoads, readBlocks, caml_oldify_mopupX9d4cTSeg,
        caml_oldify_mopupX9d4cFSeg, TermFactsO, TermFactsT, runGM, stepGM,
        regs, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
        read8_value, word, Functions.sign_extend, Sail.BitVec.signExtend] using choice)

structure ReadInput (slot delta target index : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (regs slot delta target index)
  window : ReadWindow slot 8

/-- Loaded field and destination address, before any write or oldify call. -/
structure ReadPost (slot delta target index : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (readBlocks (immediate slot before)) pc (regs slot delta target index)
    (readLoads slot before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (if immediate slot before then storePc else pointerPc) after
  registers : GHolds after.σ (afterHeadRegs slot delta target index (word before slot.toNat))
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem read_machine {slot delta target index c} (input : ReadInput slot delta target index c) :
    FnSummary pc (fun d => d = c) (ReadPost slot delta target index c) := by
  have summary := block_summary (readBlocks (immediate slot c)) pc (regs slot delta target index)
    (readLoads slot c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [8,18,19,9]; decide,
      chainPlan_facts (read_code _ input.code) (read_access slot delta target index c input.window),
      read_ok _, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, read_log]; rfl
  refine ⟨post, memory, ?_, ?_, memory ▸ input.code⟩
  · rw [PCAt, post.pc, read_pc]
  · have registers := read_registers (segmentPost_of_block post)
    simpa only [readLoads, List.headD_cons, read8_value, word] using registers

/-- Compose the loaded field with the range classifier. The runtime domain
register comes from the mopup prologue and survives the field load. -/
theorem ReadPost.young_input {slot delta target index domain before after}
    (post : ReadPost slot delta target index before after)
    (domainReg : gprGet before.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (root : word before Layout.sym_Caml_state = domain)
    (windows : Young.Windows domain) : Young.Input (word before slot.toNat) domain after := by
  have keep : gprGet after.σ 22 = gprGet before.σ 22 := by
    apply post.machine.frame Register.x22 (by decide)
    intro n hn
    have written := read_written _ n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at written
    rcases written with rfl | rfl | rfl <;> decide
  refine ⟨post.machine.good, post.machine.minstret, post.machine.tick, post.code,
    ⟨keep.trans domainReg, gholds_lookup _ post.registers rfl, True.intro⟩, ?_, windows⟩
  change bytesT after.σ.mem _ 8 = _
  rw [post.memory]
  exact root

end OCaml.Vm.Gc.FieldCopy
