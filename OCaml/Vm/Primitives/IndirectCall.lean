import OCaml.Vm.Primitives.Call
import Vsa.Sim.JalrBridge

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- An indirect ABI-call encoding and source register emitted from the ELF. -/
structure IndirectCallInstr where
  pc : BitVec 64
  word : BitVec 32
  b0 : BitVec 8
  b1 : BitVec 8
  b2 : BitVec 8
  b3 : BitVec 8
  imm : BitVec 12
  source : Nat

def IndirectCallInstr.target (a : IndirectCallInstr) (value : BitVec 64) : BitVec 64 :=
  BitVec.update (value + sign_extend (m := 64) a.imm) 0 0#1

def IndirectCallInstr.link (a : IndirectCallInstr) : BitVec 64 := Sail.BitVec.addInt a.pc 4

structure IndirectShape (a : IndirectCallInstr) : Prop where
  lower : 0x80000000 ≤ a.pc.toNat
  upper : a.pc.toNat + 4 ≤ tohostAddr
  aligned : a.pc.toNat % 4 = 0
  noncompressed : Sail.BitVec.extractLsb (((a.b3.append a.b2).append a.b1).append a.b0) 1 0 = 3#2
  bytes : (((a.b3.append a.b2).append a.b1).append a.b0) = a.word
  sourceLow : 1 ≤ a.source
  sourceHigh : a.source ≤ 31

structure IndirectPins (a : IndirectCallInstr) (c : Config) : Prop where
  byte0 : c.σ.mem[a.pc.toNat]? = some a.b0
  byte1 : c.σ.mem[a.pc.toNat + 1]? = some a.b1
  byte2 : c.σ.mem[a.pc.toNat + 2]? = some a.b2
  byte3 : c.σ.mem[a.pc.toNat + 3]? = some a.b3

def IndirectDecode (a : IndirectCallInstr) : Prop :=
  ∀ s : MState,
    s.regs.get? Register.misa = some initMisa →
    s.regs.get? Register.cur_privilege = some Privilege.Machine →
    s.regs.get? Register.mseccfg = some 0#64 →
    (ext_decode a.word).run s = .ok (instruction.JALR (a.imm, gprIdx a.source, regidx.Regidx 1#5)) s

/-- Shared semantic supplier for generated indirect call encodings. The
actual source-register value determines the target, including JALR bit clearing. -/
theorem indirect_observed {a : IndirectCallInstr} (shape : IndirectShape a) (decode : IndirectDecode a)
    (c : Config) (pins : IndirectPins a c) (good : GoodState c.σ) (tick : c.tick < 2)
    (pc : c.σ.regs.get? Register.PC = some a.pc)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (value : BitVec 64) (source : gprGet c.σ a.source = some value)
    (aligned : (a.target value).toNat % 4 = 0) :
    ∃ after, JalCallFacts (a.target value) a.link c after := by
  obtain ⟨vm,hm⟩ := minstret
  have decoded := decode (afterPrelude c.σ)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact good.misa)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact good.cur_privilege)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact good.mseccfg)
  have read := rX_src c.σ a.pc a.source shape.sourceHigh value
    (show srcPin c.σ a.source value from by
      cases h : a.source with
      | zero => have := shape.sourceLow; omega
      | succ n => simpa only [h, srcPin] using source)
  obtain ⟨s,t,step,ht,hg,memory,obs⟩ := stepObs_jalr c.σ c.tick c.steps a.pc vm value
    a.word a.imm (gprIdx a.source) (regidx.Regidx 1#5) Register.x1 a.link a.b0 a.b1 a.b2 a.b3
    good pc hm pins.byte0 pins.byte1 pins.byte2 pins.byte3 shape.lower shape.upper
    shape.aligned shape.noncompressed shape.bytes decoded read aligned
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ a.link) tick
  exact ⟨⟨s,t,c.steps+1⟩, jalrCallFacts_of_obs step ht hg memory obs⟩

/-- The same full bridge used by direct calls splices an observed indirect
call, retaining the entire supplied register interface and native frame. -/
theorem indirect_summary {a : IndirectCallInstr} (shape : IndirectShape a) (decode : IndirectDecode a)
    (c : Config) (pins : IndirectPins a c) (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (regs : GRegs) (holds : GHolds c.σ regs) (keys : KeysOK (keysG regs))
    (avoid : KeysAvoidRa regs) (value : BitVec 64)
    (source : lookupG a.source regs = some value) (aligned : (a.target value).toNat % 4 = 0) :
    FnSummary a.pc (fun d => d = c) (SegCallFacts [] regs [] (a.target value) a.link c) := by
  constructor
  rintro d ⟨pc,rfl⟩
  obtain ⟨after,h⟩ := bridgeOfSegFull [] regs [] a.pc (a.target value) a.link d
    good pc minstret tick holds keys True.intro True.intro keys avoid (by
      intro middle hg ht hp hm memory kept
      have pin : IndirectPins a middle :=
        ⟨by rw [memory]; exact pins.byte0, by rw [memory]; exact pins.byte1,
         by rw [memory]; exact pins.byte2, by rw [memory]; exact pins.byte3⟩
      exact indirect_observed shape decode middle pin hg ht hp hm value
        (gholds_lookup _ kept source) aligned)
  exact ⟨after,h.run,h⟩

end OCaml.Vm.Primitives
