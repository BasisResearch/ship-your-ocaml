import Vsa.Sim.BridgeSegFull
import OCaml.Vm.Primitives.Effects

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- A direct ABI call's instruction data, emitted from the pinned ELF. -/
structure CallInstr where
  pc : BitVec 64
  word : BitVec 32
  b0 : BitVec 8
  b1 : BitVec 8
  b2 : BitVec 8
  b3 : BitVec 8
  imm : BitVec 21

def CallInstr.target (a : CallInstr) : BitVec 64 := a.pc + sign_extend (m := 64) a.imm
def CallInstr.link (a : CallInstr) : BitVec 64 := Sail.BitVec.addInt a.pc 4

structure CallShape (a : CallInstr) : Prop where
  lower : 0x80000000 ≤ a.pc.toNat
  upper : a.pc.toNat + 4 ≤ tohostAddr
  aligned : a.pc.toNat % 4 = 0
  noncompressed : Sail.BitVec.extractLsb (((a.b3.append a.b2).append a.b1).append a.b0) 1 0 = 3#2
  bytes : (((a.b3.append a.b2).append a.b1).append a.b0) = a.word
  targetAligned : a.target.toNat % 4 = 0

structure CallPins (a : CallInstr) (c : Config) : Prop where
  byte0 : c.σ.mem[a.pc.toNat]? = some a.b0
  byte1 : c.σ.mem[a.pc.toNat + 1]? = some a.b1
  byte2 : c.σ.mem[a.pc.toNat + 2]? = some a.b2
  byte3 : c.σ.mem[a.pc.toNat + 3]? = some a.b3

/-- The generated ElfDecode entry supplies this instruction-level certificate. -/
def CallDecode (a : CallInstr) : Prop :=
  ∀ s : MState,
    s.regs.get? Register.misa = some initMisa →
    s.regs.get? Register.cur_privilege = some Privilege.Machine →
    s.regs.get? Register.mseccfg = some 0#64 →
    (ext_decode a.word).run s = .ok (instruction.JAL (a.imm, regidx.Regidx 1#5)) s

/-- One shared observation adapter for every generated direct-call site. -/
theorem call_observed {a : CallInstr} (shape : CallShape a) (decode : CallDecode a)
    (c : Config) (pins : CallPins a c) (good : GoodState c.σ) (tick : c.tick < 2)
    (pc : c.σ.regs.get? Register.PC = some a.pc)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w) :
    ∃ after, JalCallFacts a.target a.link c after := by
  obtain ⟨vm, hm⟩ := minstret
  have decoded := decode (afterPrelude c.σ)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact good.misa)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact good.cur_privilege)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact good.mseccfg)
  obtain ⟨s, t, step, ht, hg, memory, obs⟩ := stepObs_jal c.σ c.tick c.steps a.pc vm
    a.word a.imm (regidx.Regidx 1#5) Register.x1 a.link a.b0 a.b1 a.b2 a.b3
    good pc hm pins.byte0 pins.byte1 pins.byte2 pins.byte3 shape.lower shape.upper
    shape.aligned shape.noncompressed shape.bytes decoded shape.targetAligned
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ a.link) tick
  exact ⟨⟨s, t, c.steps + 1⟩, jalCallFacts_of_obs step ht hg memory obs rfl⟩

/-- The full bridge handles the JAL seam after a separately generated prefix.
Its register interface excludes ra because the call installs its own link. -/
theorem call_summary {a : CallInstr} (shape : CallShape a) (decode : CallDecode a)
    (c : Config) (pins : CallPins a c) (good : GoodState c.σ) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (regs : GRegs) (holds : GHolds c.σ regs) (keys : KeysOK (keysG regs))
    (avoid : KeysAvoidRa regs) :
    FnSummary a.pc (fun d => d = c) (SegCallFacts [] regs [] a.target a.link c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  obtain ⟨after, h⟩ := bridgeOfSegFull [] regs [] a.pc a.target a.link d
    good pc minstret tick holds keys True.intro True.intro keys avoid (by
      intro middle hg ht hp hm memory _
      have pin : CallPins a middle := by
        have mem : middle.σ.mem = d.σ.mem := memory
        exact ⟨by rw [mem]; exact pins.byte0, by rw [mem]; exact pins.byte1,
          by rw [mem]; exact pins.byte2, by rw [mem]; exact pins.byte3⟩
      exact call_observed shape decode middle pin hg ht hp hm)
  exact ⟨after, h.run, h⟩

/-- A full bridge exposes the linked ra and carried argument interface. -/
theorem call_registers_summary {a : CallInstr} (shape : CallShape a) (decode : CallDecode a)
    (c : Config) (pins : CallPins a c) (good : GoodState c.σ) (image : ExecutableImage c)
    (tick : c.tick < 2) (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (regs : GRegs) (holds : GHolds c.σ regs) (keys : KeysOK (keysG regs))
    (avoid : KeysAvoidRa regs) {value : BitVec 64} (result : lookupG 10 regs = some value) :
    FnSummary a.pc (fun d => d = c)
      (RegistersPost [1] c.σ.mem c a.target value ((1, a.link) :: regs)) := by
  have S := call_summary shape decode c pins good tick minstret regs holds keys avoid
  apply S.weaken (fun _ he => he)
  intro after post
  have memory : after.σ.mem = c.σ.mem := post.mem
  refine {
    toEffectPost := {
      good := post.good
      image := ?_
      minstret := post.minstret
      tick := post.tick
      pc := post.pc
      result := gholds_lookup _ post.registers result
      memory := memory
      output := post.output
      frame := ?_ }
    regs := ⟨post.ra, post.registers⟩ }
  · exact ⟨fun i hi => by rw [memory]; exact image.text i hi,
      fun i hi => by rw [memory]; exact image.rodata i hi⟩
  · intro r hr hn
    exact post.frame r hn (by simp [wrChain]) (beq_eq_false_iff_ne.mpr (hr 1 (by simp)))

end OCaml.Vm.Primitives
