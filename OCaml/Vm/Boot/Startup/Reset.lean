import Vsa.Sim.FactorSail
import OCaml.Vm.Boot.WhileMinImage
import OCaml.Vm.Boot.WhileMin

/-! Exact reset interface. No captured register table is used to construct reset.
The initializer is the same `initializeMemory` / `setupElf` pair as the emulator.
The execution statement remains open until the startup summaries are composed. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable Sail.ConcurrencyInterfaceV1 OCaml.Programs

/-- State supplied to Sail's setup routine by the native ELF runner. -/
def resetSeed (elf : ELF64File) : MState :=
  ⟨.emptyWithCapacity, (), initializeMemory .B64 elf, (), 0, #[]⟩

/-- Successful platform setup at architectural step zero. -/
structure ElfReset (elf : ELF64File) (c : Config) : Prop where
  setup : (Vsa.setupElf elf).run (resetSeed elf) = .ok () c.σ
  tick : c.tick = 0
  steps : c.steps = 0

/-- Setup is a function of its seed; step-zero counters determine the whole config. -/
theorem ElfReset.unique {elf : ELF64File} {a b : Config}
    (ha : ElfReset elf a) (hb : ElfReset elf b) : a = b := by
  have state : a.σ = b.σ := (EStateM.Result.ok.inj (ha.setup.symm.trans hb.setup)).2
  have tick : a.tick = b.tick := ha.tick.trans hb.tick.symm
  have steps : a.steps = b.steps := ha.steps.trans hb.steps.symm
  cases a; cases b; cases state; cases tick; cases steps; rfl

/-- Only these two ELF metadata observations affect register setup. -/
def tohostMetadata (elf : ELF64File) : Option Nat :=
  (elf.interpreted_sections.find? is_tohost).map (fun s => s.2.section_addr)

#factor_sail initializeRegisters as registersFactored

/-- Register initialization observes just the entry PC and HTIF metadata.
The generated factoring certificate makes the otherwise deep bind chain opaque
while rewriting its small metadata-dependent prefix. -/
theorem registers_metadata {a b : ELF64File}
    (entry : a.file_header.e_entry = b.file_header.e_entry)
    (tohost : tohostMetadata a = tohostMetadata b) : initializeRegisters a = initializeRegisters b := by
  rw [registersFactored.eq]
  unfold registersFactored
  change (a.interpreted_sections.find? is_tohost).map (fun s => s.2.section_addr) =
    (b.interpreted_sections.find? is_tohost).map (fun s => s.2.section_addr) at tohost
  rw [entry, tohost]

/-- ELF parsing and memory construction are separate from register setup.
This equality allows the setup proof to use a compact metadata representative. -/
theorem setupElf_congr {a b : ELF64File}
    (entry : a.file_header.e_entry = b.file_header.e_entry)
    (tohost : tohostMetadata a = tohostMetadata b) : Vsa.setupElf a = Vsa.setupElf b := by
  unfold Vsa.setupElf
  rw [registers_metadata entry tohost, entry]

private theorem bind_success {α β : Type} (f : SailM α) (g : α → SailM β)
    {s t : MState} {v : β} (h : (f >>= g).run s = .ok v t) :
    ∃ x u, f.run s = .ok x u ∧ (g x).run u = .ok v t := by
  simp only [EStateM.run, bind, EStateM.bind] at h
  cases hf : f s with
  | error e u => simp only [hf] at h; cases h
  | ok x u => exact ⟨x, u, hf, by simpa only [EStateM.run, hf] using h⟩

theorem setupElf_pc {elf : ELF64File} {s t : MState}
    (h : (Vsa.setupElf elf).run s = .ok () t) :
    t.regs.get? .PC = some elf.file_header.e_entry.toBitVec := by
  unfold Vsa.setupElf at h
  obtain ⟨_, _, _, h⟩ := bind_success _ _ h
  obtain ⟨_, _, _, h⟩ := bind_success _ _ h
  obtain ⟨_, _, _, h⟩ := bind_success _ _ h
  obtain ⟨_, _, _, h⟩ := bind_success _ _ h
  simp only [EStateM.run, writeReg, PreSail.writeReg, modify, modifyGet] at h
  cases h
  simp

/-- Successful reset finishes at the ELF entry PC before any instruction is run. -/
theorem ElfReset.pc {elf : ELF64File} {c : Config} (h : ElfReset elf c) :
    c.σ.regs.get? .PC = some elf.file_header.e_entry.toBitVec := setupElf_pc h.setup

/-- The parsed while_min ELF has the saved loader image and pinned startup metadata.
Supplied for the actual archived ELF by `WhileMinElfParse.whileMin_elf`. -/
structure WhileMinElf (elf : ELF64File) : Prop where
  memory : initializeMemory .B64 elf = WhileMinImage.initialMem
  entry : (elf.file_header.e_entry : UInt64).toBitVec = BitVec.ofNat 64 Layout.sym_start
  tohost : tohostMetadata elf = some Layout.sym_tohost

/-- Matching loader memory and setup metadata give the same reset predicate.
No equality of arbitrary initial configurations is assumed. -/
theorem ElfReset.of_whileMinElf {a b : ELF64File} {c : Config}
    (reset : ElfReset a c) (A : WhileMinElf a) (B : WhileMinElf b) : ElfReset b c := by
  have entry : a.file_header.e_entry = b.file_header.e_entry :=
    UInt64.toBitVec_inj.mp (A.entry.trans B.entry.symm)
  have setup := setupElf_congr entry (A.tohost.trans B.tohost.symm)
  have seed : resetSeed a = resetSeed b := by
    unfold resetSeed
    rw [A.memory, B.memory]
  exact ⟨by rw [← setup, ← seed]; exact reset.setup, reset.tick, reset.steps⟩

/-- Round 2 target, stated over the machine's own initialized ELF configuration.
Suppliers: loader correspondence, setup invariant, and startup function summaries. -/
def whileMin_reset_loaded_Statement : Prop :=
  ∀ elf, WhileMinElf elf → ∀ c₀, ElfReset elf c₀ →
    ∃ c_cut, Steps (Vsa.Densify.fillZero c₀) c_cut ∧
      Loaded (runtimeLayout BestFitSingleton OCaml.Vm.Gc.g1Budget) whileMin c_cut

end OCaml.Vm.Boot.Startup
