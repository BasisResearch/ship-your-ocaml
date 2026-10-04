import OCaml.Vm.Sim.ClosurerecInfixLog

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def infixWrites : List Register :=
  [Register.x8, Register.x11, Register.x12, Register.x13, Register.x14, Register.x15] ++ noiseRegs

/-- One concrete infix iteration has four aligned writable slots. -/
structure InfixWriteAt (a stackStart index : Nat) : Prop where
  header : RamWriteAt (a + 24 * index - 8) 8
  stack : RamWriteAt (stackStart - 8 * index) 8
  arity : RamWriteAt (a + 24 * index + 8) 8
  code : RamWriteAt (a + 24 * index) 8

/-- Finite metadata destinations and preserved relative bytecode offsets. -/
structure InfixRegion (pl : Place) (pc a stackStart : Nat) (targets : List Nat)
    (offsets : Nat → BitVec 32) (initial : Config) : Prop where
  small : 3 * (targets.length + 1) < 2^31
  room : 8 * targets.length ≤ stackStart
  reads : ∀ i, i < targets.length → RamReadAt (pl.codeBase + 4 * (pc + 4 + i)) 4
  writes : ∀ i, i < targets.length → InfixWriteAt a stackStart (i + 1)
  image : ImageOutside (infixGroups pl a stackStart targets).flatten
  outside : ∀ i, i < targets.length → OutLRange (infixGroups pl a stackStart targets).flatten
    (pl.codeBase + 4 * (pc + 4 + i)) 4
  snapshot : ∀ i, i < targets.length → bytesT4 initial.σ.mem (pl.codeBase + 4 * (pc + 4 + i)) = offsets i
  jump : ∀ i, (bound : i < targets.length) → target pc 2 (offsets i).toInt = some targets[i]

/-- The loop writes function copied+1; function zero was initialized separately. -/
structure InfixRegisters (pl : Place) (pc a stackStart functions copied : Nat) (c : Config) : Prop where
  counter : gpr c 13 = some (BitVec.ofNat 64 (3 * (copied + 1)))
  targetReg : gpr c 15 = some (BitVec.ofNat 64 (a + 24 * (copied + 1)))
  stackReg : gpr c 11 = some (BitVec.ofNat 64 (stackStart - 8 * copied))
  codeReg : gpr c 8 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 4 + copied)))
  arity : gpr c 12 = some (infixArityWord functions (copied + 1))
  codeBase : gpr c 16 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3)))
  limit : gpr c 10 = some (BitVec.ofNat 64 (3 * functions))

structure InfixAt (pl : Place) (pc a stackStart : Nat) (targets : List Nat) (initial : Config)
    (copied : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  image : ExecutableImage c
  bound : copied ≤ targets.length
  pcAt : pcOf c = some (if copied < targets.length then 0x8000296c#64 else 0x800029a8#64)
  regs : InfixRegisters pl pc a stackStart (targets.length + 1) copied c
  memory : c.σ.mem = writeLog initial.σ.mem (groupedLog (infixGroups pl a stackStart targets) copied)
  frame : StepFrameOut infixWrites initial.σ c.σ

def infixIndex (c : Config) : Nat := ((gpr c 13).getD 0).toNat / 3 - 1

theorem InfixAt.index {pl : Place} {pc a stackStart copied : Nat} {targets : List Nat}
    {offsets : Nat → BitVec 32} {initial c : Config} (region : InfixRegion pl pc a stackStart targets offsets initial)
    (h : InfixAt pl pc a stackStart targets initial copied c) : infixIndex c = copied := by
  have small : 3 * (copied + 1) < 2^64 := by have bound := h.bound; have small := region.small; omega
  simp only [infixIndex, h.regs.counter, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  omega

/-- The code offset survives completed iterations plus the current header/stack stores. -/
theorem InfixAt.read_after {pl : Place} {pc a stackStart i : Nat} {targets : List Nat}
    {offsets : Nat → BitVec 32} {initial c : Config} {m : Std.ExtHashMap Nat (BitVec 8)}
    (region : InfixRegion pl pc a stackStart targets offsets initial)
    (h : InfixAt pl pc a stackStart targets initial i c) (bound : i < targets.length)
    (memory : m = writeLog c.σ.mem ((infixStores pl a stackStart (targets.length + 1) (i + 1) targets[i]).take 2)) :
    bytesT4 m (pl.codeBase + 4 * (pc + 4 + i)) = offsets i := by
  have gb : i < (infixGroups pl a stackStart targets).length := by rw [infix_groups_length]; exact bound
  have sub := grouped_partial_sublist (infixGroups pl a stackStart targets) i 2 gb
  rw [infix_group_at pl a stackStart targets i bound] at sub
  have outside := outLRange_sublist sub (region.outside i bound)
  rw [← bytesT_four_eq, memory, h.memory, ← writeLog_append, bytesT_writeLog_out _ outside, bytesT_four_eq]
  exact region.snapshot i bound

structure InfixPost (pl : Place) (pc a stackStart : Nat) (targets : List Nat) (i : Nat)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pcAt : pcOf after = some (if i + 1 < targets.length then 0x8000296c#64 else 0x800029a8#64)
  regs : InfixRegisters pl pc a stackStart (targets.length + 1) (i + 1) after
  memory : after.σ.mem = writeLog before.σ.mem (infixStores pl a stackStart (targets.length + 1) (i + 1) ((targets[i]?).getD 0))
  frame : StepFrameOut infixWrites before.σ after.σ

theorem InfixAt.advance {pl : Place} {pc a stackStart i : Nat} {targets : List Nat}
    {offsets : Nat → BitVec 32} {initial c d : Config} (region : InfixRegion pl pc a stackStart targets offsets initial)
    (h : InfixAt pl pc a stackStart targets initial i c) (bound : i < targets.length)
    (post : InfixPost pl pc a stackStart targets i c d) : InfixAt pl pc a stackStart targets initial (i + 1) d := by
  have gb : i < (infixGroups pl a stackStart targets).length := by rw [infix_groups_length]; exact bound
  have memory : d.σ.mem = writeLog c.σ.mem (infixGroups pl a stackStart targets)[i] := by
    rw [infix_group_at pl a stackStart targets i bound]
    simpa only [List.getElem?_eq_getElem bound, Option.getD_some] using post.memory
  obtain ⟨image, fullMemory⟩ := grouped_log_advance gb h.image region.image h.memory memory
  exact ⟨post.good, post.tick, image, by omega, post.pcAt, post.regs, fullMemory,
    (h.frame.trans post.frame).widenChecked (allowed := infixWrites) (by decide)⟩

/-- The common native counted-loop fold handles continuing and final infix branches. -/
theorem infix_run_of_branches {pl : Place} {pc a stackStart : Nat} {targets : List Nat}
    {offsets : Nat → BitVec 32} {initial : Config} (region : InfixRegion pl pc a stackStart targets offsets initial)
    (more : ∀ i c, InfixAt pl pc a stackStart targets initial i c → i < targets.length → i + 1 < targets.length →
      ∃ nb after, StepsN nb c after ∧ InfixAt pl pc a stackStart targets initial (i + 1) after)
    (last : ∀ i c, InfixAt pl pc a stackStart targets initial i c → i < targets.length → i + 1 = targets.length →
      ∃ nb after, StepsN nb c after ∧ InfixAt pl pc a stackStart targets initial (i + 1) after) :
    Vsa.Logic.Triple (InfixAt pl pc a stackStart targets initial 0)
      (InfixAt pl pc a stackStart targets initial targets.length) :=
  OCaml.Run.counted_loop_native targets.length infixIndex (InfixAt pl pc a stackStart targets initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) more last

end OCaml.Vm.Sim
