import OCaml.Vm.Sim.CopyLogFrame
import OCaml.Vm.Sim.ForwardCopyArithmetic
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Run.CountedLoop
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def cursorCopyWrites : List Register := [Register.x13, Register.x14, Register.x15] ++ noiseRegs

/-- Pointer-copy loops either advance both cursors or recover the source
from a destination displacement. Their register choices are explicit. -/
structure PointerCopyShape where
  targetCounter : Bool
  sourceReg : Nat
  targetReg : Nat
  limitReg : Nat
  writes : List Register

def PointerCopyShape.counterBase (shape : PointerCopyShape) (source target : Nat) : Nat :=
  if shape.targetCounter then target else source

def PointerCopyShape.counterReg (shape : PointerCopyShape) : Nat :=
  if shape.targetCounter then shape.targetReg else shape.sourceReg

def PointerCopyShape.sourceWord (shape : PointerCopyShape) (source copied : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (if shape.targetCounter then source else source + 8 * copied)

abbrev cursorCopyShape : PointerCopyShape := ⟨false, 15, 14, 12, cursorCopyWrites⟩

/-- Geometry and an unchanged source snapshot for a cursor copy. -/
structure PointerCopyRegion (shape : PointerCopyShape) (source target : Nat) (words : List (BitVec 64)) (initial : Config) : Prop where
  upper : shape.counterBase source target + 8 * words.length < 2^64
  reads : ∀ i, i < words.length → RamReadAt (source + 8 * i) 8
  writes : ∀ i, i < words.length → RamWriteAt (target + 8 * i) 8
  image : ImageOutside (valueLog target words)
  separate : OutLRange (valueLog target words) source (8 * words.length)
  snapshot : ∀ i w, words[i]? = some w → word initial (source + 8 * i) = w

/-- A setup log disjoint from the source transports all cursor-copy observations. -/
theorem PointerCopyRegion.frame {shape : PointerCopyShape} {source target : Nat} {words : List (BitVec 64)}
    {before after : Config} {log : List WEntry}
    (region : PointerCopyRegion shape source target words before)
    (outside : OutLRange log source (8 * words.length))
    (memory : after.σ.mem = writeLog before.σ.mem log) :
    PointerCopyRegion shape source target words after := by
  refine ⟨region.upper, region.reads, region.writes, region.image, region.separate, ?_⟩
  intro i w selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have disjoint := outLRange_subrange outside (show source ≤ source + 8 * i by omega)
    (show source + 8 * i + 8 ≤ source + 8 * words.length by omega)
  change bytesT after.σ.mem (source + 8 * i) 8 = w
  rw [memory, bytesT_writeLog_out _ disjoint]
  exact region.snapshot i w selected

/-- A pointer-copy loop records its selected counter and exact written prefix. -/
structure PointerCopyAt (shape : PointerCopyShape) (entry exit : BitVec 64) (source target : Nat) (words : List (BitVec 64)) (initial : Config)
    (copied : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  image : ExecutableImage c
  bound : copied ≤ words.length
  pc : pcOf c = some (if copied < words.length then entry else exit)
  sourceReg : gpr c shape.sourceReg = some (shape.sourceWord source copied)
  targetReg : gpr c shape.targetReg = some (BitVec.ofNat 64 (target + 8 * copied))
  limit : gpr c shape.limitReg = some (BitVec.ofNat 64 (shape.counterBase source target + 8 * words.length))
  memory : c.σ.mem = writeLog initial.σ.mem (forwardCopyLog target words copied)
  frame : StepFrameOut shape.writes initial.σ c.σ

def pointerCopyIndex (shape : PointerCopyShape) (source target : Nat) (c : Config) : Nat :=
  (((gpr c shape.counterReg).getD 0).toNat - shape.counterBase source target) / 8

theorem PointerCopyAt.counter {shape : PointerCopyShape} {entry exit : BitVec 64}
    {source target copied : Nat} {words : List (BitVec 64)} {initial c : Config}
    (h : PointerCopyAt shape entry exit source target words initial copied c) :
    gpr c shape.counterReg = some (BitVec.ofNat 64 (shape.counterBase source target + 8 * copied)) := by
  cases branch : shape.targetCounter
  · simpa only [PointerCopyShape.counterReg, PointerCopyShape.counterBase,
      PointerCopyShape.sourceWord, branch, Bool.false_eq_true, ite_false] using h.sourceReg
  · simpa only [PointerCopyShape.counterReg, PointerCopyShape.counterBase,
      branch, ite_true] using h.targetReg

theorem PointerCopyAt.index {shape : PointerCopyShape} {entry exit : BitVec 64}
    {source target copied : Nat} {words : List (BitVec 64)} {initial c : Config}
    (region : PointerCopyRegion shape source target words initial)
    (h : PointerCopyAt shape entry exit source target words initial copied c) :
    pointerCopyIndex shape source target c = copied := by
  have small : shape.counterBase source target + 8 * copied < 2^64 := by
    have bound := h.bound; have upper := region.upper; omega
  simp only [pointerCopyIndex, h.counter, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  omega

theorem PointerCopyAt.read {shape : PointerCopyShape} {entry exit : BitVec 64} {source target copied i : Nat} {words : List (BitVec 64)} {initial c : Config}
    {value : BitVec 64} (region : PointerCopyRegion shape source target words initial)
    (h : PointerCopyAt shape entry exit source target words initial copied c) (selected : words[i]? = some value) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (bytesT8 c.σ.mem (source + 8 * i)) = value :=
  forward_copy_load region.separate h.memory (region.snapshot i value selected)
    (List.getElem?_eq_some_iff.mp selected).1

/-- A bounded cursor differs from the final cursor until the last iteration. -/
theorem cursor_copy_guard (source count i : Nat) (more : i + 1 < count) (upper : source + 8 * count < 2^64) :
    (BitVec.ofNat 64 (source + 8 * count) != BitVec.ofNat 64 (source + 8 * (i + 1))) = true := by
  rw [bne_iff_ne]
  intro equal
  have nat := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt upper,
    Nat.mod_eq_of_lt (show source + 8 * (i + 1) < 2^64 by omega)] at nat
  omega

structure PointerCopyPost (shape : PointerCopyShape) (entry exit : BitVec 64) (source target count copied : Nat) (value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : pcOf after = some (if copied + 1 < count then entry else exit)
  sourceReg : gpr after shape.sourceReg = some (shape.sourceWord source (copied + 1))
  targetReg : gpr after shape.targetReg = some (BitVec.ofNat 64 (target + 8 * (copied + 1)))
  limit : gpr after shape.limitReg = some (BitVec.ofNat 64 (shape.counterBase source target + 8 * count))
  memory : after.σ.mem = writeLog before.σ.mem [(target + 8 * copied, 8, value)]
  frame : StepFrameOut shape.writes before.σ after.σ

theorem PointerCopyAt.advance {shape : PointerCopyShape} {entry exit : BitVec 64} {source target i : Nat} {words : List (BitVec 64)} {initial c d : Config}
    (region : PointerCopyRegion shape source target words initial) (h : PointerCopyAt shape entry exit source target words initial i c)
    (bound : i < words.length) (post : PointerCopyPost shape entry exit source target words.length i words[i] c d) :
    PointerCopyAt shape entry exit source target words initial (i + 1) d := by
  obtain ⟨image, memory⟩ := forward_copy_memory_step bound h.image region.image h.memory post.memory
  exact ⟨post.good, post.tick, image, by omega, post.pc, post.sourceReg, post.targetReg, post.limit,
    memory, (h.frame.trans post.frame).widen (by intro r hr; simpa only [List.mem_append, or_self] using hr)⟩

/-- The common counted-loop rule folds either pointer counter at the supplied code addresses. -/
theorem cursor_copy_loop_at {shape : PointerCopyShape} {entry exit : BitVec 64} {source target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : PointerCopyRegion shape source target words initial)
    (body : ∀ i, Vsa.Logic.Triple (fun c => PointerCopyAt shape entry exit source target words initial i c ∧ i < words.length)
      (PointerCopyAt shape entry exit source target words initial (i + 1))) :
    Vsa.Logic.Triple (PointerCopyAt shape entry exit source target words initial 0)
      (PointerCopyAt shape entry exit source target words initial words.length) :=
  OCaml.Run.counted_loop words.length (pointerCopyIndex shape source target) (PointerCopyAt shape entry exit source target words initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) body

/-- Fold generated taken/fallthrough branches without repeating machine-run plumbing. -/
theorem cursor_copy_run_of_branches {shape : PointerCopyShape} {entry exit : BitVec 64} {source target : Nat}
    {words : List (BitVec 64)} {initial : Config}
    (region : PointerCopyRegion shape source target words initial)
    (more : ∀ i c, PointerCopyAt shape entry exit source target words initial i c →
      i < words.length → i + 1 < words.length →
      ∃ nb after, StepsN nb c after ∧ PointerCopyAt shape entry exit source target words initial (i + 1) after)
    (last : ∀ i c, PointerCopyAt shape entry exit source target words initial i c →
      i < words.length → i + 1 = words.length →
      ∃ nb after, StepsN nb c after ∧ PointerCopyAt shape entry exit source target words initial (i + 1) after) :
    Vsa.Logic.Triple (PointerCopyAt shape entry exit source target words initial 0)
      (PointerCopyAt shape entry exit source target words initial words.length) :=
  OCaml.Run.counted_loop_native words.length (pointerCopyIndex shape source target) (PointerCopyAt shape entry exit source target words initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) more last

/-- Legacy source-pointer copies specialize the shared register shape. -/
abbrev CursorCopyRegion := PointerCopyRegion cursorCopyShape
abbrev CursorCopyAtPc := PointerCopyAt cursorCopyShape
abbrev CursorCopyPostPc := PointerCopyPost cursorCopyShape

/-- GRAB specializes the shared cursor invariant to its generated loop addresses. -/
abbrev CursorCopyAt := CursorCopyAtPc 0x80003700#64 0x80003714#64
abbrev CursorCopyPost := CursorCopyPostPc 0x80003700#64 0x80003714#64

/-- Generic MAKEBLOCK uses the same register loop at its own code addresses. -/
abbrev MakeblockCopyAt := CursorCopyAtPc 0x800026cc#64 0x800026e0#64
abbrev MakeblockCopyPost := CursorCopyPostPc 0x800026cc#64 0x800026e0#64

end OCaml.Vm.Sim
