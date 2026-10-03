import OCaml.Vm.Sim.CopyLogFrame
import OCaml.Vm.Sim.ForwardCopyArithmetic
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Run.CountedLoop
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def cursorCopyWrites : List Register := [Register.x13, Register.x14, Register.x15] ++ noiseRegs

/-- Geometry and an unchanged source snapshot for a cursor copy. -/
structure CursorCopyRegion (source target : Nat) (words : List (BitVec 64)) (initial : Config) : Prop where
  upper : source + 8 * words.length < 2^64
  reads : ∀ i, i < words.length → RamReadAt (source + 8 * i) 8
  writes : ∀ i, i < words.length → RamWriteAt (target + 8 * i) 8
  image : ImageOutside (valueLog target words)
  separate : OutLRange (valueLog target words) source (8 * words.length)
  snapshot : ∀ i w, words[i]? = some w → word initial (source + 8 * i) = w

/-- A cursor loop counts by advancing its source pointer one word at a time. -/
structure CursorCopyAtPc (entry exit : BitVec 64) (source target : Nat) (words : List (BitVec 64)) (initial : Config)
    (copied : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  image : ExecutableImage c
  bound : copied ≤ words.length
  pc : pcOf c = some (if copied < words.length then entry else exit)
  sourceReg : gpr c 15 = some (BitVec.ofNat 64 (source + 8 * copied))
  targetReg : gpr c 14 = some (BitVec.ofNat 64 (target + 8 * copied))
  limit : gpr c 12 = some (BitVec.ofNat 64 (source + 8 * words.length))
  memory : c.σ.mem = writeLog initial.σ.mem (forwardCopyLog target words copied)
  frame : StepFrameOut cursorCopyWrites initial.σ c.σ

def cursorCopyIndex (source : Nat) (c : Config) : Nat := (((gpr c 15).getD 0).toNat - source) / 8

theorem CursorCopyAtPc.index {entry exit : BitVec 64} {source target copied : Nat} {words : List (BitVec 64)} {initial c : Config}
    (region : CursorCopyRegion source target words initial)
    (h : CursorCopyAtPc entry exit source target words initial copied c) : cursorCopyIndex source c = copied := by
  have small : source + 8 * copied < 2^64 := by have bound := h.bound; have upper := region.upper; omega
  simp only [cursorCopyIndex, h.sourceReg, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  omega

theorem CursorCopyAtPc.read {entry exit : BitVec 64} {source target copied i : Nat} {words : List (BitVec 64)} {initial c : Config}
    {value : BitVec 64} (region : CursorCopyRegion source target words initial)
    (h : CursorCopyAtPc entry exit source target words initial copied c) (selected : words[i]? = some value) :
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

structure CursorCopyPostPc (entry exit : BitVec 64) (source target count copied : Nat) (value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : pcOf after = some (if copied + 1 < count then entry else exit)
  sourceReg : gpr after 15 = some (BitVec.ofNat 64 (source + 8 * (copied + 1)))
  targetReg : gpr after 14 = some (BitVec.ofNat 64 (target + 8 * (copied + 1)))
  limit : gpr after 12 = some (BitVec.ofNat 64 (source + 8 * count))
  memory : after.σ.mem = writeLog before.σ.mem [(target + 8 * copied, 8, value)]
  frame : StepFrameOut cursorCopyWrites before.σ after.σ

theorem CursorCopyAtPc.advance {entry exit : BitVec 64} {source target i : Nat} {words : List (BitVec 64)} {initial c d : Config}
    (region : CursorCopyRegion source target words initial) (h : CursorCopyAtPc entry exit source target words initial i c)
    (bound : i < words.length) (post : CursorCopyPostPc entry exit source target words.length i words[i] c d) :
    CursorCopyAtPc entry exit source target words initial (i + 1) d := by
  obtain ⟨image, memory⟩ := forward_copy_memory_step bound h.image region.image h.memory post.memory
  exact ⟨post.good, post.tick, image, by omega, post.pc, post.sourceReg, post.targetReg, post.limit,
    memory, (h.frame.trans post.frame).widenChecked (allowed := cursorCopyWrites) (by decide)⟩

/-- The common counted-loop rule folds any source-pointer invariant at the supplied code addresses. -/
theorem cursor_copy_loop_at {entry exit : BitVec 64} {source target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : CursorCopyRegion source target words initial)
    (body : ∀ i, Vsa.Logic.Triple (fun c => CursorCopyAtPc entry exit source target words initial i c ∧ i < words.length)
      (CursorCopyAtPc entry exit source target words initial (i + 1))) :
    Vsa.Logic.Triple (CursorCopyAtPc entry exit source target words initial 0)
      (CursorCopyAtPc entry exit source target words initial words.length) :=
  OCaml.Run.counted_loop words.length (cursorCopyIndex source) (CursorCopyAtPc entry exit source target words initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) body

/-- Fold generated taken/fallthrough branches without repeating machine-run plumbing. -/
theorem cursor_copy_run_of_branches {entry exit : BitVec 64} {source target : Nat}
    {words : List (BitVec 64)} {initial : Config}
    (region : CursorCopyRegion source target words initial)
    (more : ∀ i c, CursorCopyAtPc entry exit source target words initial i c →
      i < words.length → i + 1 < words.length →
      ∃ nb after, StepsN nb c after ∧ CursorCopyAtPc entry exit source target words initial (i + 1) after)
    (last : ∀ i c, CursorCopyAtPc entry exit source target words initial i c →
      i < words.length → i + 1 = words.length →
      ∃ nb after, StepsN nb c after ∧ CursorCopyAtPc entry exit source target words initial (i + 1) after) :
    Vsa.Logic.Triple (CursorCopyAtPc entry exit source target words initial 0)
      (CursorCopyAtPc entry exit source target words initial words.length) := by
  apply cursor_copy_loop_at region
  intro i c ⟨h, bound⟩
  have body : ∃ nb after, StepsN nb c after ∧
      CursorCopyAtPc entry exit source target words initial (i + 1) after := by
    by_cases next : i + 1 < words.length
    · exact more i c h bound next
    · exact last i c h bound (by omega)
  obtain ⟨nb, after, steps, post⟩ := body
  exact ⟨after, OCaml.Run.vsa_steps_iff.mpr ⟨nb, OCaml.Run.vsa_stepsN_iff.mp steps⟩, post⟩

/-- GRAB specializes the shared cursor invariant to its generated loop addresses. -/
abbrev CursorCopyAt := CursorCopyAtPc 0x80003700#64 0x80003714#64
abbrev CursorCopyPost := CursorCopyPostPc 0x80003700#64 0x80003714#64

/-- Generic MAKEBLOCK uses the same register loop at its own code addresses. -/
abbrev MakeblockCopyAt := CursorCopyAtPc 0x800026cc#64 0x800026e0#64
abbrev MakeblockCopyPost := CursorCopyPostPc 0x800026cc#64 0x800026e0#64

end OCaml.Vm.Sim
