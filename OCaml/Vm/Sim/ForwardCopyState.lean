import OCaml.Vm.Sim.ForwardCopyArithmetic
import OCaml.Vm.Sim.CopyLogFrame
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore
import Vsa.Sim.FrameWriteSet
import OCaml.Run.CountedLoop

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def forwardWrites : List Register := [Register.x13, Register.x14, Register.x15] ++ noiseRegs

/-- Source snapshot and geometry for the closure-field copy in RESTART. -/
structure ForwardCopyRegion (a target : Nat) (words : List (BitVec 64)) (initial : Config) : Prop where
  small : words.length + 3 < 2^31
  reads : ∀ i, i < words.length → RamReadAt (a + 24 + 8 * i) 8
  writes : ∀ i, i < words.length → RamWriteAt (target + 8 * i) 8
  image : ImageOutside (valueLog target words)
  separate : OutLRange (valueLog target words) (a + 24) (8 * words.length)
  snapshot : ∀ i w, words[i]? = some w → OCaml.Vm.word initial (a + 24 + 8 * i) = w

/-- Loop-head or exhausted state of the forward closure-field copy. -/
structure ForwardCopyAt (a target : Nat) (words : List (BitVec 64)) (initial : Config)
    (copied : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  image : ExecutableImage c
  bound : copied ≤ words.length
  pc : pcOf c = some (if copied < words.length then 0x80002b94#64 else 0x80002bb0#64)
  sourceReg : gpr c 25 = some (BitVec.ofNat 64 a)
  targetReg : gpr c 13 = some (BitVec.ofNat 64 (target + 8 * copied))
  counter : gpr c 15 = some (BitVec.ofNat 64 (3 + copied))
  limit : gpr c 12 = some (BitVec.ofNat 64 (words.length + 3))
  memory : c.σ.mem = writeLog initial.σ.mem (forwardCopyLog target words copied)
  frame : StepFrameOut forwardWrites initial.σ c.σ

def forwardIndex (c : Config) : Nat := ((gpr c 15).getD 0).toNat - 3

theorem ForwardCopyAt.index {a target copied : Nat} {words : List (BitVec 64)} {initial c : Config}
    (region : ForwardCopyRegion a target words initial) (h : ForwardCopyAt a target words initial copied c) :
    forwardIndex c = copied := by
  have small : 3 + copied < 2^64 := by have bound := h.bound; have small := region.small; omega
  simp only [forwardIndex, h.counter, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  omega

/-- A copied prefix preserves the complete source observation window. -/
theorem ForwardCopyAt.read {a target copied i : Nat} {words : List (BitVec 64)} {initial c : Config}
    {value : BitVec 64} (region : ForwardCopyRegion a target words initial)
    (h : ForwardCopyAt a target words initial copied c) (selected : words[i]? = some value) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (bytesT8 c.σ.mem (a + 24 + 8 * i)) = value :=
  forward_copy_load region.separate h.memory (region.snapshot i value selected)
    (List.getElem?_eq_some_iff.mp selected).1

/-- Every loop store belongs to the final, image-separated write log. -/
theorem ForwardCopyRegion.entry {a target i : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : ForwardCopyRegion a target words initial) (bound : i < words.length) :
    (target + 8 * i, 8, words[i]) ∈ valueLog target words :=
  copy_store_entry bound

/-- Observations supplied by either generated branch of a forward-copy iteration. -/
structure ForwardCopyPost (a target count copied : Nat) (value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : pcOf after = some (if copied + 1 < count then 0x80002b94#64 else 0x80002bb0#64)
  sourceReg : gpr after 25 = some (BitVec.ofNat 64 a)
  targetReg : gpr after 13 = some (BitVec.ofNat 64 (target + 8 * (copied + 1)))
  counter : gpr after 15 = some (BitVec.ofNat 64 (3 + (copied + 1)))
  limit : gpr after 12 = some (BitVec.ofNat 64 (count + 3))
  memory : after.σ.mem = writeLog before.σ.mem [(target + 8 * copied, 8, value)]
  frame : StepFrameOut forwardWrites before.σ after.σ

/-- Extend the copied prefix and preserve the forward-copy invariant. -/
theorem ForwardCopyAt.advance {a target i : Nat} {words : List (BitVec 64)} {initial c d : Config}
    (region : ForwardCopyRegion a target words initial) (h : ForwardCopyAt a target words initial i c)
    (bound : i < words.length) (post : ForwardCopyPost a target words.length i words[i] c d) :
    ForwardCopyAt a target words initial (i + 1) d := by
  obtain ⟨image, memory⟩ := forward_copy_memory_step bound h.image region.image h.memory post.memory
  exact ⟨post.good, post.tick, image, by omega, post.pc, post.sourceReg, post.targetReg,
    post.counter, post.limit, memory,
    (h.frame.trans post.frame).widenChecked (allowed := forwardWrites) (by decide)⟩

/-- Fold a forward-copy invariant over a proved native iteration. -/
theorem forward_copy_loop {a target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : ForwardCopyRegion a target words initial)
    (body : ∀ i, Vsa.Logic.Triple (fun c => ForwardCopyAt a target words initial i c ∧ i < words.length)
      (ForwardCopyAt a target words initial (i + 1))) :
    Vsa.Logic.Triple (ForwardCopyAt a target words initial 0)
      (ForwardCopyAt a target words initial words.length) :=
  OCaml.Run.counted_loop words.length forwardIndex (ForwardCopyAt a target words initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) body

end OCaml.Vm.Sim
