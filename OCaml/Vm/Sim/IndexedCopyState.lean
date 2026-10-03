import OCaml.Vm.Sim.ForwardCopyArithmetic
import OCaml.Vm.Sim.CopyLogFrame
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore
import Vsa.Sim.FrameWriteSet
import OCaml.Run.CountedLoop

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- An indexed copy fixes one base register and advances the opposite cursor.
RESTART indexes its source; CLOSURE indexes its destination. -/
structure IndexedCopyShape where
  sourceIndexed : Bool
  bias : Nat
  sourceReg : Nat
  targetReg : Nat
  counterReg : Nat
  limitReg : Nat
  entry : BitVec 64
  exit : BitVec 64
  writes : List Register

def IndexedCopyShape.sourceStart (shape : IndexedCopyShape) (source : Nat) : Nat :=
  source + if shape.sourceIndexed then 8 * shape.bias else 0

def IndexedCopyShape.targetStart (shape : IndexedCopyShape) (target : Nat) : Nat :=
  target + if shape.sourceIndexed then 0 else 8 * shape.bias

def IndexedCopyShape.sourceWord (shape : IndexedCopyShape) (source copied : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (if shape.sourceIndexed then source else source + 8 * copied)

def IndexedCopyShape.targetWord (shape : IndexedCopyShape) (target copied : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (if shape.sourceIndexed then target + 8 * copied else target)

structure IndexedCopyRegion (shape : IndexedCopyShape) (source target : Nat)
    (words : List (BitVec 64)) (initial : Config) : Prop where
  small : words.length + shape.bias < 2^31
  reads : ∀ i, i < words.length → RamReadAt (shape.sourceStart source + 8 * i) 8
  writes : ∀ i, i < words.length → RamWriteAt (shape.targetStart target + 8 * i) 8
  image : ImageOutside (valueLog (shape.targetStart target) words)
  separate : OutLRange (valueLog (shape.targetStart target) words) (shape.sourceStart source) (8 * words.length)
  snapshot : ∀ i w, words[i]? = some w → word initial (shape.sourceStart source + 8 * i) = w

structure IndexedCopyAt (shape : IndexedCopyShape) (source target : Nat)
    (words : List (BitVec 64)) (initial : Config) (copied : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  image : ExecutableImage c
  bound : copied ≤ words.length
  pc : pcOf c = some (if copied < words.length then shape.entry else shape.exit)
  sourceReg : gpr c shape.sourceReg = some (shape.sourceWord source copied)
  targetReg : gpr c shape.targetReg = some (shape.targetWord target copied)
  counter : gpr c shape.counterReg = some (BitVec.ofNat 64 (shape.bias + copied))
  limit : gpr c shape.limitReg = some (BitVec.ofNat 64 (words.length + shape.bias))
  memory : c.σ.mem = writeLog initial.σ.mem (forwardCopyLog (shape.targetStart target) words copied)
  frame : StepFrameOut shape.writes initial.σ c.σ

def indexedCopyIndex (shape : IndexedCopyShape) (c : Config) : Nat :=
  ((gpr c shape.counterReg).getD 0).toNat - shape.bias

theorem IndexedCopyAt.index {shape : IndexedCopyShape} {source target copied : Nat}
    {words : List (BitVec 64)} {initial c : Config}
    (region : IndexedCopyRegion shape source target words initial)
    (h : IndexedCopyAt shape source target words initial copied c) : indexedCopyIndex shape c = copied := by
  have small : shape.bias + copied < 2^64 := by have bound := h.bound; have small := region.small; omega
  simp only [indexedCopyIndex, h.counter, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  omega

theorem IndexedCopyAt.read {shape : IndexedCopyShape} {source target copied i : Nat}
    {words : List (BitVec 64)} {initial c : Config} {value : BitVec 64}
    (region : IndexedCopyRegion shape source target words initial)
    (h : IndexedCopyAt shape source target words initial copied c) (selected : words[i]? = some value) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (bytesT8 c.σ.mem (shape.sourceStart source + 8 * i)) = value :=
  forward_copy_load region.separate h.memory (region.snapshot i value selected)
    (List.getElem?_eq_some_iff.mp selected).1

structure IndexedCopyPost (shape : IndexedCopyShape) (source target count copied : Nat)
    (value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : pcOf after = some (if copied + 1 < count then shape.entry else shape.exit)
  sourceReg : gpr after shape.sourceReg = some (shape.sourceWord source (copied + 1))
  targetReg : gpr after shape.targetReg = some (shape.targetWord target (copied + 1))
  counter : gpr after shape.counterReg = some (BitVec.ofNat 64 (shape.bias + (copied + 1)))
  limit : gpr after shape.limitReg = some (BitVec.ofNat 64 (count + shape.bias))
  memory : after.σ.mem = writeLog before.σ.mem [(shape.targetStart target + 8 * copied, 8, value)]
  frame : StepFrameOut shape.writes before.σ after.σ

theorem IndexedCopyAt.advance {shape : IndexedCopyShape} {source target i : Nat}
    {words : List (BitVec 64)} {initial c d : Config}
    (region : IndexedCopyRegion shape source target words initial)
    (h : IndexedCopyAt shape source target words initial i c) (bound : i < words.length)
    (post : IndexedCopyPost shape source target words.length i words[i] c d) :
    IndexedCopyAt shape source target words initial (i + 1) d := by
  obtain ⟨image, memory⟩ := forward_copy_memory_step bound h.image region.image h.memory post.memory
  exact ⟨post.good, post.tick, image, by omega, post.pc, post.sourceReg, post.targetReg,
    post.counter, post.limit, memory,
    (h.frame.trans post.frame).widen (by intro r hr; simpa only [List.mem_append, or_self] using hr)⟩

theorem indexed_copy_loop {shape : IndexedCopyShape} {source target : Nat}
    {words : List (BitVec 64)} {initial : Config}
    (region : IndexedCopyRegion shape source target words initial)
    (body : ∀ i, Vsa.Logic.Triple (fun c => IndexedCopyAt shape source target words initial i c ∧ i < words.length)
      (IndexedCopyAt shape source target words initial (i + 1))) :
    Vsa.Logic.Triple (IndexedCopyAt shape source target words initial 0)
      (IndexedCopyAt shape source target words initial words.length) :=
  OCaml.Run.counted_loop words.length (indexedCopyIndex shape) (IndexedCopyAt shape source target words initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) body

/-- Both generated index branches share the native counted-loop fold. -/
theorem indexed_copy_run_of_branches {shape : IndexedCopyShape} {source target : Nat}
    {words : List (BitVec 64)} {initial : Config}
    (region : IndexedCopyRegion shape source target words initial)
    (more : ∀ i c, IndexedCopyAt shape source target words initial i c → i < words.length → i + 1 < words.length →
      ∃ nb after, StepsN nb c after ∧ IndexedCopyAt shape source target words initial (i + 1) after)
    (last : ∀ i c, IndexedCopyAt shape source target words initial i c → i < words.length → i + 1 = words.length →
      ∃ nb after, StepsN nb c after ∧ IndexedCopyAt shape source target words initial (i + 1) after) :
    Vsa.Logic.Triple (IndexedCopyAt shape source target words initial 0)
      (IndexedCopyAt shape source target words initial words.length) :=
  OCaml.Run.counted_loop_native words.length (indexedCopyIndex shape) (IndexedCopyAt shape source target words initial)
    (fun _ _ h => h.index region) (fun _ _ h => h.bound) more last

end OCaml.Vm.Sim
