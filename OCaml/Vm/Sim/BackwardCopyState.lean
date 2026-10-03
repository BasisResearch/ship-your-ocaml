import OCaml.Vm.Sim.BackwardCopyArithmetic
import OCaml.Vm.Sim.ReverseCopyLog
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore
import Vsa.Sim.FrameWriteSet
import Vsa.Sim.DeriveLoop

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

def backwardWrites : List Register := [Register.x9, Register.x13, Register.x14, Register.x15] ++ noiseRegs

/-- Static geometry and the original source snapshot for a backward word copy.
Destination may overlap source, provided it begins at or above it. -/
structure BackwardCopyRegion (source target : Nat) (words : List (BitVec 64)) (initial : Config) : Prop where
  room : 8 ≤ source
  direction : source ≤ target
  small : words.length < 2^31
  sourceUpper : source + 8 * words.length ≤ 0x100000000
  targetUpper : target + 8 * words.length ≤ 0x100000000
  reads : ∀ i, i < words.length → RamReadAt (source + 8 * i) 8
  writes : ∀ i, i < words.length → RamWriteAt (target + 8 * i) 8
  image : ImageOutside (reverseCopyLog target words 0)
  snapshot : ∀ i w, words[i]? = some w → word initial (source + 8 * i) = w

/-- All loop observations, including the exhausted state after its last branch. -/
structure BackwardCopyAt (source target : Nat) (words : List (BitVec 64)) (initial : Config)
    (remaining : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  image : ExecutableImage c
  bound : remaining ≤ words.length
  pc : pcOf c = some (if 0 < remaining then 0x80002ab8#64 else 0x80002ad0#64)
  sourceReg : gpr c 9 = some (BitVec.ofNat 64 (backwardCursor source remaining))
  targetReg : gpr c 15 = some (BitVec.ofNat 64 (backwardCursor target remaining))
  counter : gpr c 14 = some (backwardCounter remaining)
  sentinel : gpr c 12 = some (-(1#64))
  memory : c.σ.mem = writeLog initial.σ.mem (reverseCopyLog target words remaining)
  frame : StepFrameOut backwardWrites initial.σ c.σ

/-- The source cursor determines the remaining count, including the zero exit. -/
def backwardRemaining (source : Nat) (c : Config) : Nat :=
  (((gpr c 9).getD 0).toNat - (source - 8)) / 8

theorem BackwardCopyAt.index {source target remaining : Nat} {words : List (BitVec 64)} {initial c : Config}
    (region : BackwardCopyRegion source target words initial)
    (h : BackwardCopyAt source target words initial remaining c) :
    backwardRemaining source c = remaining := by
  have small : backwardCursor source remaining < 2^64 := by
    have bound := h.bound
    have upper := region.sourceUpper
    unfold backwardCursor
    omega
  simp only [backwardRemaining, h.sourceReg, Option.getD_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt small]
  unfold backwardCursor
  omega

/-- Extract an unread word from the original snapshot despite overlapping writes. -/
theorem BackwardCopyAt.read {source target remaining i : Nat} {words : List (BitVec 64)}
    {initial c : Config} {value : BitVec 64} (region : BackwardCopyRegion source target words initial)
    (h : BackwardCopyAt source target words initial remaining c) (unread : i < remaining)
    (selected : words[i]? = some value) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (bytesT8 c.σ.mem (source + 8 * i)) = value :=
  (word_read_writeLog_out (reverse_copy_source_outside region.direction unread) h.memory).trans
    (region.snapshot i value selected)

/-- Each loop store is a member of the complete image-separated write log. -/
theorem BackwardCopyRegion.entry {source target i : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : BackwardCopyRegion source target words initial) (bound : i < words.length) :
    (target + 8 * i, 8, words[i]) ∈ reverseCopyLog target words 0 := by
  simp only [reverseCopyLog, List.drop_zero, List.mem_reverse]
  exact List.mem_iff_getElem.mpr ⟨i, by rw [value_log_length]; exact bound,
    value_log_getElem target words i bound⟩

/-- Observations exported by either generated branch of a copy iteration. -/
structure BackwardCopyPost (source target remaining : Nat) (value : BitVec 64)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : pcOf after = some (if 0 < remaining then 0x80002ab8#64 else 0x80002ad0#64)
  sourceReg : gpr after 9 = some (BitVec.ofNat 64 (backwardCursor source remaining))
  targetReg : gpr after 15 = some (BitVec.ofNat 64 (backwardCursor target remaining))
  counter : gpr after 14 = some (backwardCounter remaining)
  sentinel : gpr after 12 = some (-(1#64))
  memory : after.σ.mem = writeLog before.σ.mem [(target + 8 * remaining, 8, value)]
  frame : StepFrameOut backwardWrites before.σ after.σ

/-- Append one high-to-low store and preserve the shared loop invariant. -/
theorem BackwardCopyAt.advance {source target i : Nat} {words : List (BitVec 64)} {initial c d : Config}
    (region : BackwardCopyRegion source target words initial)
    (h : BackwardCopyAt source target words initial (i + 1) c)
    (bound : i < words.length) (post : BackwardCopyPost source target i words[i] c d) :
    BackwardCopyAt source target words initial i d := by
  have entry := region.entry bound
  have image := imageOutside_sublist (List.singleton_sublist.mpr entry) region.image
  refine ⟨post.good, post.tick, image_of_writeLog h.image image post.memory, by omega,
    post.pc, post.sourceReg, post.targetReg, post.counter, post.sentinel, ?_, ?_⟩
  · rw [post.memory, h.memory, reverse_copy_log_step target words i bound, writeLog_append]
  · exact (h.frame.trans post.frame).widenChecked (allowed := backwardWrites) (by decide)

/-- Fold the reverse-copy invariant using a supplied generated one-iteration proof. -/
theorem backward_copy_loop {source target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : BackwardCopyRegion source target words initial)
    (body : ∀ i, Vsa.Logic.Triple (BackwardCopyAt source target words initial (i + 1))
      (BackwardCopyAt source target words initial i)) :
    Vsa.Logic.Triple (BackwardCopyAt source target words initial words.length)
      (BackwardCopyAt source target words initial 0) := by
  let I := fun c => BackwardCopyAt source target words initial (backwardRemaining source c) c
  let B := fun c => 0 < backwardRemaining source c
  have iteration : ∀ n, Vsa.Logic.Triple (fun c => I c ∧ B c ∧ backwardRemaining source c = n)
      (fun c => I c ∧ backwardRemaining source c < n) := by
    intro n c ⟨h, positive, rank⟩
    have positive' : 0 < backwardRemaining source c := positive
    have count : backwardRemaining source c - 1 + 1 = backwardRemaining source c := by omega
    obtain ⟨d, steps, post⟩ := body (backwardRemaining source c - 1) c (by rw [count]; exact h)
    have index := post.index region
    refine ⟨d, steps, ?_, ?_⟩
    · change BackwardCopyAt source target words initial (backwardRemaining source d) d
      rw [index]; exact post
    · rw [index]; omega
  apply (loopFromBody (backwardRemaining source) iteration).conseq
  · intro c h
    change BackwardCopyAt source target words initial (backwardRemaining source c) c
    rw [h.index region]; exact h
  · intro c ⟨h, stop⟩
    have zero : backwardRemaining source c = 0 := by dsimp [B] at stop; omega
    simpa only [I, zero] using h

end OCaml.Vm.Sim
