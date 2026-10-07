import OCaml.Vm.Primitives.Named.NamedValue
import OCaml.Vm.Primitives.LibraryEffects

/-!
# `hash_value_name`'s byte loop in `caml_named_value`

`h = h * 19 + *name` over the name's bytes in 32-bit arithmetic, kept
sign-extended in `a0` by the word instructions (`slliw`/`addw`/`subw`). The
loop's generated blocks are `hashMore` (another byte) and `hashEnd` (the
terminator); `hash_loop` folds them by induction on the bytes left.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- `hash_value_name`'s 32-bit accumulator over `bytes` (unsigned `char`). -/
def hashBytes (bytes : List (BitVec 8)) : BitVec 32 :=
  bytes.foldl (fun h b => h * 19#32 + b.zeroExtend 32) 0

theorem hashBytes_snoc (bytes : List (BitVec 8)) (b : BitVec 8) :
    hashBytes (bytes ++ [b]) = hashBytes bytes * 19#32 + b.zeroExtend 32 := by
  simp [hashBytes, List.foldl_append]

theorem low_signExtend (h : BitVec 32) : BitVec.extractLsb 31 0 (BitVec.signExtend 64 h) = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

/-- The hash block's `a0`: one step of `h * 19 + byte` on the low word. -/
theorem hash_step (h : BitVec 32) (b : BitVec 8) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (bytesVal .lbu [b]) + BitVec.extractLsb 31 0
      (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0
        (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0
          (BitVec.signExtend 64 h) <<< 2)) + BitVec.extractLsb 31 0 (BitVec.signExtend 64 h))) <<< 2)) +
        -BitVec.extractLsb 31 0 (BitVec.signExtend 64 h)))) =
    BitVec.signExtend 64 (h * 19#32 + b.zeroExtend 32) := by
  simp only [low_signExtend]
  congr 1
  have eb : BitVec.extractLsb 31 0 (bytesVal .lbu [b]) = b.zeroExtend 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [bytesVal, zero_extend, Sail.BitVec.zeroExtend]
  rw [eb]
  bv_omega

/-- The name as a C string at `a`: its bytes, none zero, then the
terminator, each readable. -/
structure NameAt (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (name : List (BitVec 8)) : Prop where
  bytes : ∀ i (hi : i < name.length), (m[(a + BitVec.ofNat 64 i).toNat]?).getD 0 = name[i]
  nonzero : ∀ i (hi : i < name.length), name[i] ≠ 0#8
  nul : (m[(a + BitVec.ofNat 64 name.length).toNat]?).getD 0 = 0#8
  window : ∀ i, i ≤ name.length → ReadWindow (a + BitVec.ofNat 64 i) 1

/-- At the hash loop's head, about to fold byte `i`. -/
structure HashAt (c0 : Config) (ra a : BitVec 64) (name : List (BitVec 8)) (i : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x80021520#64 c
  bound : i < name.length
  cursor : gprGet c.σ 13 = some (a + BitVec.ofNat 64 i)
  byte : gprGet c.σ 14 = some (bytesVal .lbu [name[i]])
  hash : gprGet c.σ 10 = some (BitVec.signExtend 64 (hashBytes (name.take i)))
  memory : c.σ.mem = c0.σ.mem
  output : c.σ.sailOutput = c0.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 13, 14, 15] → gprGet c.σ n = gprGet c0.σ n

/-- The loop has hashed the whole name. -/
structure HashDone (c0 : Config) (ra : BitVec 64) (name : List (BitVec 8)) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x80021540#64 c
  hash : gprGet c.σ 10 = some (BitVec.signExtend 64 (hashBytes name))
  memory : c.σ.mem = c0.σ.mem
  output : c.σ.sailOutput = c0.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 13, 14, 15] → gprGet c.σ n = gprGet c0.σ n

/-- The registers at `c` as the blocks' symbolic inputs. -/
def regsAt (c : Config) : Nat → BitVec 64 := fun k => (gprGet c.σ k).getD 0

theorem regsAt_of {c : Config} {k : Nat} {v : BitVec 64} (h : gprGet c.σ k = some v) : regsAt c k = v := by
  simp only [regsAt, h, Option.getD_some]

theorem take_succ_eq {name : List (BitVec 8)} {i : Nat} (hi : i < name.length) :
    name.take (i + 1) = name.take i ++ [name[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]; rfl

/-- One iteration: another nonzero byte. -/
theorem hash_more {c0 c : Config} {ra a : BitVec 64} {name : List (BitVec 8)} {i : Nat}
    (named : NameAt c0.σ.mem a name) (h : HashAt c0 ra a name i c) (more : i + 1 < name.length) :
    ∃ d, Steps c d ∧ HashAt c0 ra a name (i + 1) d := by
  have r13 := regsAt_of h.cursor
  have r14 := regsAt_of h.byte
  have r10 := regsAt_of h.hash
  have regs : GHolds c.σ (hashMore_input (regsAt c)) := by
    simp only [hashMore_input, GHolds]
    exact ⟨by rw [r10]; exact h.hash, by rw [r13]; exact h.cursor, by rw [r14]; exact h.byte, trivial⟩
  have next : regsAt c 13 + 1#64 = a + BitVec.ofNat 64 (i + 1) := by
    rw [r13, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; try omega
  have read : (hashMore_loads c.σ.mem (regsAt c)) = [[name[i + 1]]] := by
    simp only [hashMore_loads, next, h.memory, named.bytes (i + 1) more]
  have leaf : LeafInput (regsAt c 1) c := by
    rw [regsAt_of h.leaf.raReg]; exact h.leaf
  have ok : guardB .BNE (bytesVal .lbu ((hashMore_loads c.σ.mem (regsAt c)).getD 0 [])) (0#64) = true := by
    rw [read]
    have nz := named.nonzero (i + 1) more
    simp only [List.getD_cons_zero, guardB, bytesVal]
    simp [zero_extend, Sail.BitVec.zeroExtend]
    intro e; apply nz; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e; have lt := (name[i + 1]).isLt; simp at this ⊢; omega
  obtain ⟨d, run, post⟩ := (hashMore_fast c (regsAt c) leaf regs (by rw [next]; exact named.window _ (by omega)) ok).run c
    ⟨h.pc, rfl⟩
  have out := post.regs
  rw [read] at out
  simp only [hashMore_regs, GHolds] at out
  obtain ⟨o14, o10, o13, -, -⟩ := out
  refine ⟨d, run, ⟨⟨post.good, post.image, post.minstret, ?_, h.leaf.aligned, post.tick⟩, post.pc,
    more, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [← h.leaf.raReg]; exact post.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)
  · rw [o13, next]
  · simpa using o14
  · rw [o10, r10, r14, hash_step, take_succ_eq (by omega : i < name.length), hashBytes_snoc]
  · rw [post.memory, h.memory]; rfl
  · rw [post.output, h.output]
  · intro n lo hi out
    exact (post.gpr_frame (by decide) n lo hi out).trans (h.frame n lo hi out)

/-- The last iteration: the terminator. -/
theorem hash_end {c0 c : Config} {ra a : BitVec 64} {name : List (BitVec 8)} {i : Nat}
    (named : NameAt c0.σ.mem a name) (h : HashAt c0 ra a name i c) (last : i + 1 = name.length) :
    ∃ d, Steps c d ∧ HashDone c0 ra name d := by
  have r13 := regsAt_of h.cursor
  have r14 := regsAt_of h.byte
  have r10 := regsAt_of h.hash
  have regs : GHolds c.σ (hashEnd_input (regsAt c)) := by
    simp only [hashEnd_input, GHolds]
    exact ⟨by rw [r10]; exact h.hash, by rw [r13]; exact h.cursor, by rw [r14]; exact h.byte, trivial⟩
  have next : regsAt c 13 + 1#64 = a + BitVec.ofNat 64 name.length := by
    rw [r13, BitVec.add_assoc, ← last]; congr 1; apply BitVec.eq_of_toNat_eq; simp; try omega
  have read : (hashEnd_loads c.σ.mem (regsAt c)) = [[0#8]] := by
    simp only [hashEnd_loads, next, h.memory, named.nul]
  have leaf : LeafInput (regsAt c 1) c := by
    rw [regsAt_of h.leaf.raReg]; exact h.leaf
  have ok : guardB .BNE (bytesVal .lbu ((hashEnd_loads c.σ.mem (regsAt c)).getD 0 [])) (0#64) = false := by
    rw [read]; decide
  obtain ⟨d, run, post⟩ := (hashEnd_fast c (regsAt c) leaf regs (by rw [next]; exact named.window _ (Nat.le_refl _)) ok).run c
    ⟨h.pc, rfl⟩
  have out := post.regs
  rw [read] at out
  simp only [hashEnd_regs, GHolds] at out
  obtain ⟨-, o10, -, -, -⟩ := out
  refine ⟨d, run, ⟨⟨post.good, post.image, post.minstret, ?_, h.leaf.aligned, post.tick⟩, post.pc,
    ?_, ?_, ?_, ?_⟩⟩
  · rw [← h.leaf.raReg]; exact post.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)
  · have full : name.take (i + 1) = name := by rw [last]; exact List.take_length
    rw [o10, r10, r14, hash_step, ← hashBytes_snoc, ← take_succ_eq (by omega : i < name.length), full]
  · rw [post.memory, h.memory]; rfl
  · rw [post.output, h.output]
  · intro n lo hi out
    exact (post.gpr_frame (by decide) n lo hi out).trans (h.frame n lo hi out)

/-- **The hash loop**, from any byte to the terminator. -/
theorem hash_loop {c0 : Config} {ra a : BitVec 64} {name : List (BitVec 8)} (named : NameAt c0.σ.mem a name) :
    ∀ k i c, i + 1 + k = name.length → HashAt c0 ra a name i c → ∃ d, Steps c d ∧ HashDone c0 ra name d := by
  intro k
  induction k with
  | zero => intro i c e h; exact hash_end named h (by omega)
  | succ k ih =>
    intro i c e h
    obtain ⟨d, run, hd⟩ := hash_more named h (by omega)
    obtain ⟨d', run', done⟩ := ih (i + 1) d (by omega) hd
    exact ⟨d', run.trans run', done⟩

end OCaml.Vm.Primitives.Named.NamedValue
