import OCaml.Vm.Boot.Startup.StrncmpTest
import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.IndexedLoop
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- Equal nonzero prefixes, with every load inside a certified readable window. -/
structure EqualPrefix (p q : BitVec 64) (last : Nat) (byte : Nat → BitVec 8) (c : Config) : Prop where
  left : ReadWindow p (last + 1)
  right : ReadWindow q (last + 1)
  leftByte : ∀ k, k ≤ last → (c.σ.mem[p.toNat + k]?).getD 0 = byte k
  rightByte : ∀ k, k ≤ last → (c.σ.mem[q.toNat + k]?).getD 0 = byte k
  nonzero : ∀ k, k ≤ last → byte k ≠ 0#8

def strncmpIndex (p : BitVec 64) (c : Config) : Nat := ((gprGet c.σ 10).getD 0).toNat - p.toNat

structure StrncmpAt (p q ra : BitVec 64) (last k : Nat) (byte : Nat → BitVec 8) (initial c : Config) : Prop where
  leaf : LeafInput ra c
  bound : k ≤ last
  pc : PCAt 0x80040d68#64 c
  regs : GHolds c.σ (strncmpTestInput (nameCursor p k) (nameCursor q k) (nameCursor p last) (byte k))
  memory : c.σ.mem = initial.σ.mem
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [10, 11, 12, 14, 15], gprReg n ≠ r) →
    (∀ x ∈ noiseRegs, (x == r) = false) → c.σ.regs.get? r = initial.σ.regs.get? r

theorem StrncmpAt.index {p q ra last k byte initial c} (region : ReadWindow p (last + 1))
    (h : StrncmpAt p q ra last k byte initial c) : strncmpIndex p c = k := by
  have cursor := gholds_lookup (n := 10) _ h.regs (by rfl)
  simp only [strncmpIndex, cursor, Option.getD_some, nameCursor_nat region h.bound]
  omega

/-- One equal-byte iteration combines the bounded test with the next two loads. -/
theorem strncmp_iteration {p q ra last k byte initial c} (data : EqualPrefix p q last byte initial)
    (h : StrncmpAt p q ra last k byte initial c) (less : k < last) :
    ∃ d, Steps c d ∧ StrncmpAt p q ra last (k + 1) byte initial d := by
  have different : nameCursor p k ≠ nameCursor p last := by
    intro eq
    have natEq := congrArg BitVec.toNat eq
    rw [nameCursor_nat data.left h.bound, nameCursor_nat data.left (Nat.le_refl _)] at natEq
    omega
  obtain ⟨mid, testRun, tested⟩ := (strncmp_test c _ _ _ ra (byte k) false h.leaf h.regs
    (by simp [different])).run c ⟨h.pc, rfl⟩
  have midLeaf : LeafInput ra mid := ⟨tested.good, tested.image, tested.minstret,
    (tested.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, tested.tick⟩
  have midRegs : GHolds mid.σ (strncmpNextInput (nameCursor p k) (nameCursor q (k + 1)) (nameCursor p last) (byte k)) := by
    refine ⟨tested.result, ?_, gholds_lookup (n := 12) _ tested.regs (by rfl),
      gholds_lookup (n := 15) _ tested.regs (by rfl), trivial⟩
    have next := gholds_lookup (n := 11) _ tested.regs (by rfl)
    rw [nameCursor_next] at next
    exact next
  have mem : mid.σ.mem = initial.σ.mem := tested.memory.trans h.memory
  have left : ReadWindow (nameCursor p k + 1#64) 1 := by
    rw [nameCursor_next]; exact name_window data.left (by omega)
  have pinL : (mid.σ.mem[(nameCursor p k + 1#64).toNat]?).getD 0 = byte (k + 1) := by
    rw [mem, nameCursor_next, nameCursor_nat data.left (by omega)]
    exact data.leftByte _ (by omega)
  have pinR : (mid.σ.mem[(nameCursor q (k + 1)).toNat]?).getD 0 = byte (k + 1) := by
    rw [mem, nameCursor_nat data.right (by omega)]
    exact data.rightByte _ (by omega)
  obtain ⟨after, nextRun, post⟩ := (strncmp_next mid _ _ _ ra (byte k) (byte (k + 1)) midLeaf midRegs
    (data.nonzero k h.bound) left (name_window data.right (by omega)) pinL pinR).run mid ⟨tested.pc, rfl⟩
  refine ⟨after, testRun.trans nextRun, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans midLeaf.raReg, midLeaf.aligned, post.tick⟩
    bound := by omega
    pc := post.pc
    regs := ?_
    memory := post.memory.trans mem
    output := post.output.trans (tested.output.trans h.output)
    frame := ?_ }⟩
  · refine ⟨?_, gholds_lookup (n := 11) _ post.regs (by rfl),
      gholds_lookup (n := 12) _ post.regs (by rfl), gholds_lookup (n := 15) _ post.regs (by rfl),
      gholds_lookup (n := 14) _ post.regs (by rfl), trivial⟩
    have result : gprGet after.σ 10 = some (nameCursor p k + 1#64) := post.result
    rw [nameCursor_next] at result
    exact result
  · intro r outside noise
    exact (post.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise).trans
      ((tested.frame r (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise).trans (h.frame r outside noise))

/-- Fold comparison of the entire bounded prefix using the observed left cursor. -/
theorem strncmp_loop {p q ra last byte} (initial : Config) (data : EqualPrefix p q last byte initial) :
    Triple (StrncmpAt p q ra last 0 byte initial) (StrncmpAt p q ra last last byte initial) :=
  indexed_loop (strncmpIndex p) last 0 _ (fun _ _ h => h.bound)
    (fun _ _ h => h.index data.left) (fun _ _ h hk => strncmp_iteration data h hk)
end OCaml.Vm.Boot.Startup
