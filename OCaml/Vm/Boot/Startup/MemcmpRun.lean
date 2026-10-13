import OCaml.Vm.Boot.Startup.MemcmpSteps
import OCaml.Vm.Boot.Startup.StrchrMiss
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- `memcmp`'s registers. -/
def memcmpWrites : List Nat := [13, 12, 15, 14, 10, 11]

/-- The byte loop after `k` equal pairs. -/
structure MemcmpAt (p q : BitVec 64) (n : Nat) (ra : BitVec 64) (start : Config) (k : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  bound : 1 ≤ k ∧ k ≤ n
  pc : PCAt 0x800406bc#64 c
  regs : GHolds c.σ [(12, nameCursor p n), (10, nameCursor p k), (11, nameCursor q k)]
  memory : c.σ.mem = start.σ.mem
  output : c.σ.sailOutput = start.σ.sailOutput
  frame : ∀ r : Register, (∀ m ∈ memcmpWrites, gprReg m ≠ r) →
    (∀ x ∈ noiseRegs, (x == r) = false) → c.σ.regs.get? r = start.σ.regs.get? r
  present : GprPresent c.σ

def memcmpIndex (p : BitVec 64) (c : Config) : Nat := ((gprGet c.σ 10).getD 0).toNat - p.toNat

/-- `memcmp` returned 0. -/
structure MemcmpEqual (ra : BitVec 64) (before after : Config) : Prop extends LeafInput ra after where
  pc : PCAt ra after
  result : gprGet after.σ 10 = some 0#64
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ m ∈ memcmpWrites, gprReg m ≠ r) →
    (∀ x ∈ noiseRegs, (x == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent after.σ

/-- `memcmp(p, q, n)` over `n ≤ 7` equal byte pairs. -/
theorem memcmp_equal (c : Config) (ra p q : BitVec 64) (n : Nat) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, p), (11, q), (12, BitVec.ofNat 64 n), (1, ra)]) (present : GprPresent c.σ)
    (lo : 1 ≤ n) (hi : n ≤ 7) (wp : ReadWindow p (n + 1)) (wq : ReadWindow q (n + 1))
    (same : ∀ k, k < n → (c.σ.mem[p.toNat + k]?).getD 0 = (c.σ.mem[q.toNat + k]?).getD 0) :
    FnSummary 0x80040698#64 (fun d => d = c) (MemcmpEqual ra c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have pk (k : Nat) (hk : k ≤ n) := nameCursor_nat (k := k) wp hk
  have qk (k : Nat) (hk : k ≤ n) := nameCursor_nat (k := k) wq hk
  -- the first pair
  obtain ⟨a, run1, front⟩ := (memcmp_front c ra p q n ((c.σ.mem[p.toNat]?).getD 0) leaf
    ⟨regs.1, regs.2.1, regs.2.2.1, trivial⟩ lo hi (name_window wp (Nat.zero_le _) |> fun w => by simpa [nameCursor] using w)
    (name_window wq (Nat.zero_le _) |> fun w => by simpa [nameCursor] using w) rfl
    (by simpa using (same 0 lo).symm)).run c ⟨pc, rfl⟩
  have start : MemcmpAt p q n ra c 1 a := {
    leaf := ⟨front.good, front.image, front.minstret,
      (front.frame .x1 (by decide) (by decide)).trans regs.2.2.2.1, leaf.aligned, front.tick⟩
    bound := ⟨Nat.le_refl _, lo⟩
    pc := front.pc
    regs := ⟨gholds_lookup (n := 12) _ front.regs (by rfl), gholds_lookup (n := 10) _ front.regs (by rfl),
      gholds_lookup (n := 11) _ front.regs (by rfl), trivial⟩
    memory := front.memory
    output := front.output
    frame := fun r outside noise => front.frame r (fun m hm => outside m hm) noise
    present := front.present present (by decide) (by simp only [keysG]; decide) }
  -- the remaining pairs
  have loop : Triple (MemcmpAt p q n ra c 1) (MemcmpAt p q n ra c n) := by
    apply indexed_loop (memcmpIndex p) n 1 _ (fun _ _ h => h.bound.2)
    · intro k d h
      simp only [memcmpIndex, gholds_lookup (n := 10) _ h.regs (by rfl), Option.getD_some, pk k h.bound.2]
      omega
    · intro k d h hk
      have differ : nameCursor p n ≠ nameCursor p k := fun e => by
        have := congrArg BitVec.toNat e
        rw [pk n (Nat.le_refl _), pk k h.bound.2] at this
        omega
      obtain ⟨e, run, post⟩ := (memcmp_step d ra p q n k ((c.σ.mem[p.toNat + k]?).getD 0) h.leaf h.regs differ
        (name_window wp (by omega)) (name_window wq (by omega)) (by rw [h.memory, pk k (by omega)])
        (by rw [h.memory, qk k (by omega)]; exact (same k hk).symm)).run d ⟨h.pc, rfl⟩
      exact ⟨e, run, {
        leaf := ⟨post.good, post.image, post.minstret,
          (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
        bound := ⟨by omega, by omega⟩
        pc := post.pc
        regs := ⟨gholds_lookup (n := 12) _ post.regs (by rfl), gholds_lookup (n := 10) _ post.regs (by rfl),
          gholds_lookup (n := 11) _ post.regs (by rfl), trivial⟩
        memory := post.memory.trans h.memory
        output := post.output.trans h.output
        frame := fun r outside noise => (post.frame r (fun m hm => outside m (by
          simp only [memcmpWrites, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)) noise).trans
          (h.frame r outside noise)
        present := post.present h.present (by decide) (by simp only [keysG]; decide) }⟩
  obtain ⟨d, run2, at_n⟩ := loop a start
  obtain ⟨e, run3, done⟩ := (memcmp_done d ra p n at_n.leaf
    ⟨at_n.regs.1, at_n.regs.2.1, at_n.leaf.raReg, trivial⟩).run d ⟨at_n.pc, rfl⟩
  exact ⟨e, run1.trans (run2.trans run3), {
    toLeafInput := ⟨done.good, done.image, done.minstret, gholds_lookup (n := 1) _ done.regs (by rfl),
      leaf.aligned, done.tick⟩
    pc := done.pc
    result := gholds_lookup (n := 10) _ done.regs (by rfl)
    memory := done.memory.trans at_n.memory
    output := done.output.trans at_n.output
    frame := fun r outside noise => (done.frame r (fun m hm => outside m (by
      simp only [memcmpWrites, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)) noise).trans
      (at_n.frame r outside noise)
    present := done.present at_n.present (by decide) (by simp only [keysG]; decide) }⟩
end OCaml.Vm.Boot.Startup
