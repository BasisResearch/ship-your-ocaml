import OCaml.Vm.Boot.Startup.Crt0

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- The exact memory effect of the counted crt0 zeroing loop. -/
def clearWords (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) :
    Nat → Std.ExtHashMap Nat (BitVec 8)
  | 0 => m
  | n + 1 => writeLog (clearWords m base n) [(base + 8 * n, 8, 0#64)]

theorem clearWords_below (m : Std.ExtHashMap Nat (BitVec 8)) (base n a : Nat)
    (ha : a < base) : (clearWords m base n)[a]? = m[a]? := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clearWords, writeLog_out _ _ _ (show OutL [(base + 8 * n, 8, 0#64)] a from
      ⟨Or.inl (by omega), True.intro⟩), ih]

/-- Region geometry; program contents do not occur in the loop contract. -/
structure ClearRegion (base count : Nat) : Prop where
  lower : 0x80000040 ≤ base
  htif : Layout.sym_tohost + 16 ≤ base
  upper : base + 8 * count ≤ 0x100000000
  aligned : base % 8 = 0

/-- The complete loop invariant with its explicit iteration index. -/
structure ClearAt (base count k : Nat) (initial : Config) (c : Config) : Prop where
  ready : CrtReady c
  bound : k ≤ count
  pc : PCAt 0x80000020#64 c
  cursor : gprGet c.σ 5 = some (BitVec.ofNat 64 (base + 8 * k))
  limit : gprGet c.σ 6 = some (BitVec.ofNat 64 (base + 8 * count))
  memory : c.σ.mem = clearWords initial.σ.mem base k
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    r ≠ .x5 → c.σ.regs.get? r = initial.σ.regs.get? r

def clearIndex (base : Nat) (c : Config) : Nat :=
  (((gprGet c.σ 5).getD 0).toNat - base) / 8

theorem ClearRegion.cursor_nat {base count k : Nat} (r : ClearRegion base count)
    (hk : k ≤ count) : (BitVec.ofNat 64 (base + 8 * k)).toNat = base + 8 * k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := r.upper
  omega

theorem ClearAt.index {base count k : Nat} {initial c : Config}
    (r : ClearRegion base count) (h : ClearAt base count k initial c) :
    clearIndex base c = k := by
  simp only [clearIndex, h.cursor, Option.getD_some, r.cursor_nat h.bound]
  omega

theorem ClearRegion.window {base count k : Nat} (r : ClearRegion base count)
    (hk : k < count) : WriteWindow (BitVec.ofNat 64 (base + 8 * k)) 8 := by
  have hn := r.cursor_nat (Nat.le_of_lt hk)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn]; have := r.lower; omega
  · rw [hn]; have := r.upper; omega
  · rw [hn]; have := r.htif; omega
  · rw [hn]; simp [Nat.add_mod, r.aligned]

/-- One symbolic iteration, including the loop guard and zero-store back edge. -/
theorem clear_iteration {base count k : Nat} {initial c : Config}
    (r : ClearRegion base count) (h : ClearAt base count k initial c)
    (hk : k < count) : ∃ d, Steps c d ∧ ClearAt base count (k + 1) initial d := by
  have branch : guardB .BGEU (BitVec.ofNat 64 (base + 8 * k))
      (BitVec.ofNat 64 (base + 8 * count)) = false := by
    apply bgeu_false_of_lt
    rw [r.cursor_nat h.bound, r.cursor_nat (Nat.le_refl count)]
    omega
  obtain ⟨mid, front, g⟩ := (guard_summary c _ _ false h.ready h.cursor h.limit branch).run c ⟨h.pc, rfl⟩
  have hp : gprGet mid.σ 5 = some (BitVec.ofNat 64 (base + 8 * k)) :=
    (g.frame .x5 (by decide)).trans h.cursor
  obtain ⟨d, back, b⟩ := (clear_body mid _ g.ready hp (r.window hk)
    (by rw [r.cursor_nat h.bound]; have := r.lower; omega)).run mid ⟨g.pc, rfl⟩
  refine ⟨d, front.trans back, ⟨b.ready, by omega, b.pc, ?_, ?_, ?_,
    b.output.trans (g.output.trans h.output), ?_⟩⟩
  · have cursor := b.cursor
    rw [show BitVec.ofNat 64 (base + 8 * k) + 8#64 =
        BitVec.ofNat 64 (base + 8 * (k + 1)) by
          rw [← BitVec.ofNat_add]; congr 1 <;> omega] at cursor
    exact cursor
  · exact (b.frame .x6 (by decide) (by decide)).trans
      ((g.frame .x6 (by decide)).trans h.limit)
  · rw [b.memory, g.memory, h.memory, r.cursor_nat h.bound]
    rfl
  · intro reg noise other
    exact (b.frame reg noise other).trans ((g.frame reg noise).trans (h.frame reg noise other))

/-- Fold any number of BSS words with one body proof, never a kernel replay. -/
theorem clear_loop {base count : Nat} (r : ClearRegion base count) (initial : Config) :
    Triple (ClearAt base count 0 initial) (ClearAt base count count initial) := by
  let I := fun c => ClearAt base count (clearIndex base c) initial c
  let B := fun c => clearIndex base c < count
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ count - clearIndex base c = n)
      (fun c => I c ∧ count - clearIndex base c < n) := by
    intro n c ⟨h, hk, hn⟩
    obtain ⟨d, run, post⟩ := clear_iteration r h hk
    have index := post.index r
    refine ⟨d, run, ?_, ?_⟩
    · change ClearAt base count (clearIndex base d) initial d
      rw [index]; exact post
    · rw [index]; dsimp [B] at hk; omega
  apply (loopFromBody (fun c => count - clearIndex base c) body).conseq
  · intro c h
    change ClearAt base count (clearIndex base c) initial c
    rw [h.index r]; exact h
  · intro c ⟨h, stop⟩
    have bound := h.bound
    have eq : clearIndex base c = count := by dsimp [B] at stop; omega
    simpa only [I, eq] using h

end OCaml.Vm.Boot.Startup
