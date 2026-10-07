import OCaml.Vm.Primitives.Named.NamedHash
import OCaml.Vm.Primitives.Named.Umoddi3Call

/-!
# `caml_named_value` up to the bucket

The prologue saves `s1`, `ra`, `s0` in a 32-byte frame and tests the name's
first byte. A nonempty name runs the hash loop (`hash_loop`) and
`__umoddi3(h, 13)` (`umoddi3_summary`); the empty name skips both (its hash
is 0). Either way the function reaches the bucket load at `0x80021550` with
`a0 = hash % 13` (`Bucketed`).
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim

/-- The prologue's three saves. -/
def saveLog (sp ra s0 s1 : BitVec 64) : List WEntry :=
  [((sp - 32#64 + 8#64).toNat, 8, s1), ((sp - 32#64 + 24#64).toNat, 8, ra), ((sp - 32#64 + 16#64).toNat, 8, s0)]

/-- **A call of `caml_named_value(name)`**: the caller's registers, the
32-byte frame below `sp`, the name as a C string apart from the frame. -/
structure LookupInput (ra sp a s0 s1 : BitVec 64) (name : List (BitVec 8)) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x800214fc#64 c
  stack : gprGet c.σ 2 = some sp
  arg : gprGet c.σ 10 = some a
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  slot8 : WriteWindow (sp - 32#64 + 8#64) 8
  slot24 : WriteWindow (sp - 32#64 + 24#64) 8
  slot16 : WriteWindow (sp - 32#64 + 16#64) 8
  named : NameAt c.σ.mem a name
  apart : ∀ i, i ≤ name.length → OutLRange (saveLog sp ra s0 s1) (a + BitVec.ofNat 64 i).toNat 1
  image : ImageOutside (saveLog sp ra s0 s1)

/-- At the bucket load: `a0 = hash % 13`, `s1 = name`, the frame saved. -/
structure Bucketed (before : Config) (ra sp a s0 s1 : BitVec 64) (name : List (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  link : ∃ r : BitVec 64, gprGet c.σ 1 = some r ∧ r.toNat % 4 = 0
  pc : PCAt 0x80021550#64 c
  index : gprGet c.σ 10 = some (BitVec.ofNat 64 ((hashBytes name).toNat % 13))
  name : gprGet c.σ 9 = some a
  stack : gprGet c.σ 2 = some (sp + 18446744073709551584#64)
  memory : c.σ.mem = writeLog before.σ.mem (saveLog sp ra s0 s1)
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 5, 9, 10, 11, 12, 13, 14, 15] → gprGet c.σ n = gprGet before.σ n
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

theorem zext_low (h : BitVec 32) : BitVec.signExtend 64 h <<< 32 >>> 32 = h.zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  rcases Nat.lt_or_ge i 32 with h32 | h32
  · have : 32 + i < 64 := by omega
    simp [h32, hi, this]
  · have : ¬ (32 + i < 32) := by omega
    simp [this, BitVec.getLsbD_of_ge h i h32]
    intro _ _ _; omega

theorem mod13 (h : BitVec 32) : h.zeroExtend 64 % 13#64 = BitVec.ofNat 64 (h.toNat % 13) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- The name survives the prologue's saves. -/
theorem NameAt.saved {m : Std.ExtHashMap Nat (BitVec 8)} {a : BitVec 64} {name : List (BitVec 8)}
    {log : List WEntry} (h : NameAt m a name)
    (apart : ∀ i, i ≤ name.length → OutLRange log (a + BitVec.ofNat 64 i).toNat 1) :
    NameAt (writeLog m log) a name := by
  have keep : ∀ i, i ≤ name.length →
      ((writeLog m log)[(a + BitVec.ofNat 64 i).toNat]?).getD 0 = (m[(a + BitVec.ofNat 64 i).toNat]?).getD 0 :=
    fun i hi => by rw [writeLog_out _ _ _ (outL_of_range (apart i hi) (Nat.le_refl _) (by omega))]
  exact ⟨fun i hi => (keep i (by omega)).trans (h.bytes i hi), h.nonzero,
    (keep _ (Nat.le_refl _)).trans h.nul, h.window⟩

/-- **A nonempty name to the bucket**: prologue, hash loop, `% 13`. -/
theorem front_nonempty {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    (h : LookupInput ra sp a s0 s1 name c) (ne : 0 < name.length) :
    ∃ d, Steps c d ∧ Bucketed c ra sp a s0 s1 name d := by
  -- the prologue
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  have r8 := regsAt_of h.saved0
  have r9 := regsAt_of h.saved1
  have r10 := regsAt_of h.arg
  have logEq : proLog (regsAt c) (pro_loads c.σ.mem (regsAt c)) = saveLog sp ra s0 s1 := by
    simp only [proLog, saveLog, r1, r2, r8, r9]
  have first : pro_loads c.σ.mem (regsAt c) = [[name[0]]] := by
    simp only [pro_loads, r10]
    rw [show a = a + BitVec.ofNat 64 0 by simp, h.named.bytes 0 ne]
  have leaf0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have regs0 : GHolds c.σ (pro_input (regsAt c)) := by
    simp only [pro_input, GHolds, r1, r2, r8, r9, r10]
    exact ⟨h.leaf.raReg, h.stack, h.saved0, h.saved1, h.arg, trivial⟩
  have nz := h.named.nonzero 0 ne
  obtain ⟨c1, run1, p1⟩ := (pro_fast c (regsAt c) leaf0 regs0 (by rw [r2]; exact h.slot8)
    (by rw [r2]; exact h.slot24) (by rw [r2]; exact h.slot16)
    (by rw [r10]; simpa using h.named.window 0 (Nat.zero_le _))
    (by
      rw [logEq, r10]
      have := h.apart 0 (Nat.zero_le _)
      simp only [saveLog, List.take] at this ⊢
      simpa using this)
    (by rw [logEq]; exact h.image)
    (by
      rw [first]
      simp only [List.getD_cons_zero, guardB, bytesVal]
      simp [zero_extend, Sail.BitVec.zeroExtend]
      intro e; apply nz; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e; have lt := (name[0]).isLt; simp at this ⊢; omega)).run c ⟨h.pc, rfl⟩
  have o1 := p1.regs
  rw [first] at o1
  simp only [pro_regs, GHolds, r1, r2, r8, r10] at o1
  obtain ⟨c1_9, c1_14, c1_2, c1_1, c1_8, c1_10, -⟩ := o1
  -- the hash loop's entry
  have regs1 : GHolds c1.σ (start_input (regsAt c1)) := by
    simp only [start_input, GHolds, regsAt_of c1_10]; exact ⟨c1_10, trivial⟩
  have leaf1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of c1_1]; exact ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩
  obtain ⟨c2, run2, p2⟩ := (start_fast c1 (regsAt c1) leaf1 regs1).run c1 ⟨p1.pc, rfl⟩
  have o2 := p2.regs
  simp only [start_regs, GHolds, regsAt_of c1_10] at o2
  obtain ⟨c2_10, c2_13, -⟩ := o2
  have m2 : c2.σ.mem = writeLog c.σ.mem (saveLog sp ra s0 s1) := by
    rw [p2.memory, wl_nil, p1.memory, logEq]
  have named2 : NameAt c2.σ.mem a name := by rw [m2]; exact h.named.saved h.apart
  have at0 : HashAt c2 ra a name 0 c2 :=
    { leaf := ⟨p2.good, p2.image, p2.minstret,
        (p2.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans c1_1, h.leaf.aligned, p2.tick⟩
      pc := p2.pc, bound := ne
      cursor := by rw [c2_13]; simp
      byte := (p2.gpr_frame (by decide) 14 (by decide) (by decide) (by decide)).trans c1_14
      hash := by rw [c2_10]; rfl
      memory := rfl, output := rfl, frame := fun _ _ _ _ => rfl, htif := rfl }
  obtain ⟨c3, run3, p3⟩ := hash_loop named2 (name.length - 1) 0 c2 (by omega) at0
  -- h % 13
  have leaf3 : LeafInput (regsAt c3 1) c3 := by rw [regsAt_of p3.leaf.raReg]; exact p3.leaf
  have regs3 : GHolds c3.σ (mod_input (regsAt c3)) := by
    simp only [mod_input, GHolds, regsAt_of p3.leaf.raReg, regsAt_of p3.hash]
    exact ⟨p3.leaf.raReg, p3.hash, trivial⟩
  obtain ⟨c4, run4, p4⟩ := (mod_fast c3 (regsAt c3) leaf3 regs3).run c3 ⟨p3.pc, rfl⟩
  have args : GHolds c4.σ [(10, (hashBytes name).zeroExtend 64), (11, 13#64)] := by
    apply holds_project p4.regs
    simp [mod_regs, lookupG, regsAt_of p3.hash, zext_low]
  obtain ⟨c5, run5, p5⟩ := (call_registers_summary mod_call_shape mod_call_decode c4 (mod_call_pins p4.image)
    p4.good p4.image p4.tick p4.minstret _ args (by change KeysOK [10, 11]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl).run c4 ⟨p4.pc, rfl⟩
  have div : Udivdi3Input ((hashBytes name).zeroExtend 64) 13#64 0x80021550#64 c5 :=
    { good := p5.good, image := p5.image, minstret := p5.minstret
      raReg := gholds_lookup (n := 1) _ p5.regs rfl, aligned := by decide, tick := p5.tick
      left := gholds_lookup (n := 10) _ p5.regs rfl, right := gholds_lookup (n := 11) _ p5.regs rfl
      nonzero := by decide }
  obtain ⟨c6, run6, p6⟩ := (Umoddi3.umoddi3_summary div).run c5
    ⟨by have := p5.pc; rw [show mod_call.target = 0x800372e8#64 from by decide] at this; exact this, rfl⟩
  have keep : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 5, 9, 10, 11, 12, 13, 14, 15] → gprGet c6.σ n = gprGet c.σ n := by
    intro n lo hi out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    exact (p6.frame n lo hi (by simp [Umoddi3.umodWrites]; omega)).trans
      ((p5.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p4.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p3.frame n lo hi (by simp; omega)).trans
      ((p2.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      (p1.gpr_frame (by decide) n lo hi (by simp; omega))))))
  refine ⟨c6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), ?_⟩
  exact
    { good := p6.good, image := p6.image, minstret := p6.minstret, tick := p6.tick
      link := ⟨_, p6.link, by decide⟩
      pc := p6.pc
      index := by have := p6.result; rw [mod13] at this; exact this
      name := (p6.frame 9 (by decide) (by decide) (by decide)).trans
        ((p5.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        ((p4.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        ((p3.frame 9 (by decide) (by decide) (by decide)).trans
        ((p2.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans c1_9))))
      stack := (p6.frame 2 (by decide) (by decide) (by decide)).trans
        ((p5.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans
        ((p4.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans
        ((p3.frame 2 (by decide) (by decide) (by decide)).trans
        ((p2.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans c1_2))))
      memory := by rw [p6.memory, p5.memory, p4.memory, wl_nil, p3.memory, m2]
      output := by rw [p6.output, p5.output, p4.output, p3.output, p2.output, p1.output]
      frame := keep
      htifIdle := by
        rw [p6.htifIdle, p5.frame _ (by decide) (by decide), p4.frame _ (by decide) (by decide), p3.htif,
          p2.frame _ (by decide) (by decide), p1.frame _ (by decide) (by decide)] }

/-- **The empty name to the bucket**: the prologue sees the terminator first; the hash is 0. -/
theorem front_empty {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    (h : LookupInput ra sp a s0 s1 name c) (e : name.length = 0) :
    ∃ d, Steps c d ∧ Bucketed c ra sp a s0 s1 name d := by
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  have r8 := regsAt_of h.saved0
  have r9 := regsAt_of h.saved1
  have r10 := regsAt_of h.arg
  have nil : name = [] := List.eq_nil_of_length_eq_zero e
  have logEq : proEmptyLog (regsAt c) (proEmpty_loads c.σ.mem (regsAt c)) = saveLog sp ra s0 s1 := by
    simp only [proEmptyLog, saveLog, r1, r2, r8, r9]
  have first : proEmpty_loads c.σ.mem (regsAt c) = [[0#8]] := by
    have := h.named.nul
    simp only [e] at this
    simp only [proEmpty_loads, r10]
    rw [show a = a + BitVec.ofNat 64 0 by simp, this]
  have leaf0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have regs0 : GHolds c.σ (proEmpty_input (regsAt c)) := by
    simp only [proEmpty_input, GHolds, r1, r2, r8, r9, r10]
    exact ⟨h.leaf.raReg, h.stack, h.saved0, h.saved1, h.arg, trivial⟩
  obtain ⟨c1, run1, p1⟩ := (proEmpty_fast c (regsAt c) leaf0 regs0 (by rw [r2]; exact h.slot8)
    (by rw [r2]; exact h.slot24) (by rw [r2]; exact h.slot16)
    (by rw [r10]; simpa using h.named.window 0 (Nat.zero_le _))
    (by
      rw [logEq, r10]
      have := h.apart 0 (Nat.zero_le _)
      simp only [saveLog, List.take] at this ⊢
      simpa using this)
    (by rw [logEq]; exact h.image)
    (by rw [first]; decide)).run c ⟨h.pc, rfl⟩
  have o1 := p1.regs
  rw [first] at o1
  simp only [proEmpty_regs, GHolds, r1, r2, r8, r10] at o1
  obtain ⟨c1_9, -, c1_2, c1_1, -, c1_10, -⟩ := o1
  have regs1 : GHolds c1.σ (empty_input (regsAt c1)) := by
    simp only [empty_input, GHolds, regsAt_of c1_10]; exact ⟨c1_10, trivial⟩
  have leaf1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of c1_1]; exact ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩
  obtain ⟨c2, run2, p2⟩ := (empty_fast c1 (regsAt c1) leaf1 regs1).run c1 ⟨p1.pc, rfl⟩
  have o2 := p2.regs
  simp only [empty_regs, GHolds] at o2
  refine ⟨c2, run1.trans run2, ?_⟩
  exact
    { good := p2.good, image := p2.image, minstret := p2.minstret, tick := p2.tick
      link := ⟨ra, (p2.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans c1_1, h.leaf.aligned⟩
      pc := p2.pc
      index := by rw [o2.1, nil]; rfl
      name := (p2.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans c1_9
      stack := (p2.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans c1_2
      memory := by rw [p2.memory, wl_nil, p1.memory, logEq]
      output := by rw [p2.output, p1.output]
      frame := fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (p2.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          (p1.gpr_frame (by decide) n lo hi (by simp; omega))
      htifIdle := by rw [p2.frame _ (by decide) (by decide), p1.frame _ (by decide) (by decide)] }

/-- **`caml_named_value` to the bucket load**, for any name. -/
theorem front {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    (h : LookupInput ra sp a s0 s1 name c) : ∃ d, Steps c d ∧ Bucketed c ra sp a s0 s1 name d := by
  rcases Nat.eq_zero_or_pos name.length with e | ne
  · exact front_empty h e
  · exact front_nonempty h ne

end OCaml.Vm.Primitives.Named.NamedValue
