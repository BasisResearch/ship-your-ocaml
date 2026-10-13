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

/-- **A copy of the hash-to-bucket code**: the hash loop's entry block at
`start` (cursor and `h = 0`), the loop (`HashCode`), the `% 13` block at
`modPc` and its `__umoddi3` call returning to `bucket`, and the empty name's
block at `empty` (hash 0, on to `bucket`). -/
structure FrontCode (call : CallInstr) (start head modPc empty bucket : BitVec 64) : Prop where
  start : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (start_input R) →
    FnSummary start (fun d => d = c)
      (WriteRegistersPost [10, 13] [] c head (0#64) (start_regs R (start_loads c.σ.mem R)))
  hash : HashCode head modPc
  mod : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (mod_input R) →
    FnSummary modPc (fun d => d = c)
      (WriteRegistersPost [10, 11] [] c call.pc (R 10 <<< 32 >>> 32) (mod_regs R (mod_loads c.σ.mem R)))
  shape : CallShape call
  decode : CallDecode call
  pins : ∀ {c : Config}, ExecutableImage c → CallPins call c
  target : call.target = 0x800372e8#64
  link : call.link = bucket
  aligned : bucket.toNat % 4 = 0
  empty : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (empty_input R) →
    FnSummary empty (fun d => d = c)
      (WriteRegistersPost [10] [] c bucket (0#64) (empty_regs R (empty_loads c.σ.mem R)))

/-- `caml_named_value`'s copy. -/
theorem frontCode :
    FrontCode mod_call 0x80021518#64 0x80021520#64 0x80021540#64 0x800215a0#64 0x80021550#64 :=
  ⟨start_fast, hashCode, mod_fast, mod_call_shape, mod_call_decode, mod_call_pins, by decide, by decide,
    by decide, empty_fast⟩

/-- The registers the hash-to-bucket code may change. -/
def hashWrites : List Nat := [1, 5, 10, 11, 12, 13, 14, 15]

/-- At the bucket load with `a0 = hash % 13`, memory and output as at `before`. -/
structure Hashed (before : Config) (bucket : BitVec 64) (name : List (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  link : ∃ r : BitVec 64, gprGet c.σ 1 = some r ∧ r.toNat % 4 = 0
  pc : PCAt bucket c
  index : gprGet c.σ 10 = some (BitVec.ofNat 64 ((hashBytes name).toNat % 13))
  memory : c.σ.mem = before.σ.mem
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ hashWrites → gprGet c.σ n = gprGet before.σ n
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- **A nonempty name from the hash loop's entry to the bucket load.** -/
theorem hashed_nonempty {call : CallInstr} {start head modPc empty bucket : BitVec 64}
    (code : FrontCode call start head modPc empty bucket) {ra a : BitVec 64} {name : List (BitVec 8)}
    {c1 : Config} (ne : 0 < name.length) (leaf : LeafInput ra c1) (pc : PCAt start c1)
    (arg : gprGet c1.σ 10 = some a) (byte : gprGet c1.σ 14 = some (bytesVal .lbu [name[0]]))
    (named : NameAt c1.σ.mem a name) :
    ∃ d, Steps c1 d ∧ Hashed c1 bucket name d := by
  have regs1 : GHolds c1.σ (start_input (regsAt c1)) := by
    simp only [start_input, GHolds, regsAt_of arg]; exact ⟨arg, trivial⟩
  have leaf1 : LeafInput (regsAt c1 1) c1 := by rw [regsAt_of leaf.raReg]; exact leaf
  obtain ⟨c2, run2, p2⟩ := (code.start c1 (regsAt c1) leaf1 regs1).run c1 ⟨pc, rfl⟩
  have o2 := p2.regs
  simp only [start_regs, GHolds, regsAt_of arg] at o2
  obtain ⟨c2_10, c2_13, -⟩ := o2
  have m2 : c2.σ.mem = c1.σ.mem := by rw [p2.memory, wl_nil]
  have named2 : NameAt c2.σ.mem a name := by rw [m2]; exact named
  have at0 : HashAt head c2 ra a name 0 c2 :=
    { leaf := ⟨p2.good, p2.image, p2.minstret,
        (p2.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans leaf.raReg, leaf.aligned, p2.tick⟩
      pc := p2.pc, bound := ne
      cursor := by rw [c2_13]; simp
      byte := (p2.gpr_frame (by decide) 14 (by decide) (by decide) (by decide)).trans byte
      hash := by rw [c2_10]; rfl
      memory := rfl, output := rfl, frame := fun _ _ _ _ => rfl, htif := rfl }
  obtain ⟨c3, run3, p3⟩ := hash_loop code.hash named2 (name.length - 1) 0 c2 (by omega) at0
  -- h % 13
  have leaf3 : LeafInput (regsAt c3 1) c3 := by rw [regsAt_of p3.leaf.raReg]; exact p3.leaf
  have regs3 : GHolds c3.σ (mod_input (regsAt c3)) := by
    simp only [mod_input, GHolds, regsAt_of p3.leaf.raReg, regsAt_of p3.hash]
    exact ⟨p3.leaf.raReg, p3.hash, trivial⟩
  obtain ⟨c4, run4, p4⟩ := (code.mod c3 (regsAt c3) leaf3 regs3).run c3 ⟨p3.pc, rfl⟩
  have args : GHolds c4.σ [(10, (hashBytes name).zeroExtend 64), (11, 13#64)] := by
    apply holds_project p4.regs
    simp [mod_regs, lookupG, regsAt_of p3.hash, zext_low]
  obtain ⟨c5, run5, p5⟩ := (call_registers_summary code.shape code.decode c4 (code.pins p4.image)
    p4.good p4.image p4.tick p4.minstret _ args (by change KeysOK [10, 11]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl).run c4 ⟨p4.pc, rfl⟩
  have div : Udivdi3Input ((hashBytes name).zeroExtend 64) 13#64 bucket c5 :=
    { good := p5.good, image := p5.image, minstret := p5.minstret
      raReg := gholds_lookup (n := 1) _ p5.regs (by simp [lookupG, code.link])
      aligned := code.aligned, tick := p5.tick
      left := gholds_lookup (n := 10) _ p5.regs rfl, right := gholds_lookup (n := 11) _ p5.regs rfl
      nonzero := by decide }
  obtain ⟨c6, run6, p6⟩ := (Umoddi3.umoddi3_summary div).run c5
    ⟨by have := p5.pc; rw [code.target] at this; exact this, rfl⟩
  refine ⟨c6, run2.trans (run3.trans (run4.trans (run5.trans run6))), ?_⟩
  exact
    { good := p6.good, image := p6.image, minstret := p6.minstret, tick := p6.tick
      link := ⟨_, p6.link, by decide⟩
      pc := p6.pc
      index := by have := p6.result; rw [mod13] at this; exact this
      memory := by rw [p6.memory, p5.memory, p4.memory, wl_nil, p3.memory, m2]
      output := by rw [p6.output, p5.output, p4.output, p3.output, p2.output]
      frame := fun n lo hi out => by
        simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (p6.frame n lo hi (by simp [Umoddi3.umodWrites]; omega)).trans
          ((p5.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          ((p4.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          ((p3.frame n lo hi (by simp; omega)).trans
          (p2.gpr_frame (by decide) n lo hi (by simp; omega)))))
      htifIdle := by
        rw [p6.htifIdle, p5.frame _ (by decide) (by decide), p4.frame _ (by decide) (by decide), p3.htif,
          p2.frame _ (by decide) (by decide)] }

/-- **The empty name from its block to the bucket load** (hash 0). -/
theorem hashed_empty {call : CallInstr} {start head modPc empty bucket : BitVec 64}
    (code : FrontCode call start head modPc empty bucket) {ra : BitVec 64} {name : List (BitVec 8)}
    {c1 : Config} (e : name.length = 0) (leaf : LeafInput ra c1) (pc : PCAt empty c1)
    (a0 : (gprGet c1.σ 10).isSome) :
    ∃ d, Steps c1 d ∧ Hashed c1 bucket name d := by
  have nil : name = [] := List.eq_nil_of_length_eq_zero e
  have c1_10 := gpr_some a0
  have regs1 : GHolds c1.σ (empty_input (regsAt c1)) := by
    simp only [empty_input, GHolds]; exact ⟨c1_10, trivial⟩
  have leaf1 : LeafInput (regsAt c1 1) c1 := by rw [regsAt_of leaf.raReg]; exact leaf
  obtain ⟨c2, run2, p2⟩ := (code.empty c1 (regsAt c1) leaf1 regs1).run c1 ⟨pc, rfl⟩
  have o2 := p2.regs
  simp only [empty_regs, GHolds] at o2
  refine ⟨c2, run2, ?_⟩
  exact
    { good := p2.good, image := p2.image, minstret := p2.minstret, tick := p2.tick
      link := ⟨ra, (p2.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans leaf.raReg, leaf.aligned⟩
      pc := p2.pc
      index := by rw [o2.1, nil]; rfl
      memory := by rw [p2.memory, wl_nil]
      output := p2.output
      frame := fun n lo hi out => p2.gpr_frame (by decide) n lo hi (fun m => out (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m; subst m; decide))
      htifIdle := p2.frame _ (by decide) (by decide) }

/-- The prologue's facts and the shared hash-to-bucket run give `Bucketed`. -/
theorem bucketed_of_hashed {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c c1 : Config}
    {pc v : BitVec 64} {writes : List Nat} {log : List WEntry} {regs : GRegs}
    (h : LookupInput ra sp a s0 s1 name c) (p1 : WriteRegistersPost writes log c pc v regs c1)
    (keys : KeysOK writes) (sub : ∀ n ∈ writes, n ∈ [1, 2, 5, 9, 10, 11, 12, 13, 14, 15])
    (c1_9 : gprGet c1.σ 9 = some a) (c1_2 : gprGet c1.σ 2 = some (sp + 18446744073709551584#64))
    (m1 : c1.σ.mem = writeLog c.σ.mem (saveLog sp ra s0 s1))
    (run : ∃ d, Steps c d ∧ Hashed c1 0x80021550#64 name d) :
    ∃ d, Steps c d ∧ Bucketed c ra sp a s0 s1 name d := by
  obtain ⟨d, run, p⟩ := run
  refine ⟨d, run, ?_⟩
  exact
    { good := p.good, image := p.image, minstret := p.minstret, tick := p.tick, link := p.link
      pc := p.pc, index := p.index
      name := (p.frame 9 (by decide) (by decide) (by decide)).trans c1_9
      stack := (p.frame 2 (by decide) (by decide) (by decide)).trans c1_2
      memory := p.memory.trans m1
      output := p.output.trans p1.output
      frame := fun n lo hi out => by
        have o1 : n ∉ writes := fun m => out (sub n m)
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (p.frame n lo hi (by simp [hashWrites]; omega)).trans (p1.gpr_frame keys n lo hi o1)
      htifIdle := p.htifIdle.trans (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)) }

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
  have m1 : c1.σ.mem = writeLog c.σ.mem (saveLog sp ra s0 s1) := by rw [p1.memory, logEq]
  obtain ⟨d, run, p⟩ := hashed_nonempty frontCode ne
    ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩ p1.pc c1_10 c1_14
    (by rw [m1]; exact h.named.saved h.apart)
  exact bucketed_of_hashed h p1 (by decide) (by decide) c1_9 c1_2 m1 ⟨d, run1.trans run, p⟩

/-- **The empty name to the bucket**: the prologue sees the terminator first; the hash is 0. -/
theorem front_empty {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    (h : LookupInput ra sp a s0 s1 name c) (e : name.length = 0) :
    ∃ d, Steps c d ∧ Bucketed c ra sp a s0 s1 name d := by
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  have r8 := regsAt_of h.saved0
  have r9 := regsAt_of h.saved1
  have r10 := regsAt_of h.arg
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
  have m1 : c1.σ.mem = writeLog c.σ.mem (saveLog sp ra s0 s1) := by rw [p1.memory, logEq]
  obtain ⟨d, run, p⟩ := hashed_empty frontCode e
    ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩ p1.pc (gpr_some_of c1_10)
  exact bucketed_of_hashed h p1 (by decide) (by decide) c1_9 c1_2 m1 ⟨d, run1.trans run, p⟩

/-- **`caml_named_value` to the bucket load**, for any name. -/
theorem front {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {c : Config}
    (h : LookupInput ra sp a s0 s1 name c) : ∃ d, Steps c d ∧ Bucketed c ra sp a s0 s1 name d := by
  rcases Nat.eq_zero_or_pos name.length with e | ne
  · exact front_empty h e
  · exact front_nonempty h ne

end OCaml.Vm.Primitives.Named.NamedValue
