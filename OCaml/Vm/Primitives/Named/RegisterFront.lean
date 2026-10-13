import OCaml.Vm.Primitives.Named.NamedRegister
import OCaml.Vm.Primitives.Named.NamedLookup

/-!
# `caml_register_named_value` up to the found/new split

The prologue saves `s1`, `s4`, `ra`, `s0`, `s2`, `s3` in a 64-byte frame and
tests the name's first byte. The hash loop, `% 13` and the chain walk are
the ones of `caml_named_value` at other addresses (`frontCode`,
`walkCode`). The function reaches `0x80021470` with the node named like the
query in `s0`, or `0x80021480` with `s0 = NULL` (`Looked`), holding the
name in `s1`, the bucket index in `s2`, the table in `s3` and the value in
`s4`.
-/

namespace OCaml.Vm.Primitives.Named.NamedRegister
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim
open NamedValue (NameAt HashCode FrontCode WalkCode Hashed hashWrites hashed_nonempty hashed_empty
  WalkState WalkDone walk walkWrites ChainAt chainFind BucketAt bucketAddr hashBytes regsAt regsAt_of
  gpr_some gpr_some_of gprReg_ne_htif wl_nil)

/-- This copy of the hash-to-bucket code. -/
theorem frontCode :
    FrontCode mod_call 0x800213fc#64 0x80021404#64 0x80021424#64 0x800214f4#64 0x80021434#64 :=
  ⟨start_fast, ⟨hashMore_fast, hashEnd_fast⟩, mod_fast, mod_call_shape, mod_call_decode, mod_call_pins,
    mod_call_target, by decide, by decide, empty_fast⟩

/-- This copy of the chain walk: a match goes on to the update, the chain's
end to the new node. -/
theorem walkCode :
    WalkCode cmp_call 0x80021458#64 0x80021460#64 0x8002146c#64 0x80021470#64 0x80021480#64 :=
  ⟨cmp_fast, cmp_call_shape, cmp_call_decode, cmp_call_pins, cmp_call_target, by decide, by decide,
    differ_fast, match_fast, nextEnd_fast, nextMore_fast⟩

/-- The prologue's six saves, from the caller's registers `R`. -/
def saveLog (R : Nat → BitVec 64) : List WEntry := proLog R []

/-- The frame slots the prologue writes, as offsets from `sp - 64`. -/
def slotOffsets : List Nat := [16, 24, 32, 40, 48, 56]

/-- **A call of `caml_register_named_value(name, v)`**: the caller's
registers `R` (`a0` the name, `a1` the value), the 64-byte frame below `sp`,
the name as a C string apart from the frame. -/
structure RegisterInput (R : Nat → BitVec 64) (name : List (BitVec 8)) (c : Config) : Prop where
  leaf : LeafInput (R 1) c
  pc : PCAt 0x800213d0#64 c
  regs : GHolds c.σ (pro_input R)
  slots : ∀ k ∈ slotOffsets, WriteWindow (R 2 - 64#64 + BitVec.ofNat 64 k) 8
  named : NameAt c.σ.mem (R 10) name
  apart : ∀ i, i ≤ name.length → OutLRange (saveLog R) (R 10 + BitVec.ofNat 64 i).toNat 1
  image : ImageOutside (saveLog R)

/-- The registers the code up to the bucket load may change. -/
def frontWrites : List Nat := [1, 2, 5, 9, 10, 11, 12, 13, 14, 15, 20]

/-- At the bucket load: `a0 = hash % 13`, `s1 = name`, `s4 = v`, the frame saved. -/
structure Bucketed (R : Nat → BitVec 64) (name : List (BitVec 8)) (before c : Config) : Prop where
  hashed : Hashed c 0x80021434#64 name c
  name : gprGet c.σ 9 = some (R 10)
  value : gprGet c.σ 20 = some (R 11)
  stack : gprGet c.σ 2 = some (R 2 + 18446744073709551552#64)
  memory : c.σ.mem = writeLog before.σ.mem (saveLog R)
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ frontWrites → gprGet c.σ n = gprGet before.σ n
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- The prologue's facts and the shared hash-to-bucket run give `Bucketed`. -/
theorem bucketed_of_hashed {R : Nat → BitVec 64} {name : List (BitVec 8)} {c c1 d : Config}
    {pc v : BitVec 64} {writes : List Nat} {log : List WEntry} {regs : GRegs}
    (p1 : WriteRegistersPost writes log c pc v regs c1) (keys : KeysOK writes)
    (sub : ∀ n ∈ writes, n ∈ frontWrites)
    (c1_9 : gprGet c1.σ 9 = some (R 10)) (c1_20 : gprGet c1.σ 20 = some (R 11))
    (c1_2 : gprGet c1.σ 2 = some (R 2 + 18446744073709551552#64))
    (m1 : c1.σ.mem = writeLog c.σ.mem (saveLog R)) (p : Hashed c1 0x80021434#64 name d) :
    Bucketed R name c d where
  hashed := { p with memory := rfl, output := rfl, frame := fun _ _ _ _ => rfl, htifIdle := rfl }
  name := (p.frame 9 (by decide) (by decide) (by decide)).trans c1_9
  value := (p.frame 20 (by decide) (by decide) (by decide)).trans c1_20
  stack := (p.frame 2 (by decide) (by decide) (by decide)).trans c1_2
  memory := p.memory.trans m1
  output := p.output.trans p1.output
  frame := fun n lo hi out => by
    have o1 : n ∉ writes := fun m => out (sub n m)
    simp only [frontWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    exact (p.frame n lo hi (by simp [hashWrites]; omega)).trans (p1.gpr_frame keys n lo hi o1)
  htifIdle := p.htifIdle.trans (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))

theorem slot {R : Nat → BitVec 64} {name : List (BitVec 8)} {c : Config} (h : RegisterInput R name c)
    (k : Nat) (hk : k ∈ slotOffsets := by decide) : WriteWindow (R 2 - 64#64 + BitVec.ofNat 64 k) 8 :=
  h.slots k hk

/-- **`caml_register_named_value` to the bucket load**, for any name. -/
theorem front {R : Nat → BitVec 64} {name : List (BitVec 8)} {c : Config} (h : RegisterInput R name c) :
    ∃ d, Steps c d ∧ Bucketed R name c d := by
  have r1 := regsAt_of h.leaf.raReg
  have rR : ∀ k ∈ [1, 2, 8, 9, 10, 11, 18, 19, 20], regsAt c k = R k := by
    intro k hk
    have := h.regs
    simp only [pro_input, GHolds] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    obtain ⟨e1, e2, e8, e9, e10, e11, e18, e19, e20, -⟩ := this
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact regsAt_of ‹_›
  have input : pro_input (regsAt c) = pro_input R := by
    simp only [pro_input, rR 1 (by decide), rR 2 (by decide), rR 8 (by decide), rR 9 (by decide),
      rR 10 (by decide), rR 11 (by decide), rR 18 (by decide), rR 19 (by decide), rR 20 (by decide)]
  have logEq : ∀ l, proLog (regsAt c) l = saveLog R := by
    intro l
    simp only [saveLog, proLog, rR 2 (by decide), rR 9 (by decide), rR 20 (by decide), rR 1 (by decide),
      rR 8 (by decide), rR 18 (by decide), rR 19 (by decide)]
  have logEq' : ∀ l, proEmptyLog (regsAt c) l = saveLog R := by
    intro l
    simp only [saveLog, proLog, proEmptyLog, rR 2 (by decide), rR 9 (by decide), rR 20 (by decide),
      rR 1 (by decide), rR 8 (by decide), rR 18 (by decide), rR 19 (by decide)]
  have take6 : (saveLog R).take 6 = saveLog R := by simp [saveLog, proLog]
  have apart0 : OutLRange (saveLog R) (R 10).toNat 1 := by simpa using h.apart 0 (Nat.zero_le _)
  have r10 := rR 10 (by decide)
  have r2 := rR 2 (by decide)
  have leaf0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have regs0 : GHolds c.σ (pro_input (regsAt c)) := by rw [input]; exact h.regs
  rcases Nat.eq_zero_or_pos name.length with e | ne
  · -- the empty name
    have nil : name = [] := List.eq_nil_of_length_eq_zero e
    have first : proEmpty_loads c.σ.mem (regsAt c) = [[0#8]] := by
      have := h.named.nul
      simp only [e] at this
      simp only [proEmpty_loads, r10]
      rw [show R 10 = R 10 + BitVec.ofNat 64 0 by simp, this]
    obtain ⟨c1, run1, p1⟩ := (proEmpty_fast c (regsAt c) leaf0 regs0
      (by rw [r2]; exact slot h 40) (by rw [r2]; exact slot h 16) (by rw [r2]; exact slot h 56)
      (by rw [r2]; exact slot h 48) (by rw [r2]; exact slot h 32) (by rw [r2]; exact slot h 24)
      (by rw [r10]; simpa using h.named.window 0 (Nat.zero_le _))
      (by rw [logEq', take6, r10]; exact apart0)
      (by rw [logEq']; exact h.image)
      (by rw [first]; decide)).run c ⟨h.pc, rfl⟩
    have o1 := p1.regs
    rw [first] at o1
    simp only [proEmpty_regs, GHolds, rR 1 (by decide), r2, rR 11 (by decide), r10] at o1
    obtain ⟨c1_20, c1_9, -, c1_2, c1_1, -, c1_10, -⟩ := o1
    have m1 : c1.σ.mem = writeLog c.σ.mem (saveLog R) := by rw [p1.memory, logEq']
    obtain ⟨d, run, p⟩ := hashed_empty frontCode e
      ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩ p1.pc (gpr_some_of c1_10)
    exact ⟨d, run1.trans run, bucketed_of_hashed p1 (by decide) (by decide) c1_9 c1_20 c1_2 m1 p⟩
  · -- a nonempty name
    have first : pro_loads c.σ.mem (regsAt c) = [[name[0]]] := by
      simp only [pro_loads, r10]
      rw [show R 10 = R 10 + BitVec.ofNat 64 0 by simp, h.named.bytes 0 ne]
    have nz := h.named.nonzero 0 ne
    obtain ⟨c1, run1, p1⟩ := (pro_fast c (regsAt c) leaf0 regs0
      (by rw [r2]; exact slot h 40) (by rw [r2]; exact slot h 16) (by rw [r2]; exact slot h 56)
      (by rw [r2]; exact slot h 48) (by rw [r2]; exact slot h 32) (by rw [r2]; exact slot h 24)
      (by rw [r10]; simpa using h.named.window 0 (Nat.zero_le _))
      (by rw [logEq, take6, r10]; exact apart0)
      (by rw [logEq]; exact h.image)
      (by
        rw [first]
        simp only [List.getD_cons_zero, guardB, bytesVal]
        simp [zero_extend, Sail.BitVec.zeroExtend]
        intro e; apply nz; apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat e; have lt := (name[0]).isLt; simp at this ⊢; omega)).run c ⟨h.pc, rfl⟩
    have o1 := p1.regs
    rw [first] at o1
    simp only [pro_regs, GHolds, rR 1 (by decide), r2, rR 11 (by decide), r10] at o1
    obtain ⟨c1_20, c1_9, c1_14, c1_2, c1_1, -, c1_10, -⟩ := o1
    have m1 : c1.σ.mem = writeLog c.σ.mem (saveLog R) := by rw [p1.memory, logEq]
    obtain ⟨d, run, p⟩ := hashed_nonempty frontCode ne
      ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩ p1.pc c1_10 c1_14
      (by rw [m1]; exact h.named.saved h.apart)
    exact ⟨d, run1.trans run, bucketed_of_hashed p1 (by decide) (by decide) c1_9 c1_20 c1_2 m1 p⟩

theorem bucket_addr (r : Nat) (hr : r < 13) :
    2147619900#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 309655#32 +++ 0#12) + 18446744073709550516#64 +
      (BitVec.ofNat 64 r <<< 32 >>> 32 <<< 3) = bucketAddr r := by
  have base : (2147619900#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 309655#32 +++ 0#12) +
      18446744073709550516#64 : BitVec 64) = BitVec.ofNat 64 Layout.sym_named_value_table := by decide
  rw [base]
  apply BitVec.eq_of_toNat_eq
  simp [bucketAddr, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Layout.sym_named_value_table]
  omega

theorem index_low (r : Nat) (hr : r < 13) : BitVec.ofNat 64 r <<< 32 >>> 32 = BitVec.ofNat 64 r := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The registers the code up to the found/new split may change. -/
def lookWrites : List Nat := [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20]

/-- `named_value_table`'s address, as the bucket block leaves it in `s3`. -/
def tableReg : BitVec 64 := 2147926000#64

/-- **At the found/new split**: `s0` holds the first node of the name's
bucket named like the query, at `0x80021470`, or `NULL`, at `0x80021480`. -/
structure Looked (R : Nat → BitVec 64) (name : List (BitVec 8)) (result : BitVec 64) (before c : Config) :
    Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  link : ∃ r : BitVec 64, gprGet c.σ 1 = some r ∧ r.toNat % 4 = 0
  pc : PCAt (if result = 0#64 then 0x80021480#64 else 0x80021470#64) c
  node : gprGet c.σ 8 = some result
  a0 : (gprGet c.σ 10).isSome
  query : gprGet c.σ 9 = some (R 10)
  bucket : gprGet c.σ 18 = some (BitVec.ofNat 64 ((hashBytes name).toNat % 13))
  table : gprGet c.σ 19 = some tableReg
  value : gprGet c.σ 20 = some (R 11)
  stack : gprGet c.σ 2 = some (R 2 + 18446744073709551552#64)
  memory : c.σ.mem = writeLog before.σ.mem (saveLog R)
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ lookWrites → gprGet c.σ n = gprGet before.σ n
  htif : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- A walk restarted after a block that changes registers outside the walk's. -/
theorem walk_restart {c d : Config} {q pc v : BitVec 64} {writes : List Nat} {regs : GRegs}
    (h : WalkState c q c) (p : WriteRegistersPost writes [] c pc v regs d) (keys : KeysOK writes)
    (no1 : 1 ∉ writes) (no9 : 9 ∉ writes) (a0 : (gprGet d.σ 10).isSome) : WalkState d q d :=
  { good := p.good, image := p.image, minstret := p.minstret, tick := p.tick
    link := by
      obtain ⟨r, hr, al⟩ := h.link
      exact ⟨r, (p.gpr_frame keys 1 (by decide) (by decide) no1).trans hr, al⟩
    a0 := a0
    query := (p.gpr_frame keys 9 (by decide) (by decide) no9).trans h.query
    memory := rfl, output := rfl, frame := fun _ _ _ _ => rfl, htif := rfl }

/-- **`caml_register_named_value` to the found/new split**, from the name's
bucket on the memory after the prologue. -/
theorem look {R : Nat → BitVec 64} {name : List (BitVec 8)} {qs : String}
    {nodes : List (BitVec 64 × String)} {c : Config} (h : RegisterInput R name c)
    (bucket : BucketAt (writeLog c.σ.mem (saveLog R)) (R 10) qs ((hashBytes name).toNat % 13) nodes) :
    ∃ d, Steps c d ∧ Looked R name (chainFind qs nodes) c d := by
  obtain ⟨cb, run1, pb⟩ := front h
  obtain ⟨head, headVal, chainAt⟩ := bucket.head
  let idx := (hashBytes name).toNat % 13
  have idxLt : idx < 13 := Nat.mod_lt _ (by decide)
  have r10 := regsAt_of pb.hashed.index
  have addr : 2147619900#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 309655#32 +++ 0#12) +
      18446744073709550516#64 + (regsAt cb 10 <<< 32 >>> 32 <<< 3) = bucketAddr idx := by
    rw [r10]; exact bucket_addr idx idxLt
  have regsB : GHolds cb.σ [(10, regsAt cb 10)] := ⟨by rw [r10]; exact pb.hashed.index, trivial⟩
  have w0 : WalkState cb (R 10) cb :=
    { good := pb.hashed.good, image := pb.hashed.image, minstret := pb.hashed.minstret
      tick := pb.hashed.tick, link := pb.hashed.link, a0 := gpr_some_of pb.hashed.index
      query := pb.name, memory := rfl, output := rfl, frame := fun _ _ _ _ => rfl, htif := rfl }
  have readHead : bytesVal .ld (read8 cb.σ.mem (bucketAddr idx).toNat) = head := by
    rw [pb.memory]; exact headVal
  -- the bucket's registers after either bucket block
  have low : regsAt cb 10 <<< 32 >>> 32 = BitVec.ofNat 64 idx := by rw [r10]; exact index_low idx idxLt
  have toDone : ∃ c2 cw, Steps cb cw ∧ c2.σ.mem = cb.σ.mem ∧ c2.σ.sailOutput = cb.σ.sailOutput ∧
      c2.σ.regs.get? Register.htif_payload_writes = cb.σ.regs.get? Register.htif_payload_writes ∧
      (∀ n, 1 ≤ n → n ≤ 31 → n ∉ [8, 15, 18, 19] → gprGet c2.σ n = gprGet cb.σ n) ∧
      WalkDone 0x80021470#64 0x80021480#64 c2 (R 10) (chainFind qs nodes) cw ∧
      gprGet cw.σ 18 = some (BitVec.ofNat 64 idx) ∧ gprGet cw.σ 19 = some tableReg := by
    by_cases empty : head = 0#64
    · obtain ⟨c2, run2, p2⟩ := (bucketEmpty_fast cb (regsAt cb) w0.leaf regsB (by rw [addr]; exact bucket.window)
        (by simp only [bucketEmpty_loads, addr, List.getD_cons_zero, readHead, empty]; decide)).run cb ⟨pb.hashed.pc, rfl⟩
      have o2 := p2.regs
      simp only [bucketEmpty_regs, bucketEmpty_loads, addr, List.getD_cons_zero, readHead, empty, GHolds] at o2
      simp only [low] at o2
      obtain ⟨o8, -, o19, o18, o10, -⟩ := o2
      have s2 := walk_restart w0 p2 (by decide) (by decide) (by decide) (gpr_some_of o10)
      obtain ⟨c3, run3, p3⟩ := (none_fast c2 (regsAt c2) s2.leaf ⟨gpr_some s2.a0, trivial⟩).run c2 ⟨p2.pc, rfl⟩
      have s3 := s2.after_block p3 (by decide) (by simp) (by simp) (by simp)
        (gpr_some_of ((p3.gpr_frame (by decide) 10 (by decide) (by decide) (by simp)).trans (gpr_some s2.a0)))
      subst empty
      cases chainAt
      · refine ⟨c2, c3, run2.trans run3, by rw [p2.memory, wl_nil], p2.output,
          p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
          fun n lo hi out => p2.gpr_frame (by decide) n lo hi out,
          ⟨s3, by rw [show chainFind qs ([] : List (BitVec 64 × String)) = 0#64 from rfl, if_pos rfl]; exact p3.pc,
            (p3.gpr_frame (by decide) 8 (by decide) (by decide) (by simp)).trans o8⟩, ?_, ?_⟩
        · exact (p3.gpr_frame (by decide) 18 (by decide) (by decide) (by simp)).trans o18
        · exact (p3.gpr_frame (by decide) 19 (by decide) (by decide) (by simp)).trans o19
      · exact absurd rfl (by assumption : (0#64 : BitVec 64) ≠ 0#64)
    · obtain ⟨c2, run2, p2⟩ := (bucketHit_fast cb (regsAt cb) w0.leaf regsB (by rw [addr]; exact bucket.window)
        (by simp only [bucketHit_loads, addr, List.getD_cons_zero, readHead]; simp [guardB, empty])).run cb
        ⟨pb.hashed.pc, rfl⟩
      have o2 := p2.regs
      simp only [bucketHit_regs, bucketHit_loads, addr, List.getD_cons_zero, readHead, GHolds] at o2
      simp only [low] at o2
      obtain ⟨o8, -, o19, o18, o10, -⟩ := o2
      have s2 := walk_restart w0 p2 (by decide) (by decide) (by decide) (gpr_some_of o10)
      have m2 : c2.σ.mem = cb.σ.mem := by rw [p2.memory, wl_nil]
      obtain ⟨cw, run3, done⟩ := walk walkCode nodes head c2 (by rw [m2, pb.memory]; exact chainAt) empty s2
        p2.pc o8
      refine ⟨c2, cw, run2.trans run3, m2, p2.output, p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide), fun n lo hi out => p2.gpr_frame (by decide) n lo hi out, done, ?_, ?_⟩
      · exact (done.state.frame 18 (by decide) (by decide) (by decide)).trans o18
      · exact (done.state.frame 19 (by decide) (by decide) (by decide)).trans o19
  obtain ⟨c2, cw, run2, m2, o2, h2, f2, pw, b18, b19⟩ := toDone
  have keep : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [8, 15, 18, 19] → n ∉ walkWrites → gprGet cw.σ n = gprGet cb.σ n :=
    fun n lo hi o2 ow => (pw.state.frame n lo hi ow).trans (f2 n lo hi o2)
  refine ⟨cw, run1.trans run2, ?_⟩
  exact
    { good := pw.state.good, image := pw.state.image, minstret := pw.state.minstret, tick := pw.state.tick
      link := pw.state.link, pc := pw.pc, node := pw.result, a0 := pw.state.a0, query := pw.state.query
      bucket := b18, table := b19
      value := (keep 20 (by decide) (by decide) (by decide) (by decide)).trans pb.value
      stack := (keep 2 (by decide) (by decide) (by decide) (by decide)).trans pb.stack
      memory := pw.state.memory.trans (m2.trans pb.memory)
      output := pw.state.output.trans (o2.trans pb.output)
      frame := fun n lo hi out => by
        simp only [lookWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (keep n lo hi (by simp; omega) (by simp [walkWrites]; omega)).trans (pb.frame n lo hi (by
          simp [frontWrites]; omega))
      htif := pw.state.htif.trans (h2.trans pb.htifIdle) }

end OCaml.Vm.Primitives.Named.NamedRegister
