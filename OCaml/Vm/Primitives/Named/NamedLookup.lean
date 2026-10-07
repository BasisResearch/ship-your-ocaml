import OCaml.Vm.Primitives.Named.NamedChain
import OCaml.Vm.Sim.LogRead

/-!
# `caml_named_value` as a call summary

`caml_named_value(name)` hashes the name (`front`), loads the bucket's head
from `named_value_table`, walks the chain (`walk`) and returns the first
node named `name` (whose first word is the value slot), or `NULL`. The
bucket's chain is `ChainAt`, stated on the memory after the prologue's three
saves (the caller's frame is below `sp`).
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim
open OCaml.Vm.Boot.Startup

/-- `&named_value_table[b]`. -/
def bucketAddr (b : Nat) : BitVec 64 := BitVec.ofNat 64 (Layout.sym_named_value_table + 8 * b)

theorem bucket_addr (r : Nat) (hr : r < 13) :
    2147620184#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 309143#32 +++ 0#12) + 18446744073709550232#64 +
      BitVec.ofNat 64 r <<< 32 >>> 29 = bucketAddr r := by
  have base : (2147620184#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 309143#32 +++ 0#12) +
      18446744073709550232#64 : BitVec 64) = BitVec.ofNat 64 Layout.sym_named_value_table := by decide
  rw [base]
  apply BitVec.eq_of_toNat_eq
  simp [bucketAddr, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Layout.sym_named_value_table]
  omega

/-- **The named-value table at the hashed bucket**, on the memory after the
prologue: the head word and its chain. -/
structure BucketAt (m : Mem) (q : BitVec 64) (qs : String) (b : Nat) (nodes : List (BitVec 64 × String)) :
    Prop where
  window : ReadWindow (bucketAddr b) 8
  head : ∃ h : BitVec 64, bytesVal .ld (read8 m (bucketAddr b).toNat) = h ∧ ChainAt m q qs h nodes

/-- **`caml_named_value` returned**: `a0` is the first node named like the
query in its bucket (or `NULL`), at the caller's return address, with the
callee-saved registers, `sp` and `ra` restored and only the frame below `sp`
written. -/
structure NamedFound (before : Config) (ra sp a s0 s1 : BitVec 64) (result : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  pc : pcOf c = some ra
  result : gprGet c.σ 10 = some result
  returned : gprGet c.σ 1 = some ra
  stack : gprGet c.σ 2 = some sp
  saved0 : gprGet c.σ 8 = some s0
  saved1 : gprGet c.σ 9 = some s1
  memory : c.σ.mem = writeLog before.σ.mem (saveLog sp ra s0 s1)
  output : c.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] →
    gprGet c.σ n = gprGet before.σ n
  htif : c.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- The walk's starting state at the bucket load. -/
theorem WalkState.of_bucketed {c cb : Config} {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)}
    (h : Bucketed c ra sp a s0 s1 name cb) : WalkState cb a cb :=
  { good := h.good, image := h.image, minstret := h.minstret, tick := h.tick, link := h.link
    a0 := gpr_some_of h.index, query := h.name, memory := rfl, output := rfl
    frame := fun _ _ _ _ => rfl, htif := rfl }

/-- The frame slots, as naturals. -/
theorem slot_nat {sp : BitVec 64} (w : WriteWindow (sp - 32#64 + 8#64) 8) {k : Nat} (hk : k ≤ 24) :
    (sp - 32#64 + BitVec.ofNat 64 k).toNat = (sp - 32#64).toNat + k := by
  have := w.upper; have := w.lower
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega

/-- The return block's view of the frame: `sp - 32` as the bucket left it. -/
theorem frame_view (sp : BitVec 64) (k : Nat) :
    sp + 18446744073709551584#64 + BitVec.ofNat 64 k = sp - 32#64 + BitVec.ofNat 64 k := by
  rw [BitVec.sub_eq_add_neg, show (-32#64 : BitVec 64) = 18446744073709551584#64 from by decide]

/-- **`caml_named_value(name)`**: the first node of the name's bucket named
`qs`, or `NULL`. -/
theorem named_value_summary {ra sp a s0 s1 : BitVec 64} {name : List (BitVec 8)} {qs : String}
    {nodes : List (BitVec 64 × String)} {c : Config}
    (h : LookupInput ra sp a s0 s1 name c)
    (bucket : BucketAt (writeLog c.σ.mem (saveLog sp ra s0 s1)) a qs ((hashBytes name).toNat % 13) nodes) :
    ∃ d, Steps c d ∧ NamedFound c ra sp a s0 s1 (chainFind qs nodes) d := by
  obtain ⟨cb, run1, pb⟩ := front h
  obtain ⟨head, headVal, chainAt⟩ := bucket.head
  let idx := (hashBytes name).toNat % 13
  have idxLt : idx < 13 := Nat.mod_lt _ (by decide)
  have r10 := regsAt_of pb.index
  have addr : 2147620184#64 + BitVec.signExtend 64 (BitVec.extractLsb' 12 20 309143#32 +++ 0#12) +
      18446744073709550232#64 + regsAt cb 10 <<< 32 >>> 29 = bucketAddr idx := by
    rw [r10]; exact bucket_addr idx idxLt
  have regsB : GHolds cb.σ [(10, regsAt cb 10)] := ⟨by rw [r10]; exact pb.index, trivial⟩
  have w0 := (WalkState.of_bucketed pb)
  have readHead : bytesVal .ld (read8 cb.σ.mem (bucketAddr idx).toNat) = head := by
    rw [pb.memory]; exact headVal
  -- to the return block, with the answer in s0
  have toDone : ∃ cw, Steps cb cw ∧ WalkDone cb a (chainFind qs nodes) cw := by
    by_cases empty : head = 0#64
    · obtain ⟨c2, run2, p2⟩ := (bucketEmpty_fast cb (regsAt cb) w0.leaf regsB (by rw [addr]; exact bucket.window)
        (by simp only [bucketEmpty_loads, addr, List.getD_cons_zero, readHead, empty]; decide)).run cb ⟨pb.pc, rfl⟩
      have o2 := p2.regs
      simp only [bucketEmpty_regs, bucketEmpty_loads, addr, List.getD_cons_zero, readHead, empty, GHolds] at o2
      have s2 := w0.after_block p2 (by decide) (by decide) (by decide) (by decide) (gpr_some_of o2.2.2.1)
      obtain ⟨c3, run3, p3⟩ := (none_fast c2 (regsAt c2) s2.leaf ⟨gpr_some s2.a0, trivial⟩).run c2 ⟨p2.pc, rfl⟩
      have s3 := s2.after_block p3 (by decide) (by simp) (by simp) (by simp)
        (gpr_some_of ((p3.gpr_frame (by decide) 10 (by decide) (by decide) (by simp)).trans (gpr_some s2.a0)))
      subst empty
      cases chainAt
      · exact ⟨c3, run2.trans run3, s3, p3.pc,
          (p3.gpr_frame (by decide) 8 (by decide) (by decide) (by simp)).trans o2.1⟩
      · exact absurd rfl (by assumption : (0#64 : BitVec 64) ≠ 0#64)
    · obtain ⟨c2, run2, p2⟩ := (bucketHit_fast cb (regsAt cb) w0.leaf regsB (by rw [addr]; exact bucket.window)
        (by simp only [bucketHit_loads, addr, List.getD_cons_zero, readHead]; simp [guardB, empty])).run cb
        ⟨pb.pc, rfl⟩
      have o2 := p2.regs
      simp only [bucketHit_regs, bucketHit_loads, addr, List.getD_cons_zero, readHead, GHolds] at o2
      have s2 := w0.after_block p2 (by decide) (by decide) (by decide) (by decide) (gpr_some_of o2.2.2.1)
      obtain ⟨cw, run3, done⟩ := walk nodes head c2 (by rw [pb.memory]; exact chainAt) empty s2
        p2.pc o2.1
      exact ⟨cw, run2.trans run3, done⟩
  obtain ⟨cw, run2, pw⟩ := toDone
  -- the return block
  have spw : gprGet cw.σ 2 = some (sp + 18446744073709551584#64) :=
    (pw.state.frame 2 (by decide) (by decide) (by decide)).trans pb.stack
  have r2 := regsAt_of spw
  have r8 := regsAt_of pw.result
  have mw : cw.σ.mem = writeLog c.σ.mem (saveLog sp ra s0 s1) := pw.state.memory.trans pb.memory
  have t8 : (sp - 32#64 + 8#64).toNat = (sp - 32#64).toNat + 8 := slot_nat h.slot8 (k := 8) (by decide)
  have t16 : (sp - 32#64 + 16#64).toNat = (sp - 32#64).toNat + 16 := slot_nat h.slot8 (k := 16) (by decide)
  have t24 : (sp - 32#64 + 24#64).toNat = (sp - 32#64).toNat + 24 := slot_nat h.slot8 (k := 24) (by decide)
  have readSaved : ∀ (i k : Nat) (w : BitVec 64), (saveLog sp ra s0 s1)[i]? = some ((sp - 32#64 + BitVec.ofNat 64 k).toNat, 8, w) →
      OutLRange ((saveLog sp ra s0 s1).drop (i + 1)) (sp - 32#64 + BitVec.ofNat 64 k).toNat 8 →
      bytesVal .ld (read8 cw.σ.mem (regsAt cw 2 + BitVec.ofNat 64 k).toNat) = w := by
    intro i k w sel out
    rw [r2, frame_view, read8_value, mw]
    exact word_writeLog_at _ _ i _ w sel out
  have readRa : bytesVal .ld (read8 cw.σ.mem (regsAt cw 2 + 24#64).toNat) = ra :=
    readSaved 1 24 ra rfl (by simp only [saveLog, List.drop, OutLRange, t16, t24, and_true]; omega)
  have readS0 : bytesVal .ld (read8 cw.σ.mem (regsAt cw 2 + 16#64).toNat) = s0 :=
    readSaved 2 16 s0 rfl trivial
  have readS1 : bytesVal .ld (read8 cw.σ.mem (regsAt cw 2 + 8#64).toNat) = s1 :=
    readSaved 0 8 s1 rfl (by simp only [saveLog, List.drop, OutLRange, t8, t16, t24, and_true]; omega)
  have win (k : Nat) (hk : k ∈ [8, 16, 24]) : ReadWindow (regsAt cw 2 + BitVec.ofNat 64 k) 8 := by
    rw [r2, frame_view]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact h.slot8.read
    · exact h.slot16.read
    · exact h.slot24.read
  have regsD : GHolds cw.σ (done_input (regsAt cw)) :=
    ⟨by rw [r2]; exact spw, by rw [r8]; exact pw.result, gpr_some pw.state.a0, trivial⟩
  obtain ⟨d, run3, pd⟩ := (done_fast cw ra (regsAt cw) pw.state.leaf regsD (win 24 (by simp)) (win 16 (by simp))
    (win 8 (by simp)) readRa h.leaf.aligned).run cw ⟨pw.pc, rfl⟩
  have od := pd.regs
  simp only [done_regs, done_loads, List.getD_cons_zero, List.getD_cons_succ, GHolds] at od
  rw [readRa, readS0, readS1] at od
  obtain ⟨d2, d9, d8, d10, d1, -⟩ := od
  refine ⟨d, run1.trans (run2.trans run3), ?_⟩
  exact
    { good := pd.good, image := pd.image, minstret := pd.minstret, tick := pd.tick
      pc := pd.pc
      result := by rw [d10, r8]
      returned := d1
      stack := by
        have e : sp + 18446744073709551584#64 + 32#64 = sp := by bv_omega
        rw [d2, r2, e]
      saved0 := d8, saved1 := d9
      memory := by rw [pd.memory, wl_nil, mw]
      output := by rw [pd.output, pw.state.output, pb.output]
      frame := fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (pd.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          ((pw.state.frame n lo hi (by simp [walkWrites]; omega)).trans (pb.frame n lo hi (by simp; omega)))
      htif := by
        rw [pd.frame _ (fun n _ => gprReg_ne_htif n) (by decide), pw.state.htif, pb.htifIdle] }

end OCaml.Vm.Primitives.Named.NamedValue
