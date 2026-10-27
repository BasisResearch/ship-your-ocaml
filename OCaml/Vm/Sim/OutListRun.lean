import OCaml.Vm.Sim.OutListWalk

/-!
# `caml_ml_out_channels_list` from its entry to its return

The prologue (`pro_step`) builds the 128-byte frame and the CAMLlocal3 roots
(`local_roots := sp + 48`) and loads the list head; an empty list jumps to the
epilogue (`0x80016088`), any other reaches the walk's head with the walk's
invariant at its first visit. The epilogue (`done_step`) restores
`local_roots`, `s0`, `ra` and `sp` and returns `res`.
-/

namespace OCaml.Vm.Sim.OutListWalk
open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel.OutList LeanRV64DExecutable
set_option autoImplicit false
variable {Customs : Config → Nat → Prop}

/-- `caml_ml_out_channels_list`'s entry. -/
def entryPc : BitVec 64 := 0x80016020#64

/-- The prologue's stores under the frame `sp` (the caller's `sp − 128`): the
saved `s0` and `ra`, `local_roots := sp + 48`, and the CAMLlocal3 frame
(`next`, `ntables = 3`, `nitems = 1`, `&res`, `&tail`, `&chan`) with
`res = tail = chan = Val_unit`. -/
def proStoreLog (sp ra s0 dom roots : BitVec 64) : List WEntry :=
  [((sp + 112#64).toNat, 8, s0), ((sp + 120#64).toNat, 8, ra), ((dom + 288#64).toNat, 8, sp + 48#64),
   ((sp + 48#64).toNat, 8, roots), ((sp + 24#64).toNat, 8, 1#64), ((sp + 32#64).toNat, 8, 1#64),
   ((sp + 40#64).toNat, 8, 1#64), ((sp + 64#64).toNat, 8, 1#64), ((sp + 56#64).toNat, 8, 3#64),
   ((sp + 72#64).toNat, 8, sp + 24#64), ((sp + 80#64).toNat, 8, sp + 32#64), ((sp + 88#64).toNat, 8, sp + 40#64)]

/-- Where the prologue goes: the empty list's `j` to the epilogue, or the head. -/
def proPc (head : BitVec 64) : BitVec 64 := if head = 0#64 then 0x80016088#64 else headPc

/-- The registers after the prologue. -/
structure ProRegs (ra sp head roots dom : BitVec 64) (e : Config) : Prop where
  link : gpr e 1 = some ra
  sp : gpr e 2 = some sp
  record : gpr e 8 = some head
  a0 : gpr e 10 = some 1#64
  state : gpr e 13 = some stateAddr
  roots : gpr e 14 = some roots
  domain : gpr e 15 = some dom

/-- The registers at the entry, for the prologue's blocks. -/
def proR (ra sp0 s0 : BitVec 64) : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp0 else s0

/-- The prologue's numbers: its frame and the domain record, in RAM above `.bss`. -/
structure ProNums (sp0 dom : BitVec 64) : Prop where
  spLow : Layout.sym_bss_end + 128 ≤ sp0.toNat
  spHigh : sp0.toNat ≤ 2 ^ 32
  spAl : sp0.toNat % 16 = 0
  dLow : Layout.sym_bss_end ≤ dom.toNat
  dHigh : dom.toNat + 296 ≤ 2 ^ 32
  dAl : dom.toNat % 8 = 0
  apart : dom.toNat + 296 ≤ sp0.toNat - 128 ∨ sp0.toNat ≤ dom.toNat + 288

theorem ProNums.spk {sp0 dom : BitVec 64} (h : ProNums sp0 dom) {k : Nat} (hk : k ≤ 120) :
    (sp0 - 128#64 + BitVec.ofNat 64 k).toNat = sp0.toNat - 128 + k := by
  have := h.spLow; have := h.spHigh
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem ProNums.d288 {sp0 dom : BitVec 64} (h : ProNums sp0 dom) : (dom + 288#64).toNat = dom.toNat + 288 := by
  have := h.dHigh; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ProNums.win {sp0 dom : BitVec 64} (h : ProNums sp0 dom) (ra s0 : BitVec 64) {k : Nat} (hk : k ≤ 120)
    (al : k % 8 = 0) : WriteWindow (proR ra sp0 s0 2 - 128#64 + BitVec.ofNat 64 k) 8 := by
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have e := h.spk hk
  have := h.spLow; have := h.spHigh; have := h.spAl
  show WriteWindow (sp0 - 128#64 + BitVec.ofNat 64 k) 8
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, tohost]; omega, by rw [e]; omega⟩

theorem ProNums.wDom {sp0 dom : BitVec 64} (h : ProNums sp0 dom) : WriteWindow (dom + 288#64) 8 := by
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have e := h.d288; have := h.dLow; have := h.dHigh; have := h.dAl
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, tohost]; omega, by rw [e]; omega⟩

/-- The prologue's log, both branches. -/
theorem proLog_eq {ra sp0 s0 dom roots : BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)}
    (wD : bytesT m (2147896584#64).toNat 8 = dom) (wR : bytesT m (dom + 288#64).toNat 8 = roots) :
    proLog (proR ra sp0 s0) (pro_loads m (proR ra sp0 s0)) = proStoreLog (sp0 - 128#64) ra s0 dom roots ∧
    proEmptyLog (proR ra sp0 s0) (proEmpty_loads m (proR ra sp0 s0)) = proStoreLog (sp0 - 128#64) ra s0 dom roots := by
  have vD : bytesVal .ld (read8 m (2147896584#64).toNat) = dom := (read8_value _ _).trans wD
  have vR : bytesVal .ld (read8 m (dom + 288#64).toNat) = roots := (read8_value _ _).trans wR
  constructor
  · simp only [proLog, pro_loads, List.getD_cons_zero, List.getD_cons_succ, vD, vR]; rfl
  · simp only [proEmptyLog, proEmpty_loads, List.getD_cons_zero, List.getD_cons_succ, vD, vR]; rfl

theorem ProNums.two {sp0 dom : BitVec 64} (h : ProNums sp0 dom) (ra s0 roots : BitVec 64) :
    OutLRange ((proStoreLog (sp0 - 128#64) ra s0 dom roots).take 2) (2147896584#64).toNat 8 ∧
    OutLRange ((proStoreLog (sp0 - 128#64) ra s0 dom roots).take 2) (2147896128#64).toNat 8 ∧
    OutLRange ((proStoreLog (sp0 - 128#64) ra s0 dom roots).take 2) (dom + 288#64).toNat 8 := by
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have := h.spLow; have := h.apart
  have r1 : (2147896584#64 : BitVec 64).toNat = 2147896584 := rfl
  have r2 : (2147896128#64 : BitVec 64).toNat = 2147896128 := rfl
  simp only [proStoreLog, List.take, OutLRange, h.spk (k := 112) (by omega), h.spk (k := 120) (by omega), h.d288,
    r1, r2, and_true]
  refine ⟨by omega, by omega, by omega⟩

theorem ProNums.outside {sp0 dom : BitVec 64} (h : ProNums sp0 dom) (ra s0 roots : BitVec 64) :
    ImageOutside (proStoreLog (sp0 - 128#64) ra s0 dom roots) := by
  have := h.spLow; have := h.dLow
  apply imageOutside_of_above
  intro x hx
  simp only [proStoreLog, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (show _ ≤ (dom + 288#64).toNat; rw [h.d288]; omega)
    | (show _ ≤ (sp0 - 128#64 + _).toNat; rw [h.spk (by omega)]; omega)

/-- The registers after the prologue's block. -/
theorem proRegs_of {ra sp0 dom head roots : BitVec 64} {e : Config} {regs : GRegs} (h : GHolds e.σ regs)
    (l1 : lookupG 1 regs = some ra) (l2 : lookupG 2 regs = some (sp0 - 128#64)) (l8 : lookupG 8 regs = some head)
    (l10 : lookupG 10 regs = some 1#64) (l13 : lookupG 13 regs = some stateAddr) (l14 : lookupG 14 regs = some roots)
    (l15 : lookupG 15 regs = some dom) : ProRegs ra (sp0 - 128#64) head roots dom e :=
  ⟨gholds_lookup _ h l1, gholds_lookup _ h l2, gholds_lookup _ h l8, gholds_lookup _ h l10,
    gholds_lookup _ h l13, gholds_lookup _ h l14, gholds_lookup _ h l15⟩

/-- The prologue on a non-empty list. -/
theorem pro_go {ra sp0 s0 dom head roots : BitVec 64} {c : Config} (nums : ProNums sp0 dom)
    (leaf : LeafInput ra c) (pc : pcOf c = some entryPc) (h2 : gpr c 2 = some sp0) (h8 : gpr c 8 = some s0)
    (wD : bytesT c.σ.mem (2147896584#64).toNat 8 = dom) (wH : bytesT c.σ.mem (2147896128#64).toNat 8 = head)
    (wR : bytesT c.σ.mem (dom + 288#64).toNat 8 = roots) (ne : head ≠ 0#64) :
    ∃ e, Steps c e ∧
      EffectPost [2, 8, 10, 11, 12, 13, 14, 15, 16, 17]
        (writeLog c.σ.mem (proStoreLog (sp0 - 128#64) ra s0 dom roots)) c headPc 1#64 e ∧
      ProRegs ra (sp0 - 128#64) head roots dom e := by
  obtain ⟨lg, _⟩ := proLog_eq (ra := ra) (sp0 := sp0) (s0 := s0) wD wR
  obtain ⟨t1, t2, t3⟩ := nums.two ra s0 roots
  have vD : bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat) = dom := (read8_value _ _).trans wD
  have vH : bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat) = head := (read8_value _ _).trans wH
  have vR : bytesVal .ld (read8 c.σ.mem (dom + 288#64).toNat) = roots := (read8_value _ _).trans wR
  obtain ⟨e, run, post⟩ := (pro_fast c (proR ra sp0 s0) leaf ⟨leaf.raReg, h2, h8, True.intro⟩
    (nums.win ra s0 (k := 112) (by omega) (by omega)) (nums.win ra s0 (k := 120) (by omega) (by omega))
    (by rw [lg]; exact t1) (by rw [lg]; exact t2) (by rw [vD]; exact nums.wDom.read) (by rw [lg, vD]; exact t3)
    (by rw [vD]; exact nums.wDom)
    (nums.win ra s0 (k := 48) (by omega) (by omega)) (nums.win ra s0 (k := 24) (by omega) (by omega))
    (nums.win ra s0 (k := 32) (by omega) (by omega)) (nums.win ra s0 (k := 40) (by omega) (by omega))
    (nums.win ra s0 (k := 64) (by omega) (by omega)) (nums.win ra s0 (k := 56) (by omega) (by omega))
    (nums.win ra s0 (k := 72) (by omega) (by omega)) (nums.win ra s0 (k := 80) (by omega) (by omega))
    (nums.win ra s0 (k := 88) (by omega) (by omega)) (by rw [lg]; exact nums.outside ra s0 roots)
    (by simp only [pro_loads, List.getD_cons_succ, List.getD_cons_zero]; rw [vH]; simpa [guardB] using ne)).run c
    ⟨pc, rfl⟩
  rw [lg] at post
  refine ⟨e, run, post.toEffectPost, proRegs_of post.regs rfl rfl ?_ rfl rfl ?_ ?_⟩
  · show some (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)) = _; rw [vH]
  · show some (bytesVal .ld (read8 c.σ.mem ((bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat)) + 288#64).toNat)) = _
    rw [vD, vR]
  · show some (bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat)) = _; rw [vD]

/-- The prologue on the empty list, to the epilogue's `j`. -/
theorem pro_empty {ra sp0 s0 dom roots : BitVec 64} {c : Config} (nums : ProNums sp0 dom)
    (leaf : LeafInput ra c) (pc : pcOf c = some entryPc) (h2 : gpr c 2 = some sp0) (h8 : gpr c 8 = some s0)
    (wD : bytesT c.σ.mem (2147896584#64).toNat 8 = dom) (wH : bytesT c.σ.mem (2147896128#64).toNat 8 = 0#64)
    (wR : bytesT c.σ.mem (dom + 288#64).toNat 8 = roots) :
    ∃ e, Steps c e ∧
      EffectPost [2, 8, 10, 11, 12, 13, 14, 15, 16, 17]
        (writeLog c.σ.mem (proStoreLog (sp0 - 128#64) ra s0 dom roots)) c 0x80016088#64 1#64 e ∧
      ProRegs ra (sp0 - 128#64) 0#64 roots dom e := by
  obtain ⟨_, lg⟩ := proLog_eq (ra := ra) (sp0 := sp0) (s0 := s0) wD wR
  obtain ⟨t1, t2, t3⟩ := nums.two ra s0 roots
  have vD : bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat) = dom := (read8_value _ _).trans wD
  have vH : bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat) = 0#64 := (read8_value _ _).trans wH
  have vR : bytesVal .ld (read8 c.σ.mem (dom + 288#64).toNat) = roots := (read8_value _ _).trans wR
  obtain ⟨e, run, post⟩ := (proEmpty_fast c (proR ra sp0 s0) leaf ⟨leaf.raReg, h2, h8, True.intro⟩
    (nums.win ra s0 (k := 112) (by omega) (by omega)) (nums.win ra s0 (k := 120) (by omega) (by omega))
    (by rw [lg]; exact t1) (by rw [lg]; exact t2) (by rw [vD]; exact nums.wDom.read) (by rw [lg, vD]; exact t3)
    (by rw [vD]; exact nums.wDom)
    (nums.win ra s0 (k := 48) (by omega) (by omega)) (nums.win ra s0 (k := 24) (by omega) (by omega))
    (nums.win ra s0 (k := 32) (by omega) (by omega)) (nums.win ra s0 (k := 40) (by omega) (by omega))
    (nums.win ra s0 (k := 64) (by omega) (by omega)) (nums.win ra s0 (k := 56) (by omega) (by omega))
    (nums.win ra s0 (k := 72) (by omega) (by omega)) (nums.win ra s0 (k := 80) (by omega) (by omega))
    (nums.win ra s0 (k := 88) (by omega) (by omega)) (by rw [lg]; exact nums.outside ra s0 roots)
    (by simp only [proEmpty_loads, List.getD_cons_succ, List.getD_cons_zero]; rw [vH]; decide)).run c ⟨pc, rfl⟩
  rw [lg] at post
  refine ⟨e, run, post.toEffectPost, proRegs_of post.regs rfl rfl ?_ rfl rfl ?_ ?_⟩
  · show some (bytesVal .ld (read8 c.σ.mem (2147896128#64).toNat)) = _; rw [vH]
  · show some (bytesVal .ld (read8 c.σ.mem ((bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat)) + 288#64).toNat)) = _
    rw [vD, vR]
  · show some (bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat)) = _; rw [vD]

/-- The epilogue's entry. -/
def donePc : BitVec 64 := 0x80016120#64

/-- **The epilogue** (`done`): `local_roots` restored, `ra` and `s0` reloaded,
the frame popped, `a0` returned. -/
theorem done_step {r sp v roots dom ra s0 : BitVec 64} {z : Config} (leaf : LeafInput r z)
    (pc : pcOf z = some donePc) (h2 : gpr z 2 = some sp) (h10 : gpr z 10 = some v)
    (h14 : gpr z 14 = some roots) (h15 : gpr z 15 = some dom)
    (wRa : bytesT z.σ.mem (sp + 120#64).toNat 8 = ra) (wS0 : bytesT z.σ.mem (sp + 112#64).toNat 8 = s0)
    (al : ra.toNat % 4 = 0)
    (spLow : Layout.sym_bss_end ≤ sp.toNat) (spHigh : sp.toNat + 128 ≤ 2 ^ 32) (spAl : sp.toNat % 16 = 0)
    (dLow : Layout.sym_bss_end ≤ dom.toNat) (dHigh : dom.toNat + 296 ≤ 2 ^ 32) (dAl : dom.toNat % 8 = 0)
    (apart : dom.toNat + 296 ≤ sp.toNat ∨ sp.toNat + 128 ≤ dom.toNat + 288) :
    ∃ z', Steps z z' ∧ EffectPost [1, 2, 8] (writeLog z.σ.mem [((dom + 288#64).toNat, 8, roots)]) z ra v z' ∧
      gpr z' 1 = some ra ∧ gpr z' 2 = some (sp + 128#64) ∧ gpr z' 8 = some s0 := by
  let R : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp else if n = 10 then v
    else if n = 14 then roots else dom
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have s120 : (sp + 120#64).toNat = sp.toNat + 120 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s112 : (sp + 112#64).toNat = sp.toNat + 112 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have d288 : (dom + 288#64).toNat = dom.toNat + 288 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have lg : doneLog R (done_loads z.σ.mem R) = [((dom + 288#64).toNat, 8, roots)] := rfl
  have w0 : WriteWindow (dom + 288#64) 8 :=
    ⟨by rw [d288]; omega, by rw [d288]; omega, by rw [d288, tohost]; omega, by rw [d288]; omega⟩
  have w1 : ReadWindow (sp + 120#64) 8 := ⟨by rw [s120]; omega, by rw [s120]; omega, Or.inr (by rw [s120, tohost]; omega)⟩
  have w2 : ReadWindow (sp + 112#64) 8 := ⟨by rw [s112]; omega, by rw [s112]; omega, Or.inr (by rw [s112, tohost]; omega)⟩
  have a1 : OutLRange [((dom + 288#64).toNat, 8, roots)] (sp + 120#64).toNat 8 := by
    simp only [OutLRange, d288, s120, and_true]; omega
  have a2 : OutLRange [((dom + 288#64).toNat, 8, roots)] (sp + 112#64).toNat 8 := by
    simp only [OutLRange, d288, s112, and_true]; omega
  have out : ImageOutside [((dom + 288#64).toNat, 8, roots)] := by
    apply imageOutside_of_above
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx; show _ ≤ (dom + 288#64).toNat; rw [d288]; omega
  obtain ⟨z', run, post⟩ := (done_fast z ra R leaf ⟨h2, h10, h14, h15, True.intro⟩ w0 w1 (by rw [lg]; exact a1) w2
    (by rw [lg]; exact a2) (by rw [lg]; exact out) ((read8_value _ _).trans wRa) al).run z ⟨pc, rfl⟩
  rw [lg] at post
  refine ⟨z', run, post.toEffectPost, ?_, gholds_lookup _ post.regs (by rfl), ?_⟩
  · rw [← wRa, ← read8_value]; exact gholds_lookup _ post.regs (by rfl)
  · rw [← wS0, ← read8_value]; exact gholds_lookup _ post.regs (by rfl)

/-- `leave`: `a0 := res`, `a5 := Caml_state`, on to the epilogue. -/
theorem leave_step {ra sp p a0 roots dom : BitVec 64} {d : Config} (leaf : LeafInput ra d)
    (regs : HeadRegs sp p a0 roots d) (pc : pcOf d = some exitPc)
    (wD : bytesT d.σ.mem (2147896584 : Nat) 8 = dom)
    (spLow : Layout.sym_bss_end ≤ sp.toNat) (spHigh : sp.toNat + 128 ≤ 2 ^ 32) :
    ∃ z, Steps d z ∧ EffectPost [10, 15] d.σ.mem d donePc (bytesT d.σ.mem (sp + 24#64).toNat 8) z ∧
      gpr z 2 = some sp ∧ gpr z 10 = some (bytesT d.σ.mem (sp + 24#64).toNat 8) ∧ gpr z 14 = some roots ∧
      gpr z 15 = some dom := by
  let R := headR ra sp p a0 roots
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have s24 : (sp + 24#64).toNat = sp.toNat + 24 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have w0 : ReadWindow stateAddr 8 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have w1 : ReadWindow (sp + 24#64) 8 := ⟨by rw [s24]; omega, by rw [s24]; omega, Or.inr (by rw [s24, tohost]; omega)⟩
  obtain ⟨z, run, post⟩ := (leave_fast d R leaf ⟨regs.sp, regs.a0, regs.state, regs.roots, True.intro⟩ w0 w1).run d
    ⟨pc, rfl⟩
  have v1 : bytesVal .ld (read8 d.σ.mem (R 2 + 24#64).toNat) = bytesT d.σ.mem (sp + 24#64).toNat 8 := read8_value _ _
  have v0 : bytesVal .ld (read8 d.σ.mem (R 13).toNat) = dom := (read8_value _ _).trans wD
  refine ⟨z, run, ?_, gholds_lookup _ post.regs (by rfl), ?_, gholds_lookup _ post.regs (by rfl), ?_⟩
  · have e := post.toEffectPost
    simp only [leave_loads, List.getD_cons_succ, List.getD_cons_zero, v1] at e
    exact e
  · rw [← v1]; exact gholds_lookup _ post.regs (by rfl)
  · rw [← v0]; exact gholds_lookup _ post.regs (by rfl)

/-- The empty list's `j` to the epilogue. -/
theorem empty_step {ra sp roots dom : BitVec 64} {e : Config} (leaf : LeafInput ra e)
    (regs : ProRegs ra sp 0#64 roots dom e) (pc : pcOf e = some 0x80016088#64) :
    ∃ z, Steps e z ∧ EffectPost [] e.σ.mem e donePc 1#64 z ∧ gpr z 2 = some sp ∧ gpr z 10 = some 1#64 ∧
      gpr z 14 = some roots ∧ gpr z 15 = some dom := by
  let R : Nat → BitVec 64 := fun n => if n = 1 then ra else if n = 2 then sp else if n = 10 then 1#64
    else if n = 14 then roots else dom
  obtain ⟨z, run, post⟩ := (empty_fast e R leaf ⟨regs.sp, regs.a0, regs.roots, regs.domain, True.intro⟩).run e ⟨pc, rfl⟩
  exact ⟨z, run, post.toEffectPost, gholds_lookup _ post.regs (by rfl), gholds_lookup _ post.regs (by rfl),
    gholds_lookup _ post.regs (by rfl), gholds_lookup _ post.regs (by rfl)⟩

/-- **At `caml_ml_out_channels_list`'s entry**: the caller's `sp` is the
walk's frame `+ 128`, the domain words read the walk's `D`, `Y`, `Lm` and
`roots`, the open-channel list is `w.chs`, the custom allocations are ready
for every listed record and newlib's heap is `H0`. -/
structure OutListInput (w : Walk) (Ready : Nat → Config → Prop) (k : Nat) (cap : Nat) (ra s0 : BitVec 64)
    (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : pcOf c = some entryPc
  stack : gpr c 2 = some (w.sp + 128#64)
  s0 : gpr c 8 = some s0
  idle : c.σ.regs.get? Register.htif_payload_writes = some 0#4
  domain : bytesT c.σ.mem (2147896584#64).toNat 8 = BitVec.ofNat 64 w.D
  roots : bytesT c.σ.mem (BitVec.ofNat 64 w.D + 288#64).toNat 8 = w.roots
  young : word c (w.D + Layout.off_young_ptr) = BitVec.ofNat 64 w.Y
  limit : word c (w.D + Layout.off_young_limit) = BitVec.ofNat 64 w.Lm
  opened : Gc.OpenChannelList c.σ.mem w.chs
  ready : Ready (k + (listedRecs c.σ.mem w.chs).length) c
  heap : OCaml.Vm.Boot.Startup.HeapReady w.H0 cap c


/-- The prologue's stores miss the records, the list head and the domain's
nursery words. -/
theorem pro_outL {w : Walk} {n : Nat} (g : WalkGeometry w n) {ra s0 : BitVec 64} {a : Nat}
    (stk : a < w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) (dom : a < w.D + 288 ∨ w.D + 296 ≤ a) :
    OutL (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots) a := by
  have sph := g.spHigh; have dh := g.domainHigh
  have spk : ∀ k, k ≤ 120 → (w.sp + BitVec.ofNat 64 k).toNat = w.sp.toNat + k := fun k hk =>
    off_toNat (by walk_omega)
  have d288 : (BitVec.ofNat 64 w.D + 288#64).toNat = w.D + 288 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; walk_omega
  simp only [proStoreLog, OutL, spk 112 (by omega), spk 120 (by omega), spk 48 (by omega), spk 24 (by omega),
    spk 32 (by omega), spk 40 (by omega), spk 64 (by omega), spk 56 (by omega), spk 72 (by omega),
    spk 80 (by omega), spk 88 (by omega), d288, and_true]
  omega

theorem pro_outLRange {w : Walk} {n : Nat} (g : WalkGeometry w n) {ra s0 : BitVec 64} {a : Nat}
    (stk : a + 8 ≤ w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) (dom : a + 8 ≤ w.D + 288 ∨ w.D + 296 ≤ a) :
    OutLRange (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots) a 8 := by
  have sph := g.spHigh; have dh := g.domainHigh
  have spk : ∀ k, k ≤ 120 → (w.sp + BitVec.ofNat 64 k).toNat = w.sp.toNat + k := fun k hk =>
    off_toNat (by walk_omega)
  have d288 : (BitVec.ofNat 64 w.D + 288#64).toNat = w.D + 288 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; walk_omega
  simp only [proStoreLog, OutLRange, spk 112 (by omega), spk 120 (by omega), spk 48 (by omega), spk 24 (by omega),
    spk 32 (by omega), spk 40 (by omega), spk 64 (by omega), spk 56 (by omega), spk 72 (by omega),
    spk 80 (by omega), spk 88 (by omega), d288, and_true]
  omega

theorem listedRecs_congr {m m' : Std.ExtHashMap Nat (BitVec 8)} {rs : List Nat}
    (h : ∀ r ∈ rs, (Listed m' (BitVec.ofNat 64 r) ↔ Listed m (BitVec.ofNat 64 r))) :
    listedRecs m' rs = listedRecs m rs := by
  unfold listedRecs
  exact List.filter_congr fun r hr => by simp only [decide_eq_decide]; exact h r hr

/-- A store log missing every record byte other than refcounts keeps the
listed records. -/
theorem listedRecs_keep {w : Walk} {n : Nat} (g : WalkGeometry w n) {m m' : Std.ExtHashMap Nat (BitVec 8)}
    (same : ∀ r ∈ w.chs, ∀ j, j < recBytes → (j < 64 ∨ 68 ≤ j) → bytesT m' (r + j) 1 = bytesT m (r + j) 1) :
    listedRecs m' w.chs = listedRecs m w.chs :=
  listedRecs_congr fun r hr => listed_iff (by have := (g.records r hr).fit; walk_omega)
    fun j hj hn => same r hr j (by walk_omega) hn

/-- **What the prologue's stores keep** from the entry `c` to `e`. -/
structure ProKept (w : Walk) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (Customs : Config → Nat → Prop) (k cap : Nat)
    (c e : Config) : Prop where
  ready : Ready (k + (listedRecs c.σ.mem w.chs).length) e
  heap : OCaml.Vm.Boot.Startup.HeapReady w.H0 cap e
  opened : Gc.OpenChannelList e.σ.mem w.chs
  words : ∀ a, (a + 8 ≤ w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) → (a + 8 ≤ w.D + 288 ∨ w.D + 296 ≤ a) →
    word e a = word c a
  bytes : ∀ a, (a < w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) → (a < w.D + 288 ∨ w.D + 296 ≤ a) →
    bytesT e.σ.mem a 1 = bytesT c.σ.mem a 1
  state : ∀ a, state e a ↔ state c a
  counted : Gc.CustomCountStep Customs c e 0

/-- What the prologue's stores keep: readiness, newlib's heap, the
open-channel list, and every word outside the frame and `local_roots`. -/
theorem pro_keeps {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k cap : Nat}
    {ra s0 : BitVec 64} {c e : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (inp : OutListInput w Ready k cap ra s0 c)
    (me : e.σ.mem = writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots)) :
    ProKept w Ready state Customs k cap c e := by
  have spl := g.spLow; have dl := g.domainLow; have dh := g.domainHigh
  have wkeep : ∀ a, (a + 8 ≤ w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) → (a + 8 ≤ w.D + 288 ∨ w.D + 296 ≤ a) →
      word e a = word c a := fun a h1 h2 => word_keep me (pro_outLRange g h1 h2)
  have bkeep : ∀ a, (a < w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) → (a < w.D + 288 ∨ w.D + 296 ≤ a) →
      (e.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := fun a h1 h2 => by
    rw [me, writeLog_out _ _ _ (pro_outL g h1 h2)]
  have dom : word c Layout.sym_Caml_state = BitVec.ofNat 64 w.D := inp.domain
  have fr := custom.frame_counted _ c e inp.ready (fun a sa => by
    have ap := custom.apart c a sa
    have lr := ap.localRoots
    have da : Gc.domainAddr c Layout.off_local_roots = w.D + 288 := by
      simp only [Gc.domainAddr, dom, BitVec.toNat_ofNat, Layout.off_local_roots]; walk_omega
    rw [da] at lr
    have bs := ap.belowStack
    exact bkeep a (by walk_omega) (by omega)) (wkeep _ (by walk_omega) (by walk_omega))
  refine ⟨fr.ready, ?_, ?_, wkeep, fun a h1 h2 => by rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte]; exact bkeep a h1 h2,
    fr.state, fr.counts⟩
  · obtain ⟨xd, xdIn, xdl, xdh⟩ := g.coverDomain
    refine Gc.HeapReady.keep_windows inp.heap (ws := [⟨w.sp.toNat, w.sp.toNat + 128⟩, ⟨w.D + 288, w.D + 296⟩])
      ?_ fun a ha => ?_
    · simp only [List.forall_mem_cons]
      refine ⟨Or.inr (Or.inl ?_), Or.inl ⟨xd, xdIn, ?_, ?_⟩, fun _ h => absurd h List.not_mem_nil⟩
      all_goals (simp only; walk_omega)
    · have h1 := ha _ List.mem_cons_self
      have h2 := ha ⟨w.D + 288, w.D + 296⟩ (by simp)
      simp only at h1 h2
      exact bkeep a h1 h2
  · exact opened_transfer inp.opened (wkeep _ (by walk_omega) (by walk_omega)) fun r hr => by
      have h := g.records r hr; have := h.domain; have := h.high
      exact wkeep _ (by simp only [Gc.chanOffNext]; walk_omega) (by simp only [Gc.chanOffNext]; walk_omega)

/-- The prologue's saved `ra` and `s0`. -/
theorem pro_saved {w : Walk} {n : Nat} (g : WalkGeometry w n) {ra s0 : BitVec 64} {c e : Config}
    (me : e.σ.mem = writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots)) :
    bytesT e.σ.mem (w.sp + 120#64).toNat 8 = ra ∧ bytesT e.σ.mem (w.sp + 112#64).toNat 8 = s0 := by
  have sph := g.spHigh; have dh := g.domainHigh; have spl := g.spLow
  have spk : ∀ k, k ≤ 120 → (w.sp + BitVec.ofNat 64 k).toNat = w.sp.toNat + k := fun k hk =>
    off_toNat (by walk_omega)
  have d288 : (BitVec.ofNat 64 w.D + 288#64).toNat = w.D + 288 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; walk_omega
  rw [me]
  constructor
  · exact Gc.word_writeLog_at _ _ 1 _ _ rfl (by
      simp only [proStoreLog, List.drop, OutLRange, spk 48 (by omega), spk 24 (by omega), spk 32 (by omega),
        spk 40 (by omega), spk 64 (by omega), spk 56 (by omega), spk 72 (by omega), spk 80 (by omega),
        spk 88 (by omega), spk 120 (by omega), d288, and_true]
      walk_omega)
  · exact Gc.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [proStoreLog, List.drop, OutLRange, spk 48 (by omega), spk 24 (by omega), spk 32 (by omega),
        spk 40 (by omega), spk 64 (by omega), spk 56 (by omega), spk 72 (by omega), spk 80 (by omega),
        spk 88 (by omega), spk 112 (by omega), spk 120 (by omega), d288, and_true]
      walk_omega)

/-- **The walk's invariant at its first visit**, after the prologue. -/
theorem walk_start {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k cap : Nat}
    {ra s0 : BitVec 64} {c e : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (inp : OutListInput w Ready k cap ra s0 c)
    (post : EffectPost [2, 8, 10, 11, 12, 13, 14, 15, 16, 17]
      (writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots)) c headPc 1#64 e)
    (regs : ProRegs ra w.sp (BitVec.ofNat 64 (w.chs.headD 0)) w.roots (BitVec.ofNat 64 w.D) e)
    (ne : w.chs ≠ []) (hS : ∀ a, state c a → w.S a) : WalkAt w Ready state Customs k e [] w.chs e := by
  have spl := g.spLow; have dl := g.domainLow; have dh := g.domainHigh; have dap := g.domainApart
  have nl := g.nurseryLow
  have me := post.memory
  have keeps := pro_keeps custom g inp me
  have recOut : ∀ r ∈ w.chs, ∀ j, j < recBytes → OutL (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots) (r + j) :=
    fun r hr j hj => by
      have h := g.records r hr
      have := h.high; have := h.domain
      exact pro_outL g (by walk_omega) (by walk_omega)
  have recs : ∀ r ∈ w.chs, ∀ j, j < recBytes → bytesT e.σ.mem (r + j) 1 = bytesT c.σ.mem (r + j) 1 :=
    fun r hr j hj => by
      rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte, me, writeLog_out _ _ _ (recOut r hr j hj)]
  have headE : bytesT e.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8 := by
    rw [me]; exact bytesT_writeLog_out _ (pro_outLRange g (by walk_omega) (by walk_omega))
  have openedE : Gc.OpenChannelList e.σ.mem w.chs := opened_transfer inp.opened headE fun r hr =>
    Reloc.bytesT_congr fun i hi => by
      rw [Nat.add_assoc]; exact recs r hr _ (by simp only [Gc.chanOffNext]; walk_omega)
  have listedE : listedRecs e.σ.mem w.chs = listedRecs c.σ.mem w.chs :=
    listedRecs_keep g fun r hr j hj _ => recs r hr j hj
  have wkeep : ∀ a, (a + 8 ≤ w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) → (a + 8 ≤ w.D + 288 ∨ w.D + 296 ≤ a) →
      word e a = word c a := fun a h1 h2 => word_keep me (pro_outLRange g h1 h2)
  have dom : word c Layout.sym_Caml_state = BitVec.ofNat 64 w.D := inp.domain
  refine {
    refwords := fun r hr => by simp [listedRecs]
    counted := ⟨fun h => by simpa [listedRecs] using h⟩
    good := post.good, image := post.image, minstret := post.minstret, tick := post.tick
    link := ⟨ra, regs.link, inp.leaf.aligned⟩
    idle := (post.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans inp.idle
    pc := by rw [post.pc]; simp [ne]
    regs := ⟨1#64, regs.sp, regs.record, regs.a0, regs.state, regs.roots⟩
    saved := fun _ _ => rfl
    gprs := GprsKept.refl e
    output := rfl
    split := by simp
    list := by
      have l := openedE
      unfold Gc.OpenChannelList at l
      rwa [(openChannels_head l).1] at l
    opened := openedE
    records := fun _ _ _ _ _ => rfl
    res := by
      simp only [listedRecs, List.filter_nil, List.length_nil, resWord, ↓reduceIte]
      rw [me]
      exact Gc.word_writeLog_at _ _ 4 _ _ rfl (by
        have spk : ∀ k, k ≤ 120 → (w.sp + BitVec.ofNat 64 k).toNat = w.sp.toNat + k := fun k hk =>
          off_toNat (by have := g.spHigh; walk_omega)
        simp only [proStoreLog, List.drop, OutLRange, spk 24 (by omega), spk 32 (by omega), spk 40 (by omega),
          spk 64 (by omega), spk 56 (by omega), spk 72 (by omega), spk 80 (by omega), spk 88 (by omega), and_true]
        omega)
    domain := by rw [wkeep _ (by walk_omega) (by walk_omega)]; exact dom
    young := by
      simp only [listedRecs, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.sub_zero]
      rw [wkeep _ (by walk_omega) (by walk_omega)]; exact inp.young
    limit := by rw [wkeep _ (by walk_omega) (by walk_omega)]; exact inp.limit
    nursery := fun j r hj => by simp [listedRecs] at hj
    frame := fun _ _ => rfl
    ready := by rw [listedE]; exact keeps.ready
    heap := ⟨w.H0, cap, keeps.heap, fun _ h => h⟩
    stateIn := fun a hs => Or.inl (hS a ((keeps.state a).mp hs)) }

/-- **`caml_ml_out_channels_list` returned**, relative to its entry `c`: `res`
in `a0` with the listed records' objects in the nursery, the caller's `ra`,
`sp`, `s0` and callee-saved registers, `local_roots` restored, and every byte
outside the walk's writes, the frame and `local_roots` as at the entry. -/
structure OutListReturned (w : Walk) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (Customs : Config → Nat → Prop) (k : Nat)
    (ra s0 : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : pcOf d = some ra
  link : gpr d 1 = some ra
  stack : gpr d 2 = some (w.sp + 128#64)
  s0 : gpr d 8 = some s0
  result : gpr d 10 = some (resWord w.Y (listedRecs c.σ.mem w.chs).length)
  saved : ∀ n ∈ calleeSaved, gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput
  idle : d.σ.regs.get? Register.htif_payload_writes = some 0#4
  nursery : NurseryList d.σ.mem w.Y (listedRecs c.σ.mem w.chs)
  young : word d (w.D + Layout.off_young_ptr) = BitVec.ofNat 64 (w.Y - 48 * (listedRecs c.σ.mem w.chs).length)
  limit : word d (w.D + Layout.off_young_limit) = BitVec.ofNat 64 w.Lm
  domain : word d Layout.sym_Caml_state = BitVec.ofNat 64 w.D
  roots : bytesT d.σ.mem (w.D + 288) 8 = w.roots
  opened : Gc.OpenChannelList d.σ.mem w.chs
  frame : ∀ a, ¬ Written w state a → (a < w.sp.toNat ∨ w.sp.toNat + 128 ≤ a) → (a < w.D + 288 ∨ w.D + 296 ≤ a) →
    bytesT d.σ.mem a 1 = bytesT c.σ.mem a 1
  /-- Four-byte readbacks from the native stores, including untouched records. -/
  refwords : ∀ r ∈ w.chs, bytesT d.σ.mem (r + chanOffRefcount) 4 =
    bytesT c.σ.mem (r + chanOffRefcount) 4 +
      (if r ∈ listedRecs c.σ.mem w.chs then 1#32 else 0#32)
  counted : Gc.CustomCountStep Customs c d (listedRecs c.σ.mem w.chs).length
  ready : Ready k d
  heap : ∃ H cap, OCaml.Vm.Boot.Startup.HeapReady H cap d ∧ ∀ x ∈ w.H0, x ∈ H

/-- The walk's frame numbers for the prologue and epilogue. -/
theorem WalkGeometry.proNums {w : Walk} {n : Nat} (g : WalkGeometry w n) :
    ProNums (w.sp + 128#64) (BitVec.ofNat 64 w.D) := by
  have spl := g.spLow; have sph := g.spHigh; have spa := g.spAligned
  have dl := g.domainLow; have dh := g.domainHigh; have da := g.domainAligned
  have s128 : (w.sp + 128#64).toNat = w.sp.toNat + 128 := off_toNat (by walk_omega)
  have dN : (BitVec.ofNat 64 w.D).toNat = w.D := toNat_ofNat_small (by walk_omega)
  exact ⟨by rw [s128]; walk_omega, by rw [s128]; walk_omega, by rw [s128]; omega, by rw [dN]; walk_omega,
    by rw [dN]; walk_omega, by rw [dN]; omega, by rw [dN, s128]; walk_omega⟩

theorem sp_round (sp : BitVec 64) : sp + 128#64 - 128#64 = sp := BitVec.add_sub_cancel _ _

/-- The restore stores preserve the physical custom count and channel list. -/
structure RestoreKept (w : Walk) (Ready : Nat → Config → Prop) (Customs : Config → Nat → Prop)
    (k : Nat) (z f : Config) : Prop where
  bytes : ∀ a, (a < w.D + 288 ∨ w.D + 296 ≤ a) → bytesT f.σ.mem a 1 = bytesT z.σ.mem a 1
  words : ∀ a, (a + 8 ≤ w.D + 288 ∨ w.D + 296 ≤ a) → word f a = word z a
  roots : bytesT f.σ.mem (w.D + 288) 8 = w.roots
  ready : Ready k f
  opened : Gc.OpenChannelList f.σ.mem w.chs
  heap : ∃ H cap, OCaml.Vm.Boot.Startup.HeapReady H cap f ∧ ∀ x ∈ w.H0, x ∈ H
  counted : Gc.CustomCountStep Customs z f 0

/-- The final `local_roots` store keeps everything the return reads, apart from that word. -/
theorem restore_keeps {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n) {z f : Config}
    (mf : f.σ.mem = writeLog z.σ.mem [((BitVec.ofNat 64 w.D + 288#64).toNat, 8, w.roots)])
    (dom : word z Layout.sym_Caml_state = BitVec.ofNat 64 w.D) (ready : Ready k z) (opened : Gc.OpenChannelList z.σ.mem w.chs)
    (heap : ∃ H cap, OCaml.Vm.Boot.Startup.HeapReady H cap z ∧ ∀ x ∈ w.H0, x ∈ H) :
    RestoreKept w Ready Customs k z f := by
  have dh := g.domainHigh; have dl := g.domainLow
  have d288 : (BitVec.ofNat 64 w.D + 288#64).toNat = w.D + 288 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; walk_omega
  have bytes : ∀ a, (a < w.D + 288 ∨ w.D + 296 ≤ a) → (f.σ.mem[a]?).getD 0 = (z.σ.mem[a]?).getD 0 := fun a h => by
    rw [mf, writeLog_out _ _ _ (by simp only [OutL, d288, and_true]; omega)]
  have words : ∀ a, (a + 8 ≤ w.D + 288 ∨ w.D + 296 ≤ a) → word f a = word z a := fun a h =>
    word_keep mf (by simp only [OutLRange, d288, and_true]; omega)
  have fr := custom.frame_counted _ z f ready (fun a sa => by
    have lr := (custom.apart z a sa).localRoots
    have da : Gc.domainAddr z Layout.off_local_roots = w.D + 288 := by
      simp only [Gc.domainAddr, dom, BitVec.toNat_ofNat, Layout.off_local_roots]; walk_omega
    rw [da] at lr
    exact bytes a (by omega)) (words _ (by walk_omega))
  refine ⟨fun a h => by rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte]; exact bytes a h,
    words, ?_, fr.ready, ?_, ?_, fr.counts⟩
  · rw [mf, ← d288]; exact Gc.word_writeLog_at _ _ 0 _ _ rfl trivial
  · exact opened_transfer opened (words _ (by walk_omega)) fun r hr => by
      have h := g.records r hr; have := h.domain; have := h.high; have := h.low
      exact words _ (by simp only [Gc.chanOffNext]; walk_omega)
  · obtain ⟨H, cap, hz, sub⟩ := heap
    obtain ⟨xd, xdIn, xdl, xdh⟩ := g.coverDomain
    refine ⟨H, cap, Gc.HeapReady.keep_windows hz (ws := [⟨w.D + 288, w.D + 296⟩]) ?_ fun a ha => bytes a ?_, sub⟩
    · simp only [List.forall_mem_cons]
      exact ⟨Or.inl ⟨xd, sub _ xdIn, by simp only; omega, by simp only; walk_omega⟩, fun _ h => absurd h List.not_mem_nil⟩
    · have := ha _ List.mem_cons_self; simpa using this

/-- The list head's word at the entry. -/
theorem head_word {w : Walk} {n : Nat} (g : WalkGeometry w n) {c : Config} (opened : Gc.OpenChannelList c.σ.mem w.chs) :
    bytesT c.σ.mem (2147896128#64).toNat 8 = BitVec.ofNat 64 (w.chs.headD 0) := by
  have h := (openChannels_head opened).1
  rw [show (2147896128#64 : BitVec 64).toNat = Layout.sym_caml_all_opened_channels from rfl, ← h, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- **Through the prologue and the walk**, on a non-empty list. -/
theorem out_list_walked {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k cap : Nat} {ra s0 : BitVec 64} {c : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (grows : CustomMemGrows state)
    (inp : OutListInput w Ready k cap ra s0 c) (count : (listedRecs c.σ.mem w.chs).length ≤ n) (ne : w.chs ≠ [])
    (hS : ∀ a, state c a → w.S a) :
    ∃ e d, Steps c d ∧
      EffectPost [2, 8, 10, 11, 12, 13, 14, 15, 16, 17]
        (writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots)) c headPc 1#64 e ∧
      WalkAt w Ready state Customs k e w.chs [] d := by
  obtain ⟨r, rest, hrs⟩ := List.exists_cons_of_ne_nil ne
  have hr := g.records r (by rw [hrs]; simp)
  have nz : BitVec.ofNat 64 (w.chs.headD 0) ≠ 0#64 := by
    rw [hrs, List.headD_cons]; intro z
    have := congrArg BitVec.toNat z
    rw [toNat_ofNat_small (by have := hr.fit; walk_omega)] at this
    have z0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have := hr.low; walk_omega
  obtain ⟨e, run1, post, regs⟩ := pro_go g.proNums inp.leaf inp.pc inp.stack inp.s0 inp.domain
    (head_word g inp.opened) inp.roots nz
  rw [sp_round] at post regs
  have start := walk_start custom g inp post regs ne hS
  obtain ⟨d, run2, walked⟩ := walk_loop custom grows g (by
    rw [listedRecs_keep g (m := c.σ.mem) fun r hr j hj _ => by
      rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte, post.memory,
        writeLog_out _ _ _ (pro_outL g (by have h := g.records r hr; have := h.high; have := g.spLow; walk_omega)
          (by have h := g.records r hr; have := h.domain; have := h.high; have := g.domainHigh; walk_omega))]]
    exact count) start
  exact ⟨e, d, run1.trans run2, post, walked⟩

/-- The frame's upper slots (the CAMLlocal3 frame and the saved `s0`, `ra`)
are outside the walk's writes. -/
theorem slot_not_written {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n) {a : Nat} (lo : w.sp.toNat + 48 ≤ a)
    (hi : a < w.sp.toNat + 128) : ¬ Written w state a := by
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh
  rintro (stk | nur | ⟨r, mem, lo', hi'⟩ | yng | hs | foot)
  · omega
  · walk_omega
  · have := (g.records r mem).high; walk_omega
  · walk_omega
  · obtain ⟨c, ap, _, _⟩ := g.stateApart _ hs
    have := ap.belowStack; walk_omega
  · have := vsaFoot_low foot; walk_omega

/-- A saved word of the prologue's frame, at the walk's exit. -/
theorem saved_slot {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {ra s0 : BitVec 64} {c e d : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (me : e.σ.mem = writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots))
    (walked : WalkAt w Ready state Customs k e w.chs [] d) :
    bytesT d.σ.mem (w.sp + 120#64).toNat 8 = ra ∧ bytesT d.σ.mem (w.sp + 112#64).toNat 8 = s0 := by
  have sph := g.spHigh; have dh := g.domainHigh; have spl := g.spLow
  have spk : ∀ k, k ≤ 120 → (w.sp + BitVec.ofNat 64 k).toNat = w.sp.toNat + k := fun k hk =>
    off_toNat (by walk_omega)
  have d288 : (BitVec.ofNat 64 w.D + 288#64).toNat = w.D + 288 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; walk_omega
  have keep : ∀ off, 48 ≤ off → off + 8 ≤ 128 → bytesT d.σ.mem (w.sp.toNat + off) 8 = bytesT e.σ.mem (w.sp.toNat + off) 8 :=
    fun off lo hi => Reloc.bytesT_congr fun i hi' => walked.frame _ (slot_not_written custom g (by omega) (by omega))
  obtain ⟨sa, sb⟩ := pro_saved g (c := c) me
  constructor
  · rw [spk 120 (by omega), keep 120 (by omega) (by omega), ← spk 120 (by omega)]; exact sa
  · rw [spk 112 (by omega), keep 112 (by omega) (by omega), ← spk 112 (by omega)]; exact sb

/-- The prologue keeps every record byte, so the listed records. -/
theorem pro_listed {w : Walk} {n : Nat} (g : WalkGeometry w n) {ra s0 : BitVec 64} {c e : Config}
    (me : e.σ.mem = writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots)) :
    listedRecs e.σ.mem w.chs = listedRecs c.σ.mem w.chs :=
  listedRecs_keep g fun r hr j hj _ => by
    have h := g.records r hr; have := h.high; have := h.domain; have := g.spLow; have := g.domainHigh
    rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte, me,
      writeLog_out _ _ _ (pro_outL g (by walk_omega) (by walk_omega))]

/-- **From the walk's exit to the return.** -/
theorem out_list_finish {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k cap : Nat} {ra s0 : BitVec 64} {c e d : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (inp : OutListInput w Ready k cap ra s0 c)
    (post : EffectPost [2, 8, 10, 11, 12, 13, 14, 15, 16, 17]
      (writeLog c.σ.mem (proStoreLog w.sp ra s0 (BitVec.ofNat 64 w.D) w.roots)) c headPc 1#64 e)
    (walked : WalkAt w Ready state Customs k e w.chs [] d) (count : (listedRecs c.σ.mem w.chs).length ≤ n) :
    ∃ f, Steps d f ∧ OutListReturned w Ready state Customs k ra s0 c f := by
  have spl := g.spLow; have sph := g.spHigh; have spa := g.spAligned
  have dl := g.domainLow; have dh := g.domainHigh; have da := g.domainAligned
  obtain ⟨r', hr', al'⟩ := walked.link
  have leaf : LeafInput r' d := ⟨walked.good, walked.image, walked.minstret, hr', al', walked.tick⟩
  obtain ⟨a0, regs⟩ := walked.regs
  have pc : pcOf d = some exitPc := by simpa using walked.pc
  have dN : (BitVec.ofNat 64 w.D).toNat = w.D := toNat_ofNat_small (by walk_omega)
  obtain ⟨z, run1, postL, z2, z10, z14, z15⟩ := leave_step leaf regs pc walked.domain (by walk_omega) (by walk_omega)
  have mz : z.σ.mem = d.σ.mem := postL.memory
  obtain ⟨wRa, wS0⟩ := saved_slot custom g post.memory walked
  obtain ⟨f, run2, postD, f1, f2, f8⟩ := done_step (ra := ra) (s0 := s0) (postL.leafInput (by decide) (by decide) leaf) postL.pc z2 z10 z14
    z15 (by rw [mz]; exact wRa) (by rw [mz]; exact wS0) inp.leaf.aligned (by walk_omega) (by walk_omega) spa
    (by rw [dN]; walk_omega) (by rw [dN]; walk_omega) (by rw [dN]; exact da) (by rw [dN]; walk_omega)
  have wz : ∀ a, word z a = word d a := fun a => by unfold word; rw [mz]
  have readyZ : Ready k z := by
    have := walked.ready
    simp only [listedRecs, List.filter_nil, List.length_nil, Nat.add_zero] at this
    exact (custom.frame _ d z this (fun a _ => by rw [mz]) (wz _)).1
  obtain ⟨bytesF, wordsF, rootsF, readyF, openedF, heapF, countedF⟩ := restore_keeps custom g postD.memory
    ((wz _).trans walked.domain) readyZ (by rw [mz]; exact walked.opened)
    (by obtain ⟨H, cap', hd, sub⟩ := walked.heap; exact ⟨H, cap', HeapReady.of_mem hd mz, sub⟩)
  have proKept := pro_keeps custom g inp post.memory
  have countedE := proKept.counted
  have listedE := pro_listed g (c := c) (e := e) post.memory
  have ns : ∀ n ∈ calleeSaved, n ∉ [1, 2, 8] ∧ n ∉ [10, 15] ∧ n ∉ [2, 8, 10, 11, 12, 13, 14, 15, 16, 17] ∧
      1 ≤ n ∧ n ≤ 31 := by decide
  have nurs := walked.nursery
  rw [listedE] at nurs
  refine ⟨f, run1.trans run2, {
    good := postD.good, image := postD.image, minstret := postD.minstret, tick := postD.tick
    pc := postD.pc
    link := f1
    stack := f2
    s0 := f8
    result := by
      rw [postD.result]
      have := walked.res
      rw [listedE] at this
      rw [this]
    saved := fun n hn => by
      obtain ⟨n1, n2, n3, lo, hi⟩ := ns n hn
      exact (postD.gpr_frame (by decide) n lo hi n1).trans ((postL.gpr_frame (by decide) n lo hi n2).trans
        ((walked.saved n hn).trans (post.gpr_frame (by decide) n lo hi n3)))
    gprs := post.kept.trans (walked.gprs.trans (postL.kept.trans postD.kept))
    output := postD.output.trans (postL.output.trans (walked.output.trans post.output))
    idle := (postD.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
      ((postL.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans walked.idle)
    nursery := nurs.frame (by have := g.room; have := g.nurseryHigh; omega) fun a lo hi => by
      have dap := g.domainApart; have nl := g.nurseryLow; have nh := g.nurseryHigh; have rm := g.room
      rw [bytesF a (by walk_omega), Channel.bytesT_one_byte, Channel.bytesT_one_byte, mz]
    young := by rw [wordsF _ (by walk_omega), wz, ← listedE]; exact walked.young
    limit := by rw [wordsF _ (by walk_omega), wz]; exact walked.limit
    domain := by rw [wordsF _ (by walk_omega), wz]; exact walked.domain
    roots := rootsF
    opened := openedF
    frame := fun a hw stk dom => by
      rw [bytesF a dom, Channel.bytesT_one_byte, mz, ← Channel.bytesT_one_byte, walked.frame a hw,
        Channel.bytesT_one_byte, Channel.bytesT_one_byte, post.memory, writeLog_out _ _ _ (pro_outL g stk dom)]
    refwords := by
      intro r hr
      have recordGeo := g.records r hr
      have rh := recordGeo.high; have rd := recordGeo.domain
      have eqF : bytesT f.σ.mem (r + chanOffRefcount) 4 = bytesT d.σ.mem (r + chanOffRefcount) 4 :=
        Reloc.bytesT_congr fun i hi => by
          rw [bytesF _ (by unfold chanOffRefcount; walk_omega), Channel.bytesT_one_byte, mz,
            ← Channel.bytesT_one_byte]
      have eqE : bytesT e.σ.mem (r + chanOffRefcount) 4 = bytesT c.σ.mem (r + chanOffRefcount) 4 :=
        Reloc.bytesT_congr fun i hi => by
          exact proKept.bytes _ (by unfold chanOffRefcount; walk_omega)
            (by unfold chanOffRefcount; walk_omega)
      rw [eqF, walked.refwords r hr, eqE, listedE]
    counted := by
      have step := ((countedE.trans walked.counted).trans
        (custom.accounting.sameMemory mz)).trans countedF
      simpa only [Nat.zero_add, Nat.add_zero, listedE] using step
    ready := readyF
    heap := heapF }⟩

/-- **The empty list**: the prologue, its `j`, the epilogue. -/
theorem out_list_none {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k cap : Nat} {ra s0 : BitVec 64} {c : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (inp : OutListInput w Ready k cap ra s0 c) (empty : w.chs = []) :
    ∃ f, Steps c f ∧ OutListReturned w Ready state Customs k ra s0 c f := by
  have spl := g.spLow; have sph := g.spHigh; have spa := g.spAligned
  have dl := g.domainLow; have dh := g.domainHigh; have da := g.domainAligned
  have dN : (BitVec.ofNat 64 w.D).toNat = w.D := toNat_ofNat_small (by walk_omega)
  have hw := head_word g inp.opened
  rw [empty] at hw
  obtain ⟨e, run1, post, regs⟩ := pro_empty g.proNums inp.leaf inp.pc inp.stack inp.s0 inp.domain hw inp.roots
  rw [sp_round] at post regs
  have me := post.memory
  obtain ⟨readyE, heapE, openedE, wordsE, bytesE, _, countedE⟩ := pro_keeps custom g inp me
  obtain ⟨wRa, wS0⟩ := pro_saved g (c := c) me
  have leafE : LeafInput ra e := post.leafInput (by decide) (by decide) inp.leaf
  obtain ⟨z, run2, postE, z2, z10, z14, z15⟩ := empty_step leafE regs post.pc
  have mz : z.σ.mem = e.σ.mem := postE.memory
  obtain ⟨f, run3, postD, f1, f2, f8⟩ := done_step (ra := ra) (s0 := s0) (postE.leafInput (by decide) (by decide) leafE)
    postE.pc z2 z10 z14 z15 (by rw [mz]; exact wRa) (by rw [mz]; exact wS0) inp.leaf.aligned (by walk_omega)
    (by walk_omega) spa (by rw [dN]; walk_omega) (by rw [dN]; walk_omega) (by rw [dN]; exact da) (by rw [dN]; walk_omega)
  have wz : ∀ a, word z a = word e a := fun a => by unfold word; rw [mz]
  have l0 : listedRecs c.σ.mem w.chs = [] := by rw [empty]; rfl
  rw [l0, List.length_nil, Nat.add_zero] at readyE
  have readyZ : Ready k z := (custom.frame _ e z readyE (fun a _ => by rw [mz]) (wz _)).1
  have domE : word e Layout.sym_Caml_state = BitVec.ofNat 64 w.D := by
    rw [wordsE _ (by walk_omega) (by walk_omega)]; exact inp.domain
  obtain ⟨bytesF, wordsF, rootsF, readyF, openedF, heapF, countedF⟩ := restore_keeps custom g postD.memory
    ((wz _).trans domE) readyZ (by rw [mz]; exact openedE) ⟨w.H0, cap, HeapReady.of_mem heapE mz, fun _ h => h⟩
  have ns : ∀ n ∈ calleeSaved, n ∉ [1, 2, 8] ∧ n ∉ ([] : List Nat) ∧ n ∉ [2, 8, 10, 11, 12, 13, 14, 15, 16, 17] ∧
      1 ≤ n ∧ n ≤ 31 := by decide
  refine ⟨f, run1.trans (run2.trans run3), {
    good := postD.good, image := postD.image, minstret := postD.minstret, tick := postD.tick
    pc := postD.pc
    link := f1
    stack := f2
    s0 := f8
    result := by rw [postD.result, l0]; rfl
    saved := fun n hn => by
      obtain ⟨n1, n2, n3, lo, hi⟩ := ns n hn
      exact (postD.gpr_frame (by decide) n lo hi n1).trans ((postE.gpr_frame (by decide) n lo hi n2).trans
        (post.gpr_frame (by decide) n lo hi n3))
    gprs := post.kept.trans (postE.kept.trans postD.kept)
    output := postD.output.trans (postE.output.trans post.output)
    idle := (postD.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
      ((postE.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
        ((post.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans inp.idle))
    nursery := by rw [l0]; exact fun j r h => by simp at h
    young := by
      rw [l0, List.length_nil, Nat.mul_zero, Nat.sub_zero, wordsF _ (by walk_omega), wz,
        wordsE _ (by walk_omega) (by walk_omega)]
      exact inp.young
    limit := by rw [wordsF _ (by walk_omega), wz, wordsE _ (by walk_omega) (by walk_omega)]; exact inp.limit
    domain := by rw [wordsF _ (by walk_omega), wz]; exact domE
    roots := rootsF
    opened := openedF
    frame := fun a _ stk dom => by
      rw [bytesF a dom, Channel.bytesT_one_byte, mz, ← Channel.bytesT_one_byte]; exact bytesE a stk dom
    refwords := by intro r hr; rw [empty] at hr; simp at hr
    counted := by
      have step := (countedE.trans (custom.accounting.sameMemory mz)).trans countedF
      simpa only [Nat.add_zero, l0, List.length_nil] using step
    ready := readyF
    heap := heapF }⟩

/-- **`caml_ml_out_channels_list` at the machine level**: from its entry to
its return, over any open-channel list. -/
theorem out_list_machine {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k cap : Nat} {ra s0 : BitVec 64} {c : Config} (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n)
    (grows : CustomMemGrows state)
    (inp : OutListInput w Ready k cap ra s0 c) (count : (listedRecs c.σ.mem w.chs).length ≤ n)
    (hS : ∀ a, state c a → w.S a) :
    ∃ f, Steps c f ∧ OutListReturned w Ready state Customs k ra s0 c f := by
  by_cases empty : w.chs = []
  · exact out_list_none custom g inp empty
  · obtain ⟨e, d, run1, post, walked⟩ := out_list_walked custom g grows inp count empty hS
    obtain ⟨f, run2, ret⟩ := out_list_finish custom g inp post walked count
    exact ⟨f, run1.trans run2, ret⟩

end OCaml.Vm.Sim.OutListWalk
