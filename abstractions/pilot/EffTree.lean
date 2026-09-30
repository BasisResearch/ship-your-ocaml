import Pilot

/-!
# EffTree: instructions as first-order effect trees over VM-state operations

Bake-off entrant for C4 (Layer B′). Each instruction is a term of a small
first-order free monad `Eff` over state operations (`getPc`/`setPc`,
`getAccu`/`setAccu`, `peek`/`poke`/`push`/`pop` on the stack, `halt`,
`wrong`, `unsupported`), run by ONE interpreter `interp`. Locality is ONE
theorem by induction on `Eff` (`interp_frame`): an effect tree whose stack
footprint is `d` (`Eff.Local`) runs the same on `top ++ rest` as on `top`,
with `rest` appended to the result. Lifted to runs (`LRun.frame`) it gives
"from any stack" facts; registers other than the stack stay symbolic
because `interp` computes on an arbitrary state.

`Semantics.lean` is NOT redefined: each opcode is linked to its effect tree
by one `Bridged` fact (`br_*`), which is what adopting `Eff` costs per
opcode on this route.

Section 1 is the abstraction (setup), section 2 the held-out cases H8, H9,
and the scaling probe H9_1000.
-/

namespace OCaml.Pilot.EffTree

open OCaml.Bytecode

/-! ## 1. The abstraction -/

/-- An instruction as a first-order tree of VM-state operations. -/
inductive Eff where
  | ret
  | getPc (k : Nat → Eff)
  | setPc (n : Nat) (e : Eff)
  | getAccu (k : Val → Eff)
  | setAccu (v : Val) (e : Eff)
  /-- read stack slot `i` (`.wrong` if absent) -/
  | peek (i : Nat) (k : Val → Eff)
  /-- overwrite stack slot `i` (`.wrong` if absent) -/
  | poke (i : Nat) (v : Val) (e : Eff)
  | push (v : Val) (e : Eff)
  /-- drop `n` slots (`.wrong` if fewer) -/
  | pop (n : Nat) (e : Eff)
  | halt (code : Nat)
  | wrong
  | unsupported

/-- The one interpreter. -/
def interp : Eff → St → Res
  | .ret, s => .next s
  | .getPc k, s => interp (k s.pc) s
  | .setPc n e, s => interp e { s with pc := n }
  | .getAccu k, s => interp (k s.accu) s
  | .setAccu v e, s => interp e { s with accu := v }
  | .peek i k, s => match s.stack[i]? with
      | some v => interp (k v) s
      | none => .wrong
  | .poke i v e, s =>
      if i < s.stack.length then interp e { s with stack := s.stack.set i v } else .wrong
  | .push v e, s => interp e { s with stack := v :: s.stack }
  | .pop n e, s => if n ≤ s.stack.length then interp e { s with stack := s.stack.drop n } else .wrong
  | .halt c, s => .halt c s.world
  | .wrong, _ => .wrong
  | .unsupported, _ => .unsupported

/-- Stack footprint: every stack access stays within the top `d` slots
(`d` tracks pushes and pops along each path). -/
def Eff.Local : Eff → Nat → Prop
  | .getPc k, d => ∀ n, (k n).Local d
  | .setPc _ e, d => e.Local d
  | .getAccu k, d => ∀ v, (k v).Local d
  | .setAccu _ e, d => e.Local d
  | .peek i k, d => i < d ∧ ∀ v, (k v).Local d
  | .poke i _ e, d => i < d ∧ e.Local d
  | .push _ e, d => e.Local (d + 1)
  | .pop n e, d => n ≤ d ∧ e.Local (d - n)
  | _, _ => True

/-- Put `rest` under the stack. -/
def frameSt (s : St) (rest : List Val) : St := { s with stack := s.stack ++ rest }

def frameRes (rest : List Val) : Res → Res
  | .next s => .next (frameSt s rest)
  | r => r

/-- LOCALITY (by induction on `Eff`): cells below the footprint are neither
read nor written. -/
theorem interp_frame (rest : List Val) :
    ∀ (e : Eff) (d : Nat) (s : St), e.Local d → d ≤ s.stack.length →
      interp e (frameSt s rest) = frameRes rest (interp e s) := by
  intro e
  induction e with
  | ret => intros; rfl
  | getPc k ih => intro d s hl hd; exact ih s.pc d s (hl _) hd
  | setPc n e ih => intro d s hl hd; exact ih d { s with pc := n } hl hd
  | getAccu k ih => intro d s hl hd; exact ih s.accu d s (hl _) hd
  | setAccu v e ih => intro d s hl hd; exact ih d { s with accu := v } hl hd
  | peek i k ih =>
      intro d s hl hd
      have hi : i < s.stack.length := by have := hl.1; omega
      obtain ⟨v, hv⟩ : ∃ v, s.stack[i]? = some v := ⟨_, List.getElem?_eq_getElem hi⟩
      have h2 : (s.stack ++ rest)[i]? = some v := by rw [List.getElem?_append_left hi, hv]
      simp only [interp, frameSt, h2, hv]
      exact ih v d s (hl.2 v) hd
  | poke i v e ih =>
      intro d s hl hd
      have hi : i < s.stack.length := by have := hl.1; omega
      have := ih d { s with stack := s.stack.set i v } hl.2 (by simpa using hd)
      simp only [interp, frameSt, List.length_append, hi, List.set_append_left _ _ hi,
        show i < s.stack.length + rest.length by omega, ite_true] at this ⊢
      exact this
  | push v e ih =>
      intro d s hl hd
      exact ih (d + 1) { s with stack := v :: s.stack } hl (by simpa using hd)
  | pop n e ih =>
      intro d s hl hd
      have hn : n ≤ s.stack.length := by have := hl.1; omega
      have := ih (d - n) { s with stack := s.stack.drop n } hl.2 (by simp; omega)
      simp only [interp, frameSt, List.length_append, hn, List.drop_append_of_le_length hn,
        show n ≤ s.stack.length + rest.length by omega, ite_true] at this ⊢
      exact this
  | halt c => intros; rfl
  | wrong => intros; rfl
  | unsupported => intros; rfl

/-- The effect tree of an instruction (the opcodes H8/H9 use). -/
def effAdv (n : Nat) : Eff := .getPc fun pc => .setPc (pc + n) .ret

def effJump (pc k : Nat) (ofs : Int) : Eff :=
  match target pc k ofs with
  | some t => .setPc t .ret
  | none => .wrong

def effOf (i : Instr) : Eff :=
  match i.op, i.args with
  | .ACC0, [] => .peek 0 fun v => .setAccu v (effAdv 1)
  | .PUSH, [] => .getAccu fun a => .push a (effAdv 1)
  | .CONST2, [] => .setAccu (.int 2) (effAdv 1)
  | .CONSTINT, [n] => .setAccu (Val.ofInt n) (effAdv 2)
  | .ADDINT, [] => .peek 0 fun b => .getAccu fun a =>
      match ints? a b with
      | some (x, y) => .pop 1 (.setAccu (.int (untag (tag64 x + tag64 y - 1))) (effAdv 1))
      | none => .wrong
  | .OFFSETINT, [n] => .getAccu fun
      | .int a => .setAccu (.int (untag (tag64 a + (BitVec.ofInt 64 n <<< 1)))) (effAdv 2)
      | _ => .wrong
  | .ASSIGN, [n] => .getAccu fun a => .poke n.toNat a (.setAccu .unit (effAdv 2))
  | .BRANCH, [ofs] => .getPc fun pc => effJump pc 0 ofs
  | .BLEINT, [n, o] => .getAccu fun
      | .int a => if (BitVec.ofInt 64 n).sle (longVal a) then .getPc fun pc => effJump pc 1 o
                  else effAdv 3
      | _ => .wrong
  | .STOP, [] => .halt 0
  | _, _ => .unsupported

/-- The bridge for one instruction: `stepI` IS its effect tree, whose stack
footprint is `need`. -/
structure Bridged (i : Instr) (need : Nat) : Prop where
  step : ∀ P s, stepI P s i = interp (effOf i) s
  foot : ∀ d, need ≤ d → (effOf i).Local d

/-- A run whose every step is a bridged instruction within the current stack. -/
inductive LRun (P : Prog) : Nat → St → St → Prop where
  | nil (s : St) : LRun P 0 s s
  | cons {n need : Nat} {s s' t : St} {i : Instr} :
      decodeAt P.code s.pc = some i → Bridged i need → need ≤ s.stack.length →
      interp (effOf i) s = .next s' → LRun P n s' t → LRun P (n + 1) s t

theorem LRun.append {P : Prog} {m n : Nat} {a b c : St} (h : LRun P m a b) (h' : LRun P n b c) :
    LRun P (n + m) a c := by
  induction h with
  | nil => exact h'
  | cons hd hb hn hi _ ih => exact .cons hd hb hn hi (ih h')

/-- LOCALITY on runs: a local run is a `BcSem` run on any stack below. -/
theorem LRun.frame {P : Prog} {n : Nat} {s t : St} (rest : List Val) (h : LRun P n s t) :
    StepsN P n (frameSt s rest) (frameSt t rest) := by
  induction h with
  | nil => exact .zero _
  | @cons _ _ s _ _ i hd hb hn hi _ ih =>
      refine .succ (.mk ?_) ih
      have hd' : decodeAt P.code (frameSt s rest).pc = some i := hd
      simp only [step, hd']
      rw [hb.step, interp_frame rest _ _ _ (hb.foot _ hn) (Nat.le_refl _), hi]
      rfl

/-- Loop rule with a rank, once for all loops. -/
theorem LRun.loop {P : Prog} (Inv : Nat → St → Prop) (Post : St → Prop)
    (body : ∀ r s, Inv r s →
      (∃ k t, LRun P k s t ∧ Post t) ∨ ∃ k t r', LRun P k s t ∧ Inv r' t ∧ r' < r) :
    ∀ r s, Inv r s → ∃ k t, LRun P k s t ∧ Post t := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro s hs
    rcases body r s hs with h | ⟨k, t, r', hr, ht, hlt⟩
    · exact h
    · obtain ⟨k', u, hu, hp⟩ := ih r' hlt t ht
      exact ⟨_, _, hr.append hu, hp⟩

/-! ### Bridges, one per opcode -/

/-- The bridge tactic: unfold both sides, split on what the arm inspects. -/
macro "bridge" : tactic => `(tactic| (
  refine ⟨fun P s => ?_, fun d h => ?_⟩
  · rcases s with ⟨pc, accu, stk, env, extra, trap, heap, world⟩
    simp only [stepI, effOf, interp, effAdv, effJump, opt, St.adv, pushAccu, intOp, brOp]
    repeat' (first | split | rfl | (subst_vars; simp_all [interp, effJump, effAdv]))
  · simp only [effOf, Eff.Local, effAdv, effJump]
    repeat' (first | omega | intro _ | split | constructor | simp_all)))

theorem br_ACC0 : Bridged ⟨.ACC0, []⟩ 1 := by bridge
theorem br_PUSH : Bridged ⟨.PUSH, []⟩ 0 := by bridge
theorem br_CONST2 : Bridged ⟨.CONST2, []⟩ 0 := by bridge
theorem br_CONSTINT (n : Int) : Bridged ⟨.CONSTINT, [n]⟩ 0 := by bridge
theorem br_ADDINT : Bridged ⟨.ADDINT, []⟩ 1 := by bridge
theorem br_OFFSETINT (n : Int) : Bridged ⟨.OFFSETINT, [n]⟩ 0 := by bridge
theorem br_ASSIGN (n : Int) : Bridged ⟨.ASSIGN, [n]⟩ (n.toNat + 1) := by bridge
theorem br_BRANCH (o : Int) : Bridged ⟨.BRANCH, [o]⟩ 0 := by bridge
theorem br_BLEINT (n o : Int) : Bridged ⟨.BLEINT, [n, o]⟩ 0 := by bridge
theorem br_STOP : Bridged ⟨.STOP, []⟩ 0 := by bridge

/-- One local step: the decode fact (`decide`, or a hypothesis), the bridge,
the footprint, and the effect tree run by `rfl` (or by `simp` with the
given facts when a branch condition is symbolic). -/
macro "lstep " br:term:max : tactic =>
  `(tactic| refine LRun.cons (by dsimp only; first | assumption | decide) $br (by simp) rfl ?_)
macro "lstep " br:term:max " using " h:term : tactic =>
  `(tactic| refine LRun.cons (by dsimp only; first | assumption | decide) $br (by simp)
    (by simp only [interp, effOf, effAdv, effJump, $h:term]; rfl) ?_)

/-! ## 2. Held-out cases -/

/-- H8 via a local run on the empty stack, framed onto `s.stack`. -/
theorem h8 : OCaml.Pilot.H8 := by
  intro s hpc
  obtain ⟨t, run, hpc', hacc, hstk⟩ : ∃ t, LRun segP 4 { s with stack := [] } t ∧
      t.pc = 5 ∧ t.accu = .int 42 ∧ t.stack = [] := by
    rcases s with ⟨pc, accu, stk, env, extra, trap, heap, world⟩
    obtain rfl : pc = 0 := hpc
    refine ⟨?t, ?run, ?_, ?_, ?_⟩
    case run =>
      lstep (br_CONSTINT 40); lstep br_PUSH; lstep br_CONST2; lstep br_ADDINT; exact .nil _
    all_goals (dsimp only; try decide)
  exact ⟨frameSt t s.stack, run.frame s.stack, hpc', hacc, by simp [frameSt, hstk]⟩

/-! ### H9: the counting loop, generic in its bound `B` -/

/-- Tagged-integer arithmetic the loop needs (`OFFSETINT 1`, `BLEINT B`). -/
theorem tag64_add_shl (a : BitVec 63) (m : BitVec 64) :
    tag64 a + (m <<< 1) = ((a.signExtend 64 + m) <<< 1) ||| 1 := by
  have h : ∀ x : BitVec 64, (x <<< 1) ||| (1 : BitVec 64) = (x <<< 1) + 1 := fun x =>
    (BitVec.add_eq_or_of_and_eq_zero _ _ (by ext i; simp; intro h _; exact h)).symm
  rw [tag64, h, h, BitVec.shiftLeft_add_distrib]
  ac_rfl

theorem untag_shl_or (y : BitVec 64) : untag ((y <<< 1) ||| 1) = y.truncate 63 := by
  ext i hi
  simp [untag, BitVec.getLsbD_sshiftRight, show 1 + i < 64 by omega, show ¬ 64 ≤ i by omega]
  rw [BitVec.getLsbD_eq_getElem (by omega)]

theorem trunc_sext_add (a : BitVec 63) (m : BitVec 64) :
    (a.signExtend 64 + m).truncate 63 = a + m.truncate 63 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_add _ _ (by omega)]
  congr 1
  ext i hi
  simp [BitVec.getLsbD_signExtend, hi]; intro; omega

theorem offsetint_ofNat (i : Nat) :
    untag (tag64 (BitVec.ofNat 63 i) + (BitVec.ofInt 64 1 <<< 1)) = BitVec.ofNat 63 (i + 1) := by
  rw [tag64_add_shl, untag_shl_or, trunc_sext_add, BitVec.ofNat_add]
  rfl

theorem bleint_ofNat (N i : Nat) (hN : N < 2^62) (hi : i < 2^62) :
    (BitVec.ofInt 64 N).sle (longVal (BitVec.ofNat 63 i)) = decide (N ≤ i) := by
  rw [BitVec.sle_eq_decide, longVal, BitVec.toInt_signExtend_of_le (by omega)]
  have h1 : (BitVec.ofInt 64 (N:Int)) = BitVec.ofNat 64 N := by simp
  rw [h1, BitVec.toInt_eq_toNat_of_lt, BitVec.toInt_eq_toNat_of_lt] <;> simp [BitVec.toNat_ofNat] <;> omega

/-- The decode facts of the counting loop with bound `B` (layout of `loopP`). -/
structure LoopCode (P : Prog) (B : Nat) : Prop where
  d0 : decodeAt P.code 0 = some ⟨.ACC0, []⟩
  d1 : decodeAt P.code 1 = some ⟨.BLEINT, [(B : Int), 8]⟩
  d4 : decodeAt P.code 4 = some ⟨.ACC0, []⟩
  d5 : decodeAt P.code 5 = some ⟨.OFFSETINT, [1]⟩
  d7 : decodeAt P.code 7 = some ⟨.ASSIGN, [0]⟩
  d9 : decodeAt P.code 9 = some ⟨.BRANCH, [-10]⟩
  d11 : decodeAt P.code 11 = some ⟨.ACC0, []⟩

/-- Loop invariant at the head, counter `i`, rank `r = B - i`. -/
structure LoopAt (B r i : Nat) (s : St) : Prop where
  rank : r = B - i
  le : i ≤ B
  pc : s.pc = 0
  stk : s.stack = [.int (BitVec.ofNat 63 i)]

theorem loop_spec {P : Prog} {B : Nat} (hc : LoopCode P B) (hB : B < 2^61) :
    ∀ r s, (∃ i, LoopAt B r i s) → ∃ k t, LRun P k s t ∧ t.pc = 12 ∧ t.accu = .int (BitVec.ofNat 63 B) := by
  obtain ⟨d0, d1, d4, d5, d7, d9, d11⟩ := hc
  refine LRun.loop (fun r s => ∃ i, LoopAt B r i s) _ ?_
  rintro r ⟨pc, accu, stk, env, extra, trap, heap, world⟩ ⟨i, rfl, hi, hpc, hs⟩
  obtain rfl : pc = 0 := hpc
  obtain rfl : stk = _ := hs
  by_cases hlt : i < B
  · have hcnd : (BitVec.ofInt 64 (B : Int)).sle (longVal (BitVec.ofNat 63 i)) = false := by
      rw [bleint_ofNat B i (by omega) (by omega)]; simp; omega
    refine .inr ⟨6, ?t, B - (i + 1), ?run, ⟨i + 1, rfl, by omega, ?_, ?_⟩, by omega⟩
    case run =>
      lstep br_ACC0; lstep (br_BLEINT B 8) using hcnd; lstep br_ACC0; lstep (br_OFFSETINT 1)
      lstep (br_ASSIGN 0); lstep (br_BRANCH (-10)); exact .nil _
    · rfl
    · simp only [offsetint_ofNat]; rfl
  · have hcnd : (BitVec.ofInt 64 (B : Int)).sle (longVal (BitVec.ofNat 63 i)) = true := by
      rw [bleint_ofNat B i (by omega) (by omega)]; simp; omega
    obtain rfl : i = B := by omega
    refine .inl ⟨3, ?t2, ?run2, ?_, ?_⟩
    case run2 =>
      lstep br_ACC0; lstep (br_BLEINT i 8) using hcnd; lstep br_ACC0; exact .nil _
    all_goals rfl

/-- H9 = the generic loop at `B = 10`, framed onto `rest`. -/
theorem loopRun {P : Prog} {B : Nat} (hc : LoopCode P B) (hB : B < 2^61) (n : Nat) (rest : List Val)
    (s : St) (hn : n ≤ B) (hpc : s.pc = 0) (hs : s.stack = .int (BitVec.ofNat 63 n) :: rest) :
    ∃ k s', StepsN P k s s' ∧ s'.pc = 12 ∧ s'.accu = .int (BitVec.ofNat 63 B) := by
  obtain ⟨k, t, run, htpc, hacc⟩ :=
    loop_spec hc hB _ { s with stack := [.int (BitVec.ofNat 63 n)] } ⟨n, rfl, hn, hpc, rfl⟩
  have h := run.frame rest
  rw [show frameSt { s with stack := [.int (BitVec.ofNat 63 n)] } rest = s by
    cases s; simp_all [frameSt]] at h
  exact ⟨k, _, h, htpc, hacc⟩

theorem h9 : OCaml.Pilot.H9 := fun n rest s hn hpc hs =>
  loopRun ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by decide) n rest s hn hpc hs

/-! ### Scaling probe: the same loop with bound 1000 -/

def loopP1000 : Prog :=
  ⟨enc [(.ACC0, []), (.BLEINT, [1000, 8]), (.ACC0, []), (.OFFSETINT, [1]), (.ASSIGN, [0]),
        (.BRANCH, [-10]), (.ACC0, []), (.STOP, [])],
   #[], ⟨[]⟩, .atom 0, [], .atom 0, []⟩

def H9_1000 : Prop :=
  ∀ (n : Nat) (rest : List Val) (s : St), n ≤ 1000 → s.pc = 0 →
    s.stack = .int (BitVec.ofNat 63 n) :: rest →
    ∃ k s', StepsN loopP1000 k s s' ∧ s'.pc = 12 ∧ s'.accu = .int 1000

theorem h9_1000 : H9_1000 := fun n rest s hn hpc hs =>
  loopRun ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by decide) n rest s hn hpc hs

end OCaml.Pilot.EffTree
