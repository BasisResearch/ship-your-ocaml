import Pilot

/-! Round-1 bake-off, INCUMBENT entrant: the held-out suite proved directly
in the project's current vocabulary and style (no new abstraction).
Measurements: abstractions/pilot/INCUMBENT.md. -/

namespace OCaml.Pilot.Incumbent

open OCaml.Bytecode OCaml.Vm OCaml.Pilot

/-! ## H1 -/

theorem h1_aux (M : VsaIris.MachineModel) {e e' : Nat} {out out' : String} :
    ∀ {a b b' : M.State}, VsaIris.Reaches M a b → M.step b = .halt e out →
      VsaIris.Reaches M a b' → M.step b' = .halt e' out' → e = e' ∧ out = out' := by
  intro a b b' r1 h1 r2 h2
  induction r1 with
  | refl x =>
    cases r2 with
    | refl => rw [h1] at h2; cases h2; exact ⟨rfl, rfl⟩
    | step s _ => rw [h1] at s; cases s
  | step s r ih =>
    cases r2 with
    | refl => rw [h2] at s; cases s
    | step s' r' => rw [s] at s'; cases s'; exact ih h1 r'

theorem h1 : H1 := by
  intro M σ e e' out out' ⟨_, r1, h1⟩ ⟨_, r2, h2⟩
  exact h1_aux M r1 h1 r2 h2

/-! ## H2 -/

theorem h2 : H2 := by
  intro M a b
  constructor
  · intro r
    induction r with
    | refl x => exact ⟨0, .zero x⟩
    | step s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .succ s hn⟩
  · rintro ⟨n, hn⟩
    exact VsaIris.ReachesN.reaches hn

/-! ## H3 -/

theorem h3 : H3 := by
  intro P hg
  constructor
  · rintro hd ⟨out, e, hh⟩
    exact hh.not_diverges hd
  · intro hn
    rcases halts_or_diverges P hg with ⟨out, e, hh⟩ | hd
    · exact (hn ⟨out, e, hh⟩).elim
    · exact hd

/-! ## H4 -/

theorem h4 : H4 := by
  intro c hns
  constructor
  · rintro hd ⟨out, e, hh⟩
    exact hd.not_halts hh
  · intro hn n
    induction n with
    | zero => exact ⟨c, .zero c⟩
    | succ k ih =>
      obtain ⟨c1, h1⟩ := ih
      rcases hns c1 h1.toSteps with ⟨c2, s⟩ | ⟨e, σ, hh⟩
      · exact ⟨c2, h1.append (.succ s (.zero _))⟩
      · exact (hn ⟨_, e, c1, σ, h1.toSteps, hh, rfl⟩).elim

/-! ## H5 -/

theorem h5 : H5 := by
  intro pl μ
  constructor
  · intro l k a h
    simp [valWord, reloc, h]
  · intro v hv
    cases v <;> simp_all [valWord, reloc, Val.loc?]

/-! ## H6 -/

/-- H6 helper: a one-byte read determines the stored byte. -/
theorem getD_of_bytesT1 {m m' : Std.ExtHashMap Nat (BitVec 8)} {a b : Nat}
    (h : Vsa.Sim.bytesT m a 1 = Vsa.Sim.bytesT m' b 1) : (m[a]?).getD 0 = (m'[b]?).getD 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have := congrArg (fun x => BitVec.getLsbD x k) h
  rw [Vsa.Sim.getLsbD_bytesT _ _ _ _ (by omega), Vsa.Sim.getLsbD_bytesT _ _ _ _ (by omega)] at this
  simpa [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk] using this

/-- H6 helper: reads of equal byte ranges are equal. -/
theorem bytesT_congr {m m' : Std.ExtHashMap Nat (BitVec 8)} :
    ∀ (w x y : Nat), (∀ j, j < w → (m[x + j]?).getD 0 = (m'[y + j]?).getD 0) →
      Vsa.Sim.bytesT m x w = Vsa.Sim.bytesT m' y w := by
  intro w
  induction w with
  | zero => intro _ _ _; rfl
  | succ w ih =>
    intro x y h
    simp only [Vsa.Sim.bytesT]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [ih (x + 1) (y + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show x + (j + 1) = x + 1 + j by omega, show y + (j + 1) = y + 1 + j by omega] at this), h0]

/-- H6 helper: copied bytes give equal reads of any width inside the copy. -/
theorem read_of_copy {c c' : Vsa.Machine.Config} {x y n : Nat}
    (h : ∀ j, j < n → byte c' (x + j) = byte c (y + j)) :
    ∀ off w, off + w ≤ n → Vsa.Sim.bytesT c'.σ.mem (x + off) w = Vsa.Sim.bytesT c.σ.mem (y + off) w := by
  intro off w hw
  apply bytesT_congr
  intro j hj
  have := getD_of_bytesT1 (h (off + j) (by omega))
  rwa [show x + (off + j) = x + off + j by omega, show y + (off + j) = y + off + j by omega] at this

/-- H6's content, without its unused `8 ≤ μ a` premise (reused by `heapRepr_reloc`). -/
theorem objAt_reloc {c c' : Vsa.Machine.Config} {pl : Place} {cp : ChanPlace} {μ : Nat → Nat}
    {a : Nat} {o : Obj} (hobj : ObjAt c pl cp a o) (hdr : word c' (μ a - 8) = word c (a - 8))
    (hfields : ∀ t fs, o = .block t fs → ∀ i v, fs[i]? = some v →
      valWord (reloc μ pl) v = some (word c' (μ a + 8 * i)))
    (hcopy : (∀ t fs, o ≠ .block t fs) → ∀ j, j < 8 * o.wosize + 8 →
      byte c' (μ a + j) = byte c (a + j)) :
    ObjAt c' (reloc μ pl) cp (μ a) o := by
  obtain ⟨hh, hp⟩ := hobj
  refine ⟨by rw [hdr]; exact hh, ?_⟩
  cases o with
  | block t fs => exact hfields t fs rfl
  | bytes b =>
    have hc := hcopy (fun t fs h => by cases h)
    obtain ⟨hb, hpad⟩ := hp
    simp only [Obj.wosize] at hc hpad ⊢
    refine ⟨fun i x hi => ?_, ?_⟩
    · have hlt : i < b.length := by
        rcases Nat.lt_or_ge i b.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hi
      rw [hc i (by omega)]; exact hb i x hi
    · have := hc (8 * (b.length / 8 + 1) - 1) (by omega)
      rw [show μ a + 8 * (b.length / 8 + 1) - 1 = μ a + (8 * (b.length / 8 + 1) - 1) by omega, this,
        show a + (8 * (b.length / 8 + 1) - 1) = a + 8 * (b.length / 8 + 1) - 1 by omega]
      exact hpad
  | double d =>
    have hc := read_of_copy (hcopy (fun t fs h => by cases h))
    have := hc 0 8 (by simp [Obj.wosize])
    simp only [Nat.add_zero] at this
    show Vsa.Sim.bytesT _ _ 8 = d
    rw [this]; exact hp
  | doubleArray ds =>
    have hc := read_of_copy (hcopy (fun t fs h => by cases h))
    intro i d hi
    have hlt : i < ds.length := by
      rcases Nat.lt_or_ge i ds.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hi
    show Vsa.Sim.bytesT _ _ 8 = d
    rw [hc (8 * i) 8 (by simp [Obj.wosize]; omega)]
    exact hp i d hi
  | int64 n =>
    have hc := read_of_copy (hcopy (fun t fs h => by cases h))
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · have := hc 0 8 (by simp [Obj.wosize]); simp only [Nat.add_zero] at this
      show (Vsa.Sim.bytesT _ _ 8).toNat = _; rw [this]; exact h1
    · show Vsa.Sim.bytesT _ _ 8 = n; rw [hc 8 8 (by simp [Obj.wosize])]; exact h2
  | int32 n =>
    have hc := read_of_copy (hcopy (fun t fs h => by cases h))
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · have := hc 0 8 (by simp [Obj.wosize]); simp only [Nat.add_zero] at this
      show (Vsa.Sim.bytesT _ _ 8).toNat = _; rw [this]; exact h1
    · show Vsa.Sim.bytesT _ _ 4 = n; rw [hc 8 4 (by simp [Obj.wosize])]; exact h2
  | nativeint n =>
    have hc := read_of_copy (hcopy (fun t fs h => by cases h))
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · have := hc 0 8 (by simp [Obj.wosize]); simp only [Nat.add_zero] at this
      show (Vsa.Sim.bytesT _ _ 8).toNat = _; rw [this]; exact h1
    · show Vsa.Sim.bytesT _ _ 8 = n; rw [hc 8 8 (by simp [Obj.wosize])]; exact h2
  | channel id =>
    have hc := read_of_copy (hcopy (fun t fs h => by cases h))
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · have := hc 0 8 (by simp [Obj.wosize]); simp only [Nat.add_zero] at this
      show (Vsa.Sim.bytesT _ _ 8).toNat = _; rw [this]; exact h1
    · show cp id = some (Vsa.Sim.bytesT _ _ 8).toNat; rw [hc 8 8 (by simp [Obj.wosize])]; exact h2

theorem h6 : H6 := by
  intro c c' pl cp μ a o hobj _ hdr hfields hcopy
  exact objAt_reloc hobj hdr hfields hcopy

/-! ## Extra C3 components (coordinator's request) -/

/-- (a) `HeapRepr` survives a relocation that moves every live object (H6's
premises per block) and keeps live blocks apart; the rival's hypotheses,
with `ObjMoved` inlined. -/
theorem heapRepr_reloc {c c' : Vsa.Machine.Config} {pl : Place} {cp : ChanPlace} {P : Prog}
    {s : St} {μ : Nat → Nat} (h : HeapRepr c pl cp P s)
    (hmv : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
      word c' (μ a - 8) = word c (a - 8) ∧
      (∀ t fs, o = .block t fs → ∀ i v, fs[i]? = some v →
        valWord (reloc μ pl) v = some (word c' (μ a + 8 * i))) ∧
      ((∀ t fs, o ≠ .block t fs) → ∀ j, j < 8 * o.wosize + 8 → byte c' (μ a + j) = byte c (a + j)))
    (hsep : ∀ l l' a a' o o', Live s.heap (roots P s) l → Live s.heap (roots P s) l' → l ≠ l' →
      pl.φ l = some a → pl.φ l' = some a' → s.heap.get? l = some o → s.heap.get? l' = some o' →
      μ a + 8 * o.wosize ≤ μ a' - 8 ∨ μ a' + 8 * o'.wosize ≤ μ a - 8) :
    HeapRepr c' (reloc μ pl) cp P s := by
  obtain ⟨hobj, _⟩ := h
  refine ⟨fun l hl => ?_, fun l l' x x' o o' hl hl' hne hx hx' ho ho' => ?_⟩
  · obtain ⟨a, o, ha, ho, hat⟩ := hobj l hl
    obtain ⟨hdr, hf, hcp⟩ := hmv l a o hl ha ho
    exact ⟨μ a, o, by simp [reloc, ha], ho, objAt_reloc hat hdr hf hcp⟩
  · simp only [reloc, Option.map_eq_some_iff] at hx hx'
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨a', ha', rfl⟩ := hx'
    exact hsep l l' a a' o o' hl hl' hne ha ha' ho ho'

/-- The rival's statement vocabulary for (b): the word holding `v` after `μ`. -/
def relocWord (μ : Nat → Nat) (pl : Place) : Val → BitVec 64 → BitVec 64
  | .ptr l k, w => match pl.φ l with
    | some a => BitVec.ofNat 64 (μ a + 8 * k)
    | none => w
  | _, w => w

/-- (b) `VmReprAt.globals` survives relocation. -/
theorem globals_reloc {c c' : Vsa.Machine.Config} {pl : Place} {μ : Nat → Nat} {g : Val}
    (h : valWord pl g = some (word c Layout.sym_caml_global_data))
    (hi : word c' Layout.sym_caml_global_data =
      relocWord μ pl g (word c Layout.sym_caml_global_data)) :
    valWord (reloc μ pl) g = some (word c' Layout.sym_caml_global_data) := by
  rw [hi]
  cases g with
  | ptr l k =>
    cases hl : pl.φ l with
    | none => simp [valWord, hl] at h
    | some a => simp [valWord, reloc, relocWord, hl]
  | _ => simpa [valWord, reloc, relocWord] using h

/-! ## H7 -/

theorem h7 : H7 := by
  intro c c' pl μ sp high stk hs hw
  exact ⟨hs.1, hw⟩

/-! ## H8 -/

theorem h8 : H8 := by
  intro s hpc
  obtain ⟨pc, accu, stack, env, extra, trap, heap, world⟩ := s
  simp only at hpc; subst hpc
  refine ⟨⟨5, .int 42, stack, env, extra, trap, heap, world⟩, ?_, rfl, rfl, rfl⟩
  refine .succ (b := ⟨2, Val.ofInt 40, stack, env, extra, trap, heap, world⟩) (.mk rfl) ?_
  refine .succ (b := ⟨3, Val.ofInt 40, Val.ofInt 40 :: stack, env, extra, trap, heap, world⟩)
    (.mk rfl) ?_
  refine .succ (b := ⟨4, .int 2, Val.ofInt 40 :: stack, env, extra, trap, heap, world⟩)
    (.mk rfl) ?_
  exact .succ (.mk rfl) (.zero _)

/-! ## H9 -/

/-- H9 helper: exactly `k` steps, as a function. -/
def runN (P : Prog) : Nat → St → Option St
  | 0, s => some s
  | k + 1, s => match step P s with
    | .next s' => runN P k s'
    | _ => none

/-- H9 helper: `runN` is sound for `StepsN`. -/
theorem runN_sound (P : Prog) : ∀ (k : Nat) (s s' : St), runN P k s = some s' → StepsN P k s s' := by
  intro k
  induction k with
  | zero => intro s s' h; cases h; exact .zero _
  | succ k ih =>
    intro s s' h
    simp only [runN] at h
    split at h
    · rename_i s1 hs; exact .succ (.mk hs) (ih s1 s' h)
    · cases h

/-- H9 helper: `BcSem` runs compose (the machine has this; `BcSem` does not). -/
theorem stepsN_append {P : Prog} {n m : Nat} {a b c : St} (h1 : StepsN P n a b)
    (h2 : StepsN P m b c) : StepsN P (n + m) a c := by
  induction h1 with
  | zero => simpa using h2
  | succ s _ ih => rw [Nat.add_right_comm]; exact .succ s (ih h2)

/-- H9 helper: the loop's state at its head with `i = n` on the stack top. -/
def loopAt (n : Nat) (accu : Val) (rest : List Val) (env : Val) (extra trap : Nat) (heap : Heap)
    (world : World) : St :=
  ⟨0, accu, .int (BitVec.ofNat 63 n) :: rest, env, extra, trap, heap, world⟩

/-- H9 helper: `OFFSETINT 1` on the tagged word, as `step` computes it. -/
def inc (n : Nat) : BitVec 63 := untag (tag64 (BitVec.ofNat 63 n) + (BitVec.ofInt 64 1 <<< 1))

theorem inc_eq (n : Nat) (hn : n < 10) : inc n = BitVec.ofNat 63 (n + 1) := by
  match n, hn with
  | 0, _ => decide | 1, _ => decide | 2, _ => decide | 3, _ => decide | 4, _ => decide
  | 5, _ => decide | 6, _ => decide | 7, _ => decide | 8, _ => decide | 9, _ => decide

/-- H9 helper: one iteration, for each concrete `n < 10`. -/
theorem loop_iter (n : Nat) (hn : n < 10) (accu : Val) (rest : List Val) (env : Val)
    (extra trap : Nat) (heap : Heap) (world : World) :
    StepsN loopP 6 (loopAt n accu rest env extra trap heap world)
      (loopAt (n + 1) .unit rest env extra trap heap world) := by
  unfold loopAt; rw [← inc_eq n hn]
  apply runN_sound
  match n, hn with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl

/-- H9 helper: the exit from `i = 10`. -/
theorem loop_exit (accu : Val) (rest : List Val) (env : Val) (extra trap : Nat) (heap : Heap)
    (world : World) :
    StepsN loopP 3 (loopAt 10 accu rest env extra trap heap world)
      ⟨12, .int 10, .int 10 :: rest, env, extra, trap, heap, world⟩ :=
  runN_sound _ 3 _ _ rfl

theorem loop_from : ∀ (d n : Nat) (accu : Val) (rest : List Val) (env : Val) (extra trap : Nat)
    (heap : Heap) (world : World), n + d = 10 →
    ∃ k s', StepsN loopP k (loopAt n accu rest env extra trap heap world) s' ∧
      s'.pc = 12 ∧ s'.accu = .int 10 := by
  intro d
  induction d with
  | zero =>
    intro n accu rest env extra trap heap world h
    obtain rfl : n = 10 := by omega
    exact ⟨_, _, loop_exit accu rest env extra trap heap world, rfl, rfl⟩
  | succ d ih =>
    intro n accu rest env extra trap heap world h
    obtain ⟨k, s', hk, hpc, hacc⟩ := ih (n + 1) .unit rest env extra trap heap world (by omega)
    exact ⟨_, s', stepsN_append (loop_iter n (by omega) accu rest env extra trap heap world) hk,
      hpc, hacc⟩

theorem h9 : H9 := by
  intro n rest s hn hpc hst
  obtain ⟨pc, accu, stack, env, extra, trap, heap, world⟩ := s
  simp only at hpc hst; subst hpc; subst hst
  exact loop_from (10 - n) n accu rest env extra trap heap world (by omega)

/-! ## H9_1000 (scaling probe; statement copied from `loopP`/`H9`, constant 1000) -/

def loopP1000 : Prog :=
  ⟨enc [(.ACC0, []), (.BLEINT, [1000, 8]), (.ACC0, []), (.OFFSETINT, [1]), (.ASSIGN, [0]),
        (.BRANCH, [-10]), (.ACC0, []), (.STOP, [])],
   #[], ⟨[]⟩, .atom 0, [], .atom 0, []⟩

def H9_1000 : Prop :=
  ∀ (n : Nat) (rest : List Val) (s : St), n ≤ 1000 → s.pc = 0 →
    s.stack = .int (BitVec.ofNat 63 n) :: rest →
    ∃ k s', StepsN loopP1000 k s s' ∧ s'.pc = 12 ∧ s'.accu = .int 1000

/-- H9_1000 helper: the loop test fails below 1000 (kernel-decided per value). -/
theorem bleint1000_false : ∀ n, n < 1000 →
    (BitVec.ofInt 64 1000).sle (longVal (BitVec.ofNat 63 n)) = false := by
  decide +kernel

/-- H9_1000 helper: `OFFSETINT 1` below 1000 (kernel-decided per value). -/
theorem inc1000 : ∀ n, n < 1000 →
    untag (tag64 (BitVec.ofNat 63 n) + (BitVec.ofInt 64 1 <<< 1)) = BitVec.ofNat 63 (n + 1) := by
  decide +kernel

/-- H9_1000 helper: the one symbolic step, `BLEINT` not taken. -/
theorem bleint1000_step (v : BitVec 63) (hc : (BitVec.ofInt 64 1000).sle (longVal v) = false)
    (rest : List Val) (env : Val) (extra trap : Nat) (heap : Heap) (world : World) :
    step loopP1000 ⟨1, .int v, .int v :: rest, env, extra, trap, heap, world⟩ =
      .next ⟨4, .int v, .int v :: rest, env, extra, trap, heap, world⟩ := by
  have hd : decodeAt loopP1000.code 1 = some ⟨.BLEINT, [1000, 8]⟩ := rfl
  simp only [step, hd, stepI, brOp, hc]
  rfl

/-- H9_1000 helper: one iteration, symbolic in the counter. -/
theorem loop1000_iter (n : Nat) (hn : n < 1000) (accu : Val) (rest : List Val) (env : Val)
    (extra trap : Nat) (heap : Heap) (world : World) :
    StepsN loopP1000 6 (loopAt n accu rest env extra trap heap world)
      (loopAt (n + 1) .unit rest env extra trap heap world) := by
  unfold loopAt; rw [← inc1000 n hn]
  exact .succ (.mk rfl) (.succ (.mk (bleint1000_step _ (bleint1000_false n hn) _ _ _ _ _ _))
    (runN_sound _ 4 _ _ rfl))

theorem loop1000_from : ∀ (d n : Nat) (accu : Val) (rest : List Val) (env : Val)
    (extra trap : Nat) (heap : Heap) (world : World), n + d = 1000 →
    ∃ k s', StepsN loopP1000 k (loopAt n accu rest env extra trap heap world) s' ∧
      s'.pc = 12 ∧ s'.accu = .int 1000 := by
  intro d
  induction d with
  | zero =>
    intro n accu rest env extra trap heap world h
    obtain rfl : n = 1000 := by omega
    exact ⟨_, _, runN_sound _ 3 _ ⟨12, .int 1000, .int 1000 :: rest, env, extra, trap, heap, world⟩
      rfl, rfl, rfl⟩
  | succ d ih =>
    intro n accu rest env extra trap heap world h
    obtain ⟨k, s', hk, hpc, hacc⟩ := ih (n + 1) .unit rest env extra trap heap world (by omega)
    exact ⟨_, s', stepsN_append (loop1000_iter n (by omega) accu rest env extra trap heap world) hk,
      hpc, hacc⟩

theorem h9_1000 : H9_1000 := by
  intro n rest s hn hpc hst
  obtain ⟨pc, accu, stack, env, extra, trap, heap, world⟩ := s
  simp only at hpc hst; subst hpc; subst hst
  exact loop1000_from (1000 - n) n accu rest env extra trap heap world (by omega)

end OCaml.Pilot.Incumbent
