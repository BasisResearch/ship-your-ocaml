/-! Toy checks for round-2 R2-3 (standalone, Lean core only). -/

/-! (1) Sort-driven vs bit-driven relocation disagree on an aliasing raw word. -/
inductive Val | int (n : Nat) | ptr (l : Nat) (k : Nat) | raw (w : Nat)
deriving DecidableEq

def enc (pl : Nat → Nat) : Val → Nat
  | .int n => 2*n+1 | .ptr l k => pl l + 8*k | .raw w => w

/-- young range [lo,hi) -/
def young (lo hi w : Nat) : Bool := w % 2 == 0 && lo ≤ w && w < hi

/-- the collector's action on a word: bit-classified (k = 0 pointers only). -/
def gcWord (lo hi : Nat) (fwd : Nat → Nat) (w : Nat) : Nat :=
  if young lo hi w then fwd w else w

/-- H5 as stated (sort-driven): the GC's image of enc v is enc of the relocated placement. -/
def H5stated (lo hi : Nat) (pl fwd : Nat → Nat) (v : Val) : Prop :=
  gcWord lo hi fwd (enc pl v) = enc (fun l => fwd (pl l)) v

-- placement: block 0 at 0x1008 (young), moved to 0x9000.  A raw word 0x1008 in a stack slot.
def pl0 : Nat → Nat := fun _ => 0x1008
def fwd0 : Nat → Nat := fun w => if w == 0x1008 then 0x9000 else w

example : H5stated 0x1000 0x2000 pl0 fwd0 (.ptr 0 0) := by unfold H5stated; decide
example : ¬ H5stated 0x1000 0x2000 pl0 fwd0 (.raw 0x1008) := by unfold H5stated; decide

/-- coherence premise: raw words are odd or outside the young range. -/
def Coh (lo hi : Nat) : Val → Prop
  | .raw w => young lo hi w = false
  | _ => True

theorem h5_coh (lo hi : Nat) (pl fwd : Nat → Nat) (hpl : ∀ l, young lo hi (pl l) = true)
    (v : Val) (hv : Coh lo hi v) (hk : ∀ l k, v = .ptr l k → k = 0) :
    H5stated lo hi pl fwd v := by
  cases v with
  | int n =>
    simp [H5stated, gcWord, enc, young]; all_goals omega
  | ptr l k =>
    have := hk l k rfl; subst this
    simp [H5stated, gcWord, enc, hpl]
  | raw w => simp [H5stated, gcWord, enc, Coh] at *; simp [hv]

/-! (2) Free-monad step: locality proved once by induction on the program. -/
structure St where
  accu : Int
  stack : List Int
  rest : Nat          -- stands for env/heap/world: never an op target here
deriving DecidableEq, Repr

inductive VM (α : Type) where
  | ret (a : α)
  | rdAcc (k : Int → VM α)
  | wrAcc (v : Int) (k : VM α)
  | push (v : Int) (k : VM α)
  | pop (k : Int → VM α)
  | fail

def VM.bind : VM α → (α → VM β) → VM β
  | .ret a, f => f a
  | .rdAcc k, f => .rdAcc (fun v => (k v).bind f)
  | .wrAcc v k, f => .wrAcc v (k.bind f)
  | .push v k, f => .push v (k.bind f)
  | .pop k, f => .pop (fun v => (k v).bind f)
  | .fail, _ => .fail

def run : VM α → St → Option (α × St)
  | .ret a, s => some (a, s)
  | .rdAcc k, s => run (k s.accu) s
  | .wrAcc v k, s => run k { s with accu := v }
  | .push v k, s => run k { s with stack := v :: s.stack }
  | .pop k, s => match s.stack with
      | [] => none
      | v :: vs => run (k v) { s with stack := vs }
  | .fail, _ => none

/-- partial state: accu maybe unknown, known stack prefix, unknown tail. -/
structure PSt where
  accu : Option Int
  pre : List Int
deriving DecidableEq, Repr

def runP : VM α → PSt → Option (α × PSt)
  | .ret a, p => some (a, p)
  | .rdAcc k, p => match p.accu with
      | none => none
      | some a => runP (k a) p
  | .wrAcc v k, p => runP k { p with accu := some v }
  | .push v k, p => runP k { p with pre := v :: p.pre }
  | .pop k, p => match p.pre with
      | [] => none
      | v :: vs => runP (k v) { p with pre := vs }
  | .fail, _ => none

def Agrees (p : PSt) (s : St) : Prop :=
  (∀ a, p.accu = some a → s.accu = a) ∧ ∃ tail, s.stack = p.pre ++ tail

def overlay (p : PSt) (s : St) (tail : List Int) : St :=
  { s with accu := p.accu.getD s.accu, stack := p.pre ++ tail }

theorem runP_accu_mono (m : VM α) : ∀ (p : PSt) a p' x,
    p.accu = some x → runP m p = some (a, p') → ∃ y, p'.accu = some y := by
  induction m with
  | ret b => intro p a p' x hx h; simp [runP] at h; obtain ⟨-, rfl⟩ := h; exact ⟨x, hx⟩
  | rdAcc k ih =>
    intro p a p' x hx h; simp only [runP, hx] at h; exact ih x p a p' x hx h
  | wrAcc v k ih => intro p a p' x hx h; simp only [runP] at h; exact ih _ a p' v rfl h
  | push v k ih => intro p a p' x hx h; simp only [runP] at h; exact ih { p with pre := v :: p.pre } a p' x hx h
  | pop k ih =>
    intro p a p' x hx h; simp only [runP] at h; split at h
    · simp at h
    · rename_i v vs _; exact ih v { p with pre := vs } a p' x hx h
  | fail => intro p a p' x _ h; simp [runP] at h

/-- E1: locality, once, by induction on the program (one case per op). -/
theorem locality (m : VM α) : ∀ (p : PSt) (s : St) (tail : List Int) a p',
    (∀ x, p.accu = some x → s.accu = x) → s.stack = p.pre ++ tail →
    runP m p = some (a, p') → run m s = some (a, overlay p' s tail) := by
  induction m with
  | ret x =>
    intro p s tail a p' hacc hst h
    simp [runP] at h; obtain ⟨rfl, rfl⟩ := h
    simp [run, overlay]; cases s; cases hp : p.accu <;> simp_all
  | rdAcc k ih =>
    intro p s tail a p' hacc hst h
    simp only [runP] at h; split at h
    · simp at h
    · rename_i x hx; simp only [run]; rw [hacc x hx]; exact ih x p s tail a p' hacc hst h
  | wrAcc v k ih =>
    intro p s tail a p' hacc hst h
    simp only [runP] at h; simp only [run]
    have := ih { p with accu := some v } { s with accu := v } tail a p' (by simp) hst h
    rw [this]; obtain ⟨y, hy⟩ := runP_accu_mono k _ a p' v rfl h; simp [overlay, hy]
  | push v k ih =>
    intro p s tail a p' hacc hst h
    simp only [runP] at h; simp only [run]
    have := ih { p with pre := v :: p.pre } { s with stack := v :: s.stack } tail a p' hacc (by simp [hst]) h
    rw [this]; simp [overlay]
  | pop k ih =>
    intro p s tail a p' hacc hst h
    simp only [runP] at h; split at h
    · simp at h
    · rename_i v vs hpre
      simp only [run]; rw [hst, hpre]; simp only [List.cons_append]
      have := ih v { p with pre := vs } { s with stack := vs ++ tail } tail a p' hacc rfl h
      rw [this]; simp [overlay]
  | fail => intro p s tail a p' _ _ h; simp [runP] at h

/-- H8-shaped block: CONSTINT 40; PUSH; CONST2; ADDINT. -/
def h8prog : VM Unit :=
  .wrAcc 40 <| .rdAcc fun a => .push a <| .wrAcc 2 <|
  .rdAcc fun x => .pop fun y => .wrAcc (x + y) (.ret ())

theorem h8_closed : runP h8prog ⟨none, []⟩ = some ((), ⟨some 42, []⟩) := by decide

theorem h8_any (s : St) : run h8prog s = some ((), { s with accu := 42 }) := by
  have := locality h8prog ⟨none, []⟩ s s.stack () ⟨some 42, []⟩ (by simp) (by simp) h8_closed
  rw [this]; simp [overlay]

#print axioms h8_any
#print axioms h5_coh
#print axioms locality
