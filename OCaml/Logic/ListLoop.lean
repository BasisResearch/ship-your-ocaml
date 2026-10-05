import OCaml.Logic.Function

namespace OCaml.Bytecode

/-- A finite OCaml list spine. Elements are arbitrary and may share heap
objects; only the tag-zero two-field cons cells are traversed. -/
inductive ListSpine (h : Heap) : Val → Nat → Prop where
  | nil : ListSpine h (.int 0) 0
  | cons {l : Nat} {head tail : Val} {n : Nat}
      (cell : h.get? l = some (.block 0 [head, tail]))
      (rest : ListSpine h tail n) : ListSpine h (.ptr l 0) (n + 1)

structure LengthContext where
  entry : Nat
  closure : Nat
  ret : Nat
  caller : Val
  saved : BitVec 63
  trap : Nat
  heap : Heap
  world : World
  tail : List Val

def LengthContext.state (c : LengthContext) (n : Nat) (v a : Val) : St :=
  ⟨c.entry, a, .int (BitVec.ofNat 63 n) :: v :: .code c.ret :: c.caller :: .int c.saved :: c.tail,
    .ptr c.closure 0, 1, c.trap, c.heap, c.world⟩

def LengthContext.result (c : LengthContext) (n : Nat) : St :=
  ⟨c.ret, .int (BitVec.ofNat 63 n), c.tail, c.caller, c.saved.toNat, c.trap, c.heap, c.world⟩

/-- The generator supplies these two symbolic paths from actual compiler
bytes. The shared loop proof supplies the invariant and termination. -/
structure LengthCertificate (P : Prog) (c : LengthContext) : Prop where
  body : ∀ n l v a, n + 1 < 2^62 → field? c.heap (.ptr l 0) 1 = some v →
    Run.iter (bcK P) 10 (c.state n (.ptr l 0) a) =
      .ok (c.state (n+1) v (.ptr c.closure 0))
  done : ∀ n a, Run.iter (bcK P) 5 (c.state n (.int 0) a) = .ok (c.result n)

structure LengthWitness (c : LengthContext) (total : Nat) (s : St) where
  count : Nat
  remaining : Nat
  cursor : Val
  accu : Val
  state : s = c.state count cursor accu
  spine : ListSpine c.heap cursor remaining
  sum : count + remaining = total

def LengthInvariant (c : LengthContext) (total : Nat) (s : St) : Prop :=
  Nonempty (LengthWitness c total s)

private theorem length_head (c : LengthContext) (n : Nat) (v a : Val) (hn : n < 2^63) :
    headNat (c.state n v a) = n := by
  simp [headNat, LengthContext.state, Nat.mod_eq_of_lt hn]

/-- Ranked list walking, shared by every recognized length-accumulator loop.
The result is the initial counter plus the number of cons cells, with caller
frame, heap and world restored exactly. -/
theorem length_loop (P : Prog) (c : LengthContext) (cert : LengthCertificate P c)
    (start len : Nat) (v a : Val) (spine : ListSpine c.heap v len)
    (bound : start + len < 2^62) :
    Nonempty (SummaryResult P (c.state start v a) (fun t => t = c.result (start + len))) := by
  let total := start + len
  have body : ∀ s, LengthInvariant c total s → ¬ headNat s = total →
      ∃ k s', Run.iter (bcK P) k s = .ok s' ∧ LengthInvariant c total s' ∧
        total - headNat s' < total - headNat s := by
    intro s inv ne
    rcases inv with ⟨⟨n, rem, cursor, accu, rfl, hs, he⟩⟩
    have hn : n < 2^63 := by dsimp [total] at he; omega
    rw [length_head c n cursor accu hn] at ne
    cases hs with
    | nil => simp at he; exact False.elim (ne he)
    | @cons l head tail remaining cell rest =>
      have hn1 : n + 1 < 2^62 := by dsimp [total] at he; omega
      have read : field? c.heap (.ptr l 0) 1 = some tail := by simp [field?, cell]
      refine ⟨10, c.state (n+1) tail (.ptr c.closure 0), cert.body n l tail accu hn1 read,
        ⟨⟨n+1, remaining, tail, .ptr c.closure 0, rfl, rest, by omega⟩⟩, ?_⟩
      rw [length_head c (n+1) tail _ (by omega), length_head c n (.ptr l 0) accu hn]
      omega
  have done : ∀ s, LengthInvariant c total s → headNat s = total →
      ∃ k s', Run.iter (bcK P) k s = .ok s' ∧ s' = c.result total := by
    intro s inv eq
    rcases inv with ⟨⟨n, rem, cursor, accu, rfl, hs, he⟩⟩
    have hn : n < 2^63 := by dsimp [total] at he; omega
    rw [length_head c n cursor accu hn] at eq
    have hz : rem = 0 := by omega
    subst rem
    cases hs
    exact ⟨5, c.result n, cert.done n accu, by rw [eq]⟩
  obtain ⟨k, t, run, post⟩ := loop_rule (LengthInvariant c total)
    (fun t => t = c.result total) (fun s => total - headNat s) (fun s => headNat s = total)
    body done (c.state start v a) ⟨⟨start, len, v, a, rfl, spine, rfl⟩⟩
  exact ⟨⟨k, t, run, post⟩⟩

/-- The list invariant feeds the same application interface as acyclic
functions; callers use `call_summary` or `tail_summary` unchanged. -/
theorem length_application (P : Prog) (c : LengthContext) (cert : LengthCertificate P c)
    (start len : Nat) (v a : Val) (spine : ListSpine c.heap v len)
    (bound : start + len < 2^62) :
    ApplicationSummary P c.entry (EntryShape (c.state start v a))
      (fun _ t => t = c.result (start + len)) := by
  constructor
  intro s _ pre
  rcases pre with ⟨rfl⟩
  exact length_loop P c cert start len v a spine bound

end OCaml.Bytecode
