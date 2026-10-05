import OCaml.Vm.Sim.ArmInput
import OCaml.RefinementF1

/-!
# From a decoded instruction to the code fetches the arms consume

`decodeAt` reads the opcode word and one signed word per operand; these
lemmas turn a successful decode into `DispatchCode` and the operand fetches,
so every `_next` loop-head simulation becomes an F1 table row.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

theorem Opcode.ofNat?_none (n : Nat) : Opcode.ofNat? (n + 149) = none := rfl

theorem Opcode.ofNat?_small : ∀ n, n < 149 → ∀ o, Opcode.ofNat? n = some o → o.toNat = n := by
  decide

/-- An opcode number decodes only from its own code. -/
theorem Opcode.ofNat?_toNat_eq {n : Nat} {o : Opcode} (h : Opcode.ofNat? n = some o) : o.toNat = n := by
  by_cases small : n < 149
  · exact Opcode.ofNat?_small n small o h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 149 := ⟨n - 149, by omega⟩
    rw [Opcode.ofNat?_none] at h
    cases h

theorem option_mapM_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β} {k : Nat} {b : β}, l.mapM f = some r → r[k]? = some b →
      ∃ x, l[k]? = some x ∧ f x = some b
  | [], r, k, b, h, hb => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    cases hb
  | x :: l, r, k, b, h, hb => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      exact ⟨x, rfl, hy⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hb ⊢
      exact option_mapM_get hys hb

/-- The operand fetches of a decoded instruction. -/
def OperandFetches (P : Prog) (pc : Nat) (args : List Int) : Prop :=
  ∀ k a, args[k]? = some a → ∃ w, P.code[pc + 1 + k]? = some w ∧ w.toInt = a

/-- **Decode to fetch.** -/
theorem decode_fetch {P : Prog} {s : St} {i : Instr} (hd : decodeAt P.code s.pc = some i) :
    DispatchCode P s i.op ∧ OperandFetches P s.pc i.args := by
  simp only [decodeAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
  obtain ⟨n, hn, op, hop, len, -, args, hargs, rfl⟩ := hd
  simp only [Code.word, Option.map_eq_some_iff] at hn
  obtain ⟨w, hw, rfl⟩ := hn
  refine ⟨⟨?_⟩, ?_⟩
  · rw [hw, Opcode.ofNat?_toNat_eq hop]
    simp
  · intro k a ha
    obtain ⟨j, hj, hf⟩ := option_mapM_get hargs ha
    have hjk : j = k := by
      have bound := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_range] at bound
      rw [List.getElem?_range bound] at hj
      exact (Option.some.inj hj).symm
    subst hjk
    simp only [Code.arg, Option.map_eq_some_iff] at hf
    obtain ⟨w', hw', rfl⟩ := hf
    exact ⟨w', hw', rfl⟩

/-! ## Table rows from loop-head simulations -/

/-- A row from a one-operand simulation. `shape`: every other operand list
makes the step `.wrong`; `noHalt`: the opcode never halts. -/
theorem opArm_of_next1 {L : OCaml.Layout} {P : Prog} {op : Opcode}
    (next : ∀ s s' c (w : BitVec 32), Reach P s → OCaml.LoopAt L P s c → DispatchCode P s op →
      P.code[s.pc + 1]? = some w → stepI P s ⟨op, [w.toInt]⟩ = .next s' →
      ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c')
    (shape : ∀ s args, (∀ a, args ≠ [a]) → stepI P s ⟨op, args⟩ = .wrong)
    (noHalt : ∀ s a e w, stepI P s ⟨op, [a]⟩ ≠ .halt e w) :
    OCaml.OpArm P (OCaml.LoopAt L P) op := by
  intro s c i reach h hd hop _
  obtain ⟨code, fetches⟩ := decode_fetch hd
  obtain ⟨o, args⟩ := i
  simp only at hop
  subst hop
  by_cases single : ∃ a, args = [a]
  · obtain ⟨a, rfl⟩ := single
    obtain ⟨w, hw, rfl⟩ := fetches 0 a rfl
    apply OCaml.ArmOutcome.of_next
    · exact fun s' step => next s s' c w reach h code hw step
    · exact noHalt s w.toInt
  · rw [shape s args (fun a ha => single ⟨a, ha⟩)]
    trivial

/-- A row from a two-operand simulation. -/
theorem opArm_of_next2 {L : OCaml.Layout} {P : Prog} {op : Opcode}
    (next : ∀ s s' c (w v : BitVec 32), Reach P s → OCaml.LoopAt L P s c → DispatchCode P s op →
      P.code[s.pc + 1]? = some w → P.code[s.pc + 2]? = some v →
      stepI P s ⟨op, [w.toInt, v.toInt]⟩ = .next s' →
      ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c')
    (shape : ∀ s args, (∀ a b, args ≠ [a, b]) → stepI P s ⟨op, args⟩ = .wrong)
    (noHalt : ∀ s a b e w, stepI P s ⟨op, [a, b]⟩ ≠ .halt e w) :
    OCaml.OpArm P (OCaml.LoopAt L P) op := by
  intro s c i reach h hd hop _
  obtain ⟨code, fetches⟩ := decode_fetch hd
  obtain ⟨o, args⟩ := i
  simp only at hop
  subst hop
  by_cases pair : ∃ a b, args = [a, b]
  · obtain ⟨a, b, rfl⟩ := pair
    obtain ⟨w, hw, rfl⟩ := fetches 0 a rfl
    obtain ⟨v, hv, rfl⟩ := fetches 1 b rfl
    apply OCaml.ArmOutcome.of_next
    · exact fun s' step => next s s' c w v reach h code hw hv step
    · exact noHalt s w.toInt v.toInt
  · rw [shape s args (fun a b hab => pair ⟨a, b, hab⟩)]
    trivial

/-- A row from an operand-free simulation. -/
theorem opArm_of_next0 {L : OCaml.Layout} {P : Prog} {op : Opcode}
    (next : ∀ s s' c, Reach P s → OCaml.LoopAt L P s c → DispatchCode P s op →
      stepI P s ⟨op, []⟩ = .next s' → ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c')
    (shape : ∀ s args, args ≠ [] → stepI P s ⟨op, args⟩ = .wrong)
    (noHalt : ∀ s e w, stepI P s ⟨op, []⟩ ≠ .halt e w) :
    OCaml.OpArm P (OCaml.LoopAt L P) op := by
  intro s c i reach h hd hop _
  obtain ⟨code, -⟩ := decode_fetch hd
  obtain ⟨o, args⟩ := i
  simp only at hop
  subst hop
  by_cases empty : args = []
  · subst empty
    apply OCaml.ArmOutcome.of_next
    · exact fun s' step => next s s' c reach h code step
    · exact noHalt s
  · rw [shape s args empty]
    trivial

end OCaml.Vm.Sim
