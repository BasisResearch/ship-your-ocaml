import OCaml.Vm.Sim.BlockAllocation
import OCaml.Vm.Sim.CopyLogFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- GRAB initializes its environment, copies arguments, then installs code and
arity metadata. This log records that native order. -/
def partialClosureLog (a : Nat) (code env : BitVec 64) (args : List (BitVec 64)) : List WEntry :=
  [(a - 8, 8, blockHeader (args.length + 3) closureTag), (a + 16, 8, env)] ++
    valueLog (a + 24) args ++ [(a, 8, code), (a + 8, 8, 5#64)]

/-- Word-copy readbacks survive arbitrary earlier writes and a disjoint suffix. -/
theorem value_log_framed {pl : Place} {before after : Config} {base : Nat}
    {values : List Val} {words : List (BitVec 64)} {front back : List WEntry}
    (represented : ValueWords pl values words)
    (memory : after.σ.mem = writeLog before.σ.mem ((front ++ valueLog base words) ++ back))
    (outside : OutLRange back base (8 * words.length)) :
    ∀ i v, values[i]? = some v → valWord pl v = some (word after (base + 8 * i)) := by
  apply represented.readback
  intro i w selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have slot : OutLRange back (base + 8 * i) 8 := outLRange_subrange outside (by omega) (by omega)
  change bytesT after.σ.mem _ 8 = w
  rw [memory, writeLog_append, bytesT_writeLog_out _ slot, writeLog_append]
  exact indexed_log_read base (valueEntries words) (value_entries_distinct words) i w
    (value_entries_selected selected) _

/-- Separation is compositional across consecutive exact write logs. -/
theorem outLRange_append {left right : List WEntry} {a n : Nat}
    (hl : OutLRange left a n) (hr : OutLRange right a n) : OutLRange (left ++ right) a n := by
  induction left with
  | nil => exact hr
  | cons entry left ih => exact ⟨hl.1, ih hl.2⟩

/-- Ordinary closures initialize captured fields before installing code and arity. -/
def closureLog (a : Nat) (code : BitVec 64) (captures : List (BitVec 64)) : List WEntry :=
  [(a - 8, 8, blockHeader (captures.length + 2) closureTag)] ++
    valueLog (a + 16) captures ++ [(a, 8, code), (a + 8, 8, 5#64)]

/-- The native closure write order establishes metadata and arbitrary captures
without commuting memory stores. -/
theorem closure_log_layout {pl : Place} {cp : ChanPlace} {before after : Config}
    {a pc : Nat} {args : List Val} {words : List (BitVec 64)}
    (room : 8 ≤ a) (small : words.length + 2 < 2^32)
    (arguments : ValueWords pl args words)
    (memory : after.σ.mem = writeLog before.σ.mem
      (closureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * pc)) words)) :
    ObjAt after pl cp a (.block closureTag ([.code pc, Val.ofInt 2] ++ args)) := by
  have headerCopy : OutLRange (valueLog (a + 16) words) (a - 8) 8 := by
    apply outLRange_of_windows (value_log_in (a + 16) words)
    exact ⟨Or.inl (by dsimp only; omega), trivial⟩
  have header := word_after_writeLog_at memory 0 (a - 8)
    (blockHeader (words.length + 2) closureTag) rfl
    (outLRange_append headerCopy ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩)
  have tailMemory : after.σ.mem = writeLog before.σ.mem
      (([(a - 8, 8, blockHeader (words.length + 2) closureTag)] ++
        valueLog (a + 16) words) ++ [(a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * pc)), (a + 8, 8, 5#64)]) := by
    simpa only [closureLog, List.append_assoc] using memory
  have argsRead := value_log_framed arguments tailMemory
    (show OutLRange [(a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * pc)), (a + 8, 8, 5#64)]
      (a + 16) (8 * words.length) from ⟨Or.inr (by dsimp only; omega), Or.inr (by dsimp only; omega), trivial⟩)
  have suffixRead (i address : Nat) (w : BitVec 64)
      (selected : [(a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * pc)), (a + 8, 8, 5#64)][i]? = some (address, 8, w))
      (outside : OutLRange ([(a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * pc)), (a + 8, 8, 5#64)].drop (i + 1)) address 8) :
      word after address = w := by
    rw [word, tailMemory, writeLog_append]
    exact word_writeLog_at _ _ i address w selected outside
  constructor
  · change HeaderOk (word after (a - 8)) (([.code pc, Val.ofInt 2] ++ args).length) closureTag
    rw [header]
    simpa only [List.length_append, List.length_cons, List.length_nil, arguments.length, Nat.add_comm] using
      block_header_ok (words.length + 2) closureTag small (by decide)
  · intro i v selected
    cases i with
    | zero =>
      cases selected
      simp only [valWord, Nat.mul_zero, Nat.add_zero]
      rw [suffixRead 0 a _ rfl ⟨Or.inl (by omega), trivial⟩]
    | succ i => cases i with
      | zero =>
        cases selected
        change valWord pl (Val.ofInt 2) = some (word after (a + 8))
        rw [suffixRead 1 (a + 8) _ rfl trivial]
        rfl
      | succ i =>
        have read := argsRead i v selected
        simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using read

/-- GRAB is the common closure layout with its environment as the first capture. -/
theorem partial_closure_layout {pl : Place} {cp : ChanPlace} {before after : Config}
    {a pc : Nat} {env : Val} {envWord : BitVec 64} {args : List Val} {words : List (BitVec 64)}
    (room : 8 ≤ a) (small : words.length + 3 < 2^32)
    (environment : valWord pl env = some envWord) (arguments : ValueWords pl args words)
    (memory : after.σ.mem = writeLog before.σ.mem
      (partialClosureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * pc)) envWord words)) :
    ObjAt after pl cp a (.block closureTag ([.code pc, Val.ofInt 2, env] ++ args)) := by
  apply closure_log_layout room (words := envWord :: words) (by simpa using small)
    (ValueWords.cons environment arguments)
  simpa only [closureLog, partialClosureLog, List.length_cons, value_log_cons,
    Nat.add_assoc, List.cons_append, List.nil_append] using memory

end OCaml.Vm.Sim
