import OCaml.Vm.Sim.ApplyFrameLog
import OCaml.Vm.Sim.ValueWords
import OCaml.Vm.Sim.FrameInsert
import OCaml.Vm.Sim.RetaddrStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Native fixed-arity frame log, based three words below the old stack. -/
def applyFrameLog (sp : Nat) (args : List (BitVec 64)) (code env extra : BitVec 64) : List WEntry :=
  indexedLog (sp - 24) (applyFrameEntries args code env extra)

/-- The saved arguments and caller frame introduce only existing roots. -/
theorem apply_frame_roots {P : Prog} {s : St} (count : Nat) :
    ∀ v ∈ s.stack.take count ++ [.code (s.pc + 1), s.env, Val.ofInt s.extra], ∀ l,
      v.loc? = some l → Live s.heap (roots P s) l := by
  intro v member l loc
  rcases List.mem_append.mp member with argument | saved
  · exact Live.root (by simp [roots, List.mem_of_mem_take argument]) loc
  · exact retaddr_roots (s.pc + 1) v saved l loc

/-- One represented frame-insertion theorem for APPLY1, APPLY2 and APPLY3.
Their native store permutations share the same indexed readback certificate. -/
theorem apply_frame_payload {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {args : List (BitVec 64)} {env : BitVec 64}
    (h : VmPayload P s before pl cp sp high) (room : 24 ≤ sp)
    (positive : 1 ≤ args.length) (small : args.length ≤ 3) (bound : args.length ≤ s.stack.length)
    (arguments : ValueWords pl (s.stack.take args.length) args) (envWord : valWord pl s.env = some env)
    (outside : StackEditOutside (applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
      env (tag64 (BitVec.ofNat 63 s.extra))) P s before pl cp high)
    (memory : after.σ.mem = writeLog before.σ.mem
      (applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) env (tag64 (BitVec.ofNat 63 s.extra))))
    (out : after.σ.sailOutput = before.σ.sailOutput) :
    VmPayload P {s with stack := s.stack.take args.length ++ [.code (s.pc + 1), s.env, Val.ofInt s.extra] ++ s.stack.drop args.length}
      after pl cp (sp - 24) high := by
  have join : sp - 24 + 8 * (args.length + 3) = sp + 8 * args.length := by omega
  have saved : ValueWords pl [.code (s.pc + 1), s.env, Val.ofInt s.extra]
      [BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)), env, tag64 (BitVec.ofNat 63 s.extra)] :=
    ValueWords.cons rfl (ValueWords.cons envWord (ValueWords.cons rfl (ValueWords.nil pl)))
  have represented : ValueWords pl (s.stack.take args.length ++ [.code (s.pc + 1), s.env, Val.ofInt s.extra])
      (applyFrameWords args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) env (tag64 (BitVec.ofNat 63 s.extra))) :=
    arguments.append saved
  have inside := apply_entries_in (sp - 24)
    (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) env (tag64 (BitVec.ofNat 63 s.extra)) positive small
  rw [join] at inside
  apply payload_replace_prefix h bound outside inside memory out
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
    omega
  · intro i v selected
    have index := (List.getElem?_eq_some_iff.mp selected).1
    have wordsBound : i < (applyFrameWords args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
        env (tag64 (BitVec.ofNat 63 s.extra))).length := by rw [represented.length]; exact index
    have wordAt := List.getElem?_eq_getElem wordsBound
    have value := represented.slots i v selected
    rw [wordAt] at value
    rw [value]
    congr 1
    symm
    apply indexed_stored (apply_entries_distinct _ _ _ positive small)
      (apply_entries_selected positive small wordAt) memory
  · exact apply_frame_roots args.length

end OCaml.Vm.Sim
