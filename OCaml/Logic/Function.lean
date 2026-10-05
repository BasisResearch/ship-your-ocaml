import OCaml.Logic.ApplicationSteps
import OCaml.Logic.Block

namespace OCaml.Bytecode

/-- Reduce a certified local instruction without expanding the surrounding
function or the interpreter's other opcode arms. -/
theorem decoded_sym_step {P : Prog} {decode : Nat → Option Instr} {s t : St}
    {i : Instr} {n : Nat} (hd : decode s.pc = some i)
    (hs : stepI P s i = .next t) :
    Run.iter (decodedK P decode) (n + 1) s = Run.iter (decodedK P decode) n t := by
  rw [Run.iter]
  simp only [decodedK, hd, hs]
  rfl

/-- A concrete symbolic calling shape; its fields may contain arbitrary
arguments, caller frames, heaps and worlds. -/
structure EntryShape (initial : St) (s : St) : Prop where
  state : s = initial

/-- Turn a proved symbolic function run into the shared application interface.
No run obligation is hidden in the precondition. -/
theorem application_of_run {P : Prog} {initial final : St} {n : Nat}
    (run : Run.iter (bcK P) n initial = .ok final) :
    ApplicationSummary P initial.pc (EntryShape initial) (fun _ t => t = final) := by
  constructor
  intro s _ pre
  rcases pre with ⟨rfl⟩
  exact ⟨⟨n, final, run, rfl⟩⟩

/-- Decode a generated arity prefix once for the generic under-application
rule. The resulting application summary includes allocation and caller return. -/
theorem certified_under (P : Prog) (b : CertifiedBlock)
    (pin : P.code.extract b.base (b.base + b.code.size) = b.code)
    (pc req ret : Nat) (a env caller : Val) (extra trap : Nat)
    (saved : BitVec 63) (h : Heap) (w : World) (args tail : List Val)
    (decode : b.decode pc = some ⟨.GRAB, [req]⟩)
    (arity : extra < req) (count : args.length = 1 + extra) (restart : 1 ≤ pc) :
    ApplicationSummary P pc
      (EntryShape ⟨pc, a, args ++ .code ret :: caller :: .int saved :: tail,
        env, extra, trap, h, w⟩)
      (fun _ t => t = ⟨ret, .ptr h.objs.length 0, tail, caller, saved.toNat, trap,
        (h.alloc (.block closureTag (.code (pc - 1) :: Val.ofInt 2 :: env :: args))).1, w⟩) :=
  application_of_run (grab_under P pc req ret a env caller extra trap saved h w args tail
    (b.decode_sound P pin pc _ decode) arity count restart)

end OCaml.Bytecode
