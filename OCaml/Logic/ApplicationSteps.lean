import OCaml.Logic.Application

/-! Push/enter boundaries shared by generated call sites. Decoder premises
come from `CertifiedBlock.decode_sound`; all state effects reduce `stepI`. -/
namespace OCaml.Bytecode

/-- Factor the symbolic instruction boundary once, for every generated
instruction certificate and every application case below. -/
theorem sym_instr {P : Prog} {s t : St} {i : Instr}
    (decode : decodeAt P.code s.pc = some i) (execute : stepI P s i = .next t) :
    Run.iter (bcK P) 1 s = .ok t := by
  rw [Run.iter_one]
  unfold bcK step
  simp only [decode, execute]

/-- APPLY1 pushes the actual caller frame and enters the closure with zero
extra arguments. `call_summary` consumes the resulting state. -/
theorem apply1_enter (P : Prog) (pc dest : Nat) (f arg env : Val) (extra trap : Nat)
    (h : Heap) (w : World) (tail : List Val)
    (decode : decodeAt P.code pc = some ⟨.APPLY1, []⟩)
    (code : field? h f 0 = some (.code dest)) :
    Run.iter (bcK P) 1 ⟨pc, f, arg :: tail, env, extra, trap, h, w⟩ =
      .ok ⟨dest, f, arg :: .code (pc + 1) :: env :: Val.ofInt extra :: tail,
        f, 0, trap, h, w⟩ := by
  apply sym_instr decode
  simp [stepI, enter, code, opt]

/-- Over-applied RETURN re-enters the result closure and decrements extra
arguments. It does not pop a caller return frame. -/
theorem return_over (P : Prog) (pc dest : Nat) (f env : Val) (extra trap : Nat)
    (h : Heap) (w : World) (args tail : List Val)
    (decode : decodeAt P.code pc = some ⟨.RETURN, [args.length]⟩)
    (code : field? h f 0 = some (.code dest)) :
    Run.iter (bcK P) 1 ⟨pc, f, args ++ tail, env, extra + 1, trap, h, w⟩ =
      .ok ⟨dest, f, tail, f, extra, trap, h, w⟩ := by
  apply sym_instr decode
  have guard : ¬ ((args.length : Int) < 0) := by omega
  simp [stepI, guard, enter, code, opt]

/-- Under-applied GRAB allocates a partial closure and immediately restores
the caller frame. RESTART's address is the instruction preceding GRAB. -/
theorem grab_under (P : Prog) (pc req ret : Nat) (a env caller : Val)
    (extra trap : Nat) (saved : BitVec 63) (h : Heap) (w : World) (args tail : List Val)
    (decode : decodeAt P.code pc = some ⟨.GRAB, [req]⟩)
    (arity : extra < req) (count : args.length = 1 + extra) (restart : 1 ≤ pc) :
    Run.iter (bcK P) 1
      ⟨pc, a, args ++ .code ret :: caller :: .int saved :: tail, env, extra, trap, h, w⟩ =
      .ok ⟨ret, .ptr h.objs.length 0, tail, caller, saved.toNat, trap,
        (h.alloc (.block closureTag (.code (pc - 1) :: Val.ofInt 2 :: env :: args))).1, w⟩ := by
  apply sym_instr decode
  have guard : ¬ ((req : Int) < 0) := by omega
  simp only [stepI, guard, if_false]
  have hn : ¬ req ≤ extra := by omega
  have hp : ¬ pc < 1 := by omega
  simp [hn, hp, ← count, Heap.alloc]

/-- RESTART reads a partial closure, prepends its captured arguments and
restores its original environment before the next GRAB. -/
theorem restart_partial (P : Prog) (pc target : Nat) (a env : Val) (extra trap : Nat)
    (h : Heap) (w : World) (args tail : List Val) :
    let obj := Obj.block closureTag (.code target :: Val.ofInt 2 :: env :: args)
    let heap := (h.alloc obj).1
    decodeAt P.code pc = some ⟨.RESTART, []⟩ →
    Run.iter (bcK P) 1
      ⟨pc, a, tail, .ptr (h.alloc obj).2 0, extra, trap, heap, w⟩ =
      .ok ⟨pc + 1, a, args ++ tail, env, extra + args.length, trap, heap, w⟩ := by
  dsimp only
  intro decode
  apply sym_instr decode
  simp only [stepI, Heap.get_alloc_fresh]
  simp [St.adv]

end OCaml.Bytecode
