import OCaml.Vm.Sim.PushtrapArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Native store order for the four-word exception frame and trap pointer. -/
def pushtrapLog (sp domain : Nat) (code link env extra : BitVec 64) : List WEntry :=
  [(sp - 32, 8, code), (sp - 8, 8, extra), (sp - 16, 8, env), (sp - 24, 8, link),
   (domain + Layout.off_trapsp, 8, BitVec.ofNat 64 (sp - 32))]

/-- Exact exception-frame readbacks, in logical stack order. -/
structure PushtrapStored (sp domain : Nat) (code link env extra : BitVec 64) (c : Config) : Prop where
  handler : word c (sp - 32) = code
  linkWord : word c (sp - 24) = link
  environment : word c (sp - 16) = env
  extraArgs : word c (sp - 8) = extra
  trap : word c (domain + Layout.off_trapsp) = BitVec.ofNat 64 (sp - 32)

/-- Distinct frame slots and the disjoint domain field retain their last writes. -/
theorem pushtrap_stored {before after : Config} {sp domain : Nat} {code link env extra : BitVec 64}
    (room : 32 ≤ sp)
    (separate : domain + Layout.off_trapsp + 8 ≤ sp - 32 ∨ sp ≤ domain + Layout.off_trapsp)
    (memory : after.σ.mem = writeLog before.σ.mem (pushtrapLog sp domain code link env extra)) :
    PushtrapStored sp domain code link env extra after := by
  constructor
  · apply word_after_writeLog_at memory 0 _ _ rfl
    simp only [pushtrapLog, List.drop, OutLRange, and_true]
    omega
  · apply word_after_writeLog_at memory 3 _ _ rfl
    simp only [pushtrapLog, List.drop, OutLRange, and_true]
    omega
  · apply word_after_writeLog_at memory 2 _ _ rfl
    simp only [pushtrapLog, List.drop, OutLRange, and_true]
    omega
  · apply word_after_writeLog_at memory 1 _ _ rfl
    simp only [pushtrapLog, List.drop, OutLRange, and_true]
    omega
  · exact word_after_writeLog_at memory 4 _ _ rfl trivial

/-- The exception frame introduces only the existing environment root. -/
theorem pushtrap_roots {P : Prog} {s : St} (dest depth : Nat) :
    ∀ v ∈ [.code dest, Val.ofInt depth, s.env, Val.ofInt s.extra], ∀ l,
      v.loc? = some l → Live s.heap (roots P s) l := by
  intro v member l loc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · cases loc
  · cases loc
  · exact Live.root (by simp [roots]) loc
  · cases loc

/-- Store separation and native geometry for PUSHTRAP, to be supplied by the
loop invariant; stack and domain writes preserve different memory regions. -/
structure PushtrapWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high dest : Nat) (env : BitVec 64) : Prop where
  room : 32 ≤ sp
  highSmall : high < 2^63
  trapBound : s.trap ≤ s.stack.length + 4
  codeWindow : WriteWindow (BitVec.ofNat 64 (sp - 32)) 8
  extraWindow : WriteWindow (BitVec.ofNat 64 (sp - 8)) 8
  envWindow : WriteWindow (BitVec.ofNat 64 (sp - 16)) 8
  linkWindow : WriteWindow (BitVec.ofNat 64 (sp - 24)) 8
  domainAddress : (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp < 2^64
  trapWindow : WriteWindow (word c Layout.sym_Caml_state + BitVec.ofNat 64 Layout.off_trapsp) 8
  separate : (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8 ≤ sp - 32 ∨
    sp ≤ (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp
  payload : TrapWriteOutside
    (pushtrapLog sp (word c Layout.sym_Caml_state).toNat (BitVec.ofNat 64 (pl.codeBase + 4 * dest))
      (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap))) env (tag64 (BitVec.ofNat 63 s.extra))) P s c pl cp sp
  image : ImageOutside
    (pushtrapLog sp (word c Layout.sym_Caml_state).toNat (BitVec.ofNat 64 (pl.codeBase + 4 * dest))
      (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap))) env (tag64 (BitVec.ofNat 63 s.extra)))
  bindings : BindingsOutside
    (pushtrapLog sp (word c Layout.sym_Caml_state).toNat (BitVec.ofNat 64 (pl.codeBase + 4 * dest))
      (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap))) env (tag64 (BitVec.ofNat 63 s.extra))) P c

end OCaml.Vm.Sim
