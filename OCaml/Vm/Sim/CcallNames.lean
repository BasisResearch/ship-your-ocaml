import OCaml.Vm.Sim.CcallRows

/-!
# `CcallReturns` from per-primitive summaries

`CcallReturns L P op ra k` asks, at every reachable `C_CALLk` site, for the
callee's machine summary of whichever F1 primitive the site names. A
primitive's summary is stated once, per name, as `PrimReturnsAt` (exactly the
`CcallReturns.callee` shape; a1-prims' adapters produce it). `of_names`
assembles a list of them, given that every reached call names one of the list
(a per-program checked fact, or `primsF1` itself via `GoodF1`: `of_primsF1`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **One primitive's returning summary at a `C_CALLk` site** (lane a1-prims). -/
def PrimReturnsAt (L : OCaml.Layout) (P : Prog) (op : Opcode) (ra : BitVec 64) (k : Nat)
    (name : String) : Prop :=
  ∀ s c pl cp sp high table entry value env index v heap world, Reach P s →
    CcallReady op L P s c pl cp sp high (domainAt c) table entry value env index name →
    primF1Impl name (s.accu :: s.stack.take k) s.heap s.world = .ok v heap world →
    ∃ result, CcallCallee ra (s.accu :: s.stack.take k) L P s pl cp sp high (domainAt c) entry env
      name v result heap world

/-- **Assembly**: every reached call names a summarized primitive. -/
theorem CcallReturns.of_names {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    {names : List String} (each : ∀ name ∈ names, PrimReturnsAt L P op ra k name)
    (reached : ∀ s c pl cp sp high table entry value env index name, Reach P s →
      CcallReady op L P s c pl cp sp high (domainAt c) table entry value env index name →
      name ∈ primsF1 → name ∈ names) :
    CcallReturns L P op ra k :=
  ⟨fun s c pl cp sp high table entry value env index name v heap world reach ready member ok =>
    each name (reached s c pl cp sp high table entry value env index name reach ready member)
      s c pl cp sp high table entry value env index v heap world reach ready ok⟩

/-- **The general instance**: summaries for all F1 primitives give the C_CALL
returns of every program (no per-program premise). -/
theorem CcallReturns.of_primsF1 {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    (each : ∀ name ∈ primsF1, PrimReturnsAt L P op ra k name) : CcallReturns L P op ra k :=
  .of_names each fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ member => member

theorem _root_.OCaml.Bytecode.Opcode.toNat_lt (o : Opcode) : o.toNat < 149 := by cases o <;> decide

theorem _root_.OCaml.Bytecode.Opcode.toNat_inj {a b : Opcode} (h : a.toNat = b.toNat) : a = b := by
  have ha : a ∈ Opcode.all := by cases a <;> decide
  have hb : b ∈ Opcode.all := by cases b <;> decide
  have e := Opcode.ofNat_toNat a ha
  rw [h, Opcode.ofNat_toNat b hb] at e
  exact (Option.some.inj e).symm

/-- An arm's dispatch word is the program's opcode word at `pc` (code
representation, dispatch fetch, code placement in the arena). -/
theorem ArmInput.fetch {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} (h : ArmInput L P s op c pl cp sp high)
    {w : BitVec 32} (hw : P.code[s.pc]? = some w) : w = BitVec.ofNat 32 op.toNat := by
  have repr := h.code s.pc w hw
  have bound : s.pc < P.code.size := (Array.getElem?_eq_some_iff.mp hw).1
  have arena := h.geometry.codeArena
  have addr : (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)).toNat = pl.codeBase + 4 * s.pc := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [Vsa.Sim.DlHeap.heapEnd] at arena
    omega
  have op := h.dispatch.opcode
  rw [addr] at op
  exact repr.symm.trans op

end OCaml.Vm.Sim
