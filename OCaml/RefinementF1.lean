import OCaml.Refinement
import OCaml.Fragment

/-!
# Layer A for the F1 fragment: statement and assembly

`Good P` says only that `BcSem` never gets stuck; `BcSem` has since grown
F2–F5 opcodes, primitives and the callback boundary. The F1 target restricts
the programs, never the conclusion:

* `InF1 P i` — a decoded instruction is an F1 opcode, and a `C_CALLk` names an
  F1 primitive (`primsF1`).
* `GoodF1 P` — `Good P`, and every reachable state decodes to an `InF1`
  instruction (so the run never reaches the callback/uncaught-exception
  boundary, which is F4).
* `OcamlrunRefinementF1 L B` — `OcamlrunRefinement L B` with `GoodF1` for
  `Good`; same conclusion (halting behaviours equal, divergence equal).

The assembly: `F1Arms L P R c0` is the per-opcode table (entry, one `.next`
obligation and one `.halt` obligation per F1 opcode) over a loop invariant
`R` of the arm families' choosing (at least `Running`). `F1Arms.simR`
dispatches a `BcSem` step to its opcode's row, and
`ocamlrun_refinementF1_of_arms` gives the headline from the table.
-/

namespace OCaml

open OCaml.Bytecode Vsa.Machine

/-- The primitive a `C_CALLk` instruction names, if it is one. -/
def _root_.OCaml.Bytecode.Instr.ccallName (P : Prog) (i : Instr) : Option String :=
  match i.op, i.args with
  | .C_CALL1, [p] | .C_CALL2, [p] | .C_CALL3, [p] | .C_CALL4, [p] | .C_CALL5, [p] => P.prims[p.toNat]?
  | .C_CALLN, [_, p] => P.prims[p.toNat]?
  | _, _ => none

/-- `Max_young_wosize` (runtime/caml/config.h): larger blocks are allocated in
the major heap (`caml_alloc_shr`), a path outside F1 (Fragment.lean,
`majorAllocLedger`). -/
def maxYoungWosize : Nat := 256

/-- The block an allocating instruction makes fits the minor heap, as
interp.c tests it: MAKEBLOCK `wosize ≤ Max_young_wosize`, CLOSURE
`nvars ≤ Max_young_wosize - 2`, CLOSUREREC `3 nfuncs - 1 + nvars ≤
Max_young_wosize`. Other instructions trivially pass. -/
def _root_.OCaml.Bytecode.Instr.minorAlloc (i : Instr) : Bool :=
  match i.op, i.args with
  | .MAKEBLOCK, sz :: _ => decide (sz ≤ (maxYoungWosize : Int))
  | .CLOSURE, nv :: _ => decide (nv ≤ (maxYoungWosize : Int) - 2)
  | .CLOSUREREC, nf :: nv :: _ => decide (nf * 3 - 1 + nv ≤ (maxYoungWosize : Int))
  | _, _ => true

/-- A decoded instruction inside F1: an F1 opcode, an F1 primitive if it
calls one, and a minor-heap allocation if it allocates. Decidable, so a static
code check is a `decide`. -/
structure InF1 (P : Prog) (i : Instr) : Prop where
  opcode : i.op.fragment = .F1
  primitive : (i.ccallName P).all (· ∈ primsF1) = true
  minor : i.minorAlloc = true

instance (P : Prog) (i : Instr) : Decidable (InF1 P i) :=
  decidable_of_iff (i.op.fragment = .F1 ∧ (i.ccallName P).all (· ∈ primsF1) = true ∧ i.minorAlloc = true)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- The named primitive of an F1 `C_CALLk` is an F1 primitive. -/
theorem InF1.prim {P : Prog} {i : Instr} (h : InF1 P i) {nm : String}
    (hn : i.ccallName P = some nm) : nm ∈ primsF1 := by
  simpa [hn] using h.primitive

/-- `STOP` hands its accumulator to caml_main, which reads a word with low
bits `10` as an exception result (`Is_exception_result`). Represented
non-raw values never have those bits; a `.raw` accumulator at `STOP` is
outside F1. -/
def stopOrdinary (i : Instr) (v : Val) : Bool :=
  match i.op, v with
  | .STOP, .raw _ => false
  | _, _ => true

/-- **The F1 domain.** `Good`, every reachable state is at an F1 instruction
of the main code, and `STOP` never returns a raw word. -/
structure GoodF1 (P : Prog) : Prop where
  good : Good P
  inF1 : ∀ s, Reach P s → ∃ i, decodeAt P.code s.pc = some i ∧ InF1 P i
  stopAccu : ∀ s i, Reach P s → decodeAt P.code s.pc = some i → stopOrdinary i s.accu = true

/-- `GoodF1` from a static check of the code plus the dynamic fact that the
run never leaves it: every decodable word is F1, and reachable PCs decode. -/
theorem GoodF1.of_static {P : Prog} (hg : Good P)
    (static : ∀ pc i, decodeAt P.code pc = some i → InF1 P i)
    (decodes : ∀ s, Reach P s → decodeAt P.code s.pc ≠ none)
    (stopAccu : ∀ s i, Reach P s → decodeAt P.code s.pc = some i → stopOrdinary i s.accu = true) :
    GoodF1 P where
  good := hg
  stopAccu := stopAccu
  inF1 s hr := by
    cases h : decodeAt P.code s.pc with
    | none => exact absurd h (decodes s hr)
    | some i => exact ⟨i, rfl, static _ _ h⟩

/-- **Layer A for F1 (statement).** For every loaded F1 program inside the
budget and the observational GC-safety domain, the machine halts with
`(out, e)` iff `BcSem` does, and diverges iff `BcSem` does. -/
def OcamlrunRefinementF1 (L : Layout) (B : Budget) : Prop :=
  ∀ P c, Loaded L P c → GoodF1 P → Fits B P → GcSafe P →
    (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c)

/-- The full statement implies the F1 one. -/
theorem OcamlrunRefinement.f1 {L : Layout} {B : Budget} (h : OcamlrunRefinement L B) :
    OcamlrunRefinementF1 L B := fun P c hL hg hf hgc => h P c hL hg.good hf hgc

/-! ## The per-opcode table -/

/-- What the machine must do for one `BcSem` outcome from a configuration
related to the pre-state: reach (in at least one step) a configuration
related to the next state, or halt with the final console and exit code.
`.unsupported`/`.wrong` never occur under `Good`. -/
def ArmOutcome (R : St → Config → Prop) (c : Config) : Res → Prop
  | .next s' => ∃ c', Plus c c' ∧ R s' c'
  | .halt e w => Halts c (bytesToString w.console) e
  | _ => True

/-- An arm proved for its `.next` outcomes, with no halting outcome. -/
theorem ArmOutcome.of_next {R : St → Config → Prop} {c : Config} {r : Res}
    (next : ∀ s', r = .next s' → ∃ c', Plus c c' ∧ R s' c')
    (noHalt : ∀ e w, r ≠ .halt e w) : ArmOutcome R c r := by
  cases r with
  | next s' => exact next s' rfl
  | halt e w => exact absurd rfl (noHalt e w)
  | unsupported | wrong => trivial

/-- An arm proved for its `.next` and `.halt` outcomes. -/
theorem ArmOutcome.of_cases {R : St → Config → Prop} {c : Config} {r : Res}
    (next : ∀ s', r = .next s' → ∃ c', Plus c c' ∧ R s' c')
    (halt : ∀ e w, r = .halt e w → Halts c (bytesToString w.console) e) : ArmOutcome R c r := by
  cases r with
  | next s' => exact next s' rfl
  | halt e w => exact halt e w rfl
  | unsupported | wrong => trivial

/-- **One row of the arm table**: the `caml_interprete` arm of `op`, from
any reachable state related by the loop invariant `R` and decoding to an F1
instruction with opcode `op`. -/
def OpArm (P : Prog) (R : St → Config → Prop) (op : Opcode) : Prop :=
  ∀ s c i, Reach P s → R s c → decodeAt P.code s.pc = some i → i.op = op → InF1 P i →
    ArmOutcome R c (stepI P s i)

/-- A row is vacuous for an opcode no reachable state decodes to. -/
theorem OpArm.of_unreached {P : Prog} {R : St → Config → Prop} {op : Opcode}
    (h : ∀ s i, Reach P s → decodeAt P.code s.pc = some i → i.op ≠ op) : OpArm P R op :=
  fun s _ i reach _ hd hop _ => absurd hop (h s i reach hd)

/-- **The F1 arm table** for one program started from `c0`, under a loop
invariant `R` of the arm families' choosing (it contains `Running`, plus what
the families preserve: dispatch clock, native invocation frame, ...). The
`arm` rows belong to the arm lanes (docs/lanes/F1-split.md); `entry` and
the halting rows (`STOP`, `caml_sys_exit`) to bprime. -/
structure F1Arms (P : Prog) (c0 : Config) (R : St → Config → Prop) : Prop where
  entry : ∃ c', Plus c0 c' ∧ R P.init c'
  arm : ∀ op, op.fragment = .F1 → OpArm P R op

/-- **Assembly**: the table is a simulation of every F1 run. -/
theorem F1Arms.simR {P : Prog} {c0 : Config} {R : St → Config → Prop}
    (A : F1Arms P c0 R) (hg : GoodF1 P) : SimR P c0 R := by
  have row : ∀ s c, Reach P s → R s c → ArmOutcome R c (step P s) := by
    intro s c hr hv
    obtain ⟨i, hd, hi⟩ := hg.inF1 s hr
    have hs : step P s = stepI P s i := by simp only [step, hd]
    rw [hs]
    exact A.arm i.op hi.opcode s c i hr hv hd rfl hi
  refine ⟨A.entry, fun s s' c hr hv e => ?_, fun s e w c hr hv h => ?_⟩
  · simpa only [ArmOutcome, e] using row s c hr hv
  · simpa only [ArmOutcome, h] using row s c hr hv

/-- **Layer A for F1 from the arm tables.** For each loaded F1 program in the
domain, some loop invariant carries a complete table. -/
theorem ocamlrun_refinementF1_of_arms {L : Layout} {B : Budget}
    (A : ∀ P c, Loaded L P c → GoodF1 P → Fits B P → GcSafe P → ∃ R, F1Arms P c R) :
    OcamlrunRefinementF1 L B := by
  intro P c hL hg hf hgc
  obtain ⟨R, T⟩ := A P c hL hg hf hgc
  exact (T.simR hg).refines hg.good

/-- The existing `ArmSim` contract restricted to F1 programs is a table over
`LoopAt` (its entry is reused; its `next`/`halt` give every row). -/
theorem ArmSim.f1Arms {L : Layout} {B : Budget} {P : Prog} {c : Config} (A : ArmSim L B P)
    (hL : Loaded L P c) (hg : GoodF1 P) (hf : Fits B P) (hgc : GcSafe P) :
    F1Arms P c (LoopAt L P) where
  entry := A.entry c hL hg.good hf hgc
  arm op _ s c' i hr hv hd _ _ := by
    have hs : step P s = stepI P s i := by simp only [step, hd]
    exact ArmOutcome.of_cases (fun s' e => A.next s s' c' hr hg.good hf hgc hv (hs.trans e))
      (fun e w h => A.halt s e w c' hr hg.good hf hgc hv (hs.trans h))

end OCaml
