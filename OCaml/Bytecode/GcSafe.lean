import OCaml.Bytecode.Semantics

/-! Observational safety for the runtime's Forward-tag shortcut. BcSem itself
stays deterministic; the relations here describe representation changes only. -/
namespace OCaml.Bytecode

/-- A value-bearing position, including roots and arbitrary heap fields.
Code, raw payloads and control metadata are not scanned values. -/
inductive FwdSlot where
  | accu | env | stack (i : Nat) | field (l i : Nat) | named (i : Nat) | argv

def FwdSlot.read (s : St) : FwdSlot → Option Val
  | .accu => some s.accu
  | .env => some s.env
  | .stack i => s.stack[i]?
  | .field l i => field? s.heap (.ptr l 0) i
  | .named i => (s.world.named[i]?).map Prod.snd
  | .argv => some s.world.argv

def FwdSlot.write (s : St) (v : Val) : FwdSlot → St
  | .accu => { s with accu := v }
  | .env => { s with env := v }
  | .stack i => { s with stack := s.stack.set i v }
  | .field l i => { s with heap := (setField? s.heap (.ptr l 0) i v).getD s.heap }
  | .named i => { s with world := { s.world with named := s.world.named.modify i (fun p => (p.1, v)) } }
  | .argv => { s with world := { s.world with argv := v } }

/-- minor_gc.c deliberately retains wrappers around Forward, Lazy and (with
FLAT_FLOAT_ARRAY) Double payloads. In particular a lazy returning another lazy
must not become a request to force the inner lazy. NoForgery separately excludes
out-of-value-area raw pointers; this predicate does not assert that invariant. -/
def ShortcutPayload (h : Heap) (v : Val) : Prop :=
  ∀ t, tag? h v = some t → t ≠ 250 ∧ t ≠ 246 ∧ t ≠ 253

/-- One occurrence of a forced lazy may be replaced by its payload. -/
inductive FwdEdit : St → St → Prop where
  | replace (s : St) (slot : FwdSlot) (l : Nat) (v : Val)
      (block : s.heap.get? l = some (.block 250 [v]))
      (payload : ShortcutPayload s.heap v)
      (atSlot : slot.read s = some (.ptr l 0)) :
      FwdEdit s (slot.write s v)

/-- The forwarding equivalence: finite contextual shortcuts and their inverses.
Occurrences may be replaced independently, so aliases need not change together. -/
inductive FwdEq : St → St → Prop where
  | refl (s : St) : FwdEq s s
  | edit {s t} : FwdEdit s t → FwdEq s t
  | symm {s t} : FwdEq s t → FwdEq t s
  | trans {s t u} : FwdEq s t → FwdEq t u → FwdEq s u

infix:50 " ≈fwd " => FwdEq

/-- Source-checked non-collecting primitive cases used by the force path:
obj.c:caml_obj_tag never allocates; array.c:caml_array_unsafe_get allocates
only for a Double_array_tag argument. The machine boundary proof must justify
these exclusions, including the concrete argument representation. -/
def NonCollectingCall (P : Prog) (s : St) (i : Instr) : Prop :=
  (∃ p, i.op = .C_CALL1 ∧ i.args = [p] ∧ P.prims[p.toNat]? = some "caml_obj_tag") ∨
  (∃ p, i.op = .C_CALL2 ∧ i.args = [p] ∧ P.prims[p.toNat]? = some "caml_array_unsafe_get" ∧
    tag? s.heap s.accu ≠ some doubleArrayTag)

/-- Conservative interpreter collection boundaries: allocating bytecodes,
primitive calls (except the source-checked cases above) and signal checks.
The machine G2 proof must show that every collection is represented at one
of these boundaries. Tag-test/field-read spans inside Lazy.force do not
allocate; allowing a shortcut in the middle would incorrectly reject the
standard library. GRAB and the other primitive calls are conservatively
included even when a particular invocation does not allocate. -/
def CollectionPoint (P : Prog) (s : St) : Prop :=
  ∃ i, decodeAt P.code s.pc = some i ∧ i.op ∈
    [.GRAB, .CLOSURE, .CLOSUREREC, .MAKEBLOCK, .MAKEBLOCK1, .MAKEBLOCK2,
     .MAKEBLOCK3, .MAKEFLOATBLOCK, .GETFLOATFIELD, .C_CALL1, .C_CALL2,
     .C_CALL3, .C_CALL4, .C_CALL5, .C_CALLN, .CHECK_SIGNALS] ∧
    ¬ NonCollectingCall P s i

/-- Reachability closed under earlier collection shortcuts. Restricting safety
to the original deterministic run would miss the states after the first GC. -/
inductive GcReach (P : Prog) : St → Prop where
  | init : GcReach P P.init
  | next {s t} : GcReach P s → Step P s t → GcReach P t
  | collect {s t} : GcReach P s → CollectionPoint P s → s ≈fwd t → GcReach P t

/-- A continuation's externally visible halting observation. -/
def HaltsFrom (P : Prog) (s : St) (out : String) (e : Nat) : Prop :=
  ∃ w, Run.HaltsK (bcK P) s (.halt e w) ∧ bytesToString w.console = out

/-- Only the Layer A observations, not heap identity or intermediate steps. -/
structure FwdObservations (P : Prog) (s t : St) : Prop where
  halt : ∀ out e, HaltsFrom P s out e ↔ HaltsFrom P t out e
  diverge : Run.DivK (bcK P) s ↔ Run.DivK (bcK P) t

/-- GC-safety, beside Good and Fits: at every reachable collection boundary,
forwarding-equivalent states have the same exit code, console output and
divergence. This is observational, not a lockstep/bisimulation requirement:
forcing a wrapper and forcing its payload can take different numbers of steps.
It restricts only actual collection boundaries (conservatively classified above)
and only the runtime's permitted shortcut, rather than banning Forward blocks,
ISINT or Obj operations globally. Reachability includes previous collections.
These are the weakest *observations* required by the current Layer A headline;
the boundary classifier is an explicit conservative approximation. The concrete
collector must separately justify its boundary, representation and progress. -/
def GcSafe (P : Prog) : Prop :=
  ∀ s t, GcReach P s → CollectionPoint P s → s ≈fwd t → FwdObservations P s t

end OCaml.Bytecode
