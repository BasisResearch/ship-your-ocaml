import OCaml.Refinement
import OCaml.Vm.Reloc
import OCaml.Vm.PlatformReloc

/-! Safety interfaces for the minor collector and writing arms.
The remembered-slot list is a ghost view: `RefTableView` is an explicitly
named obligation to connect it to the runtime's concrete ref_table. Nothing
here asserts that an arbitrary Running state satisfies these conditions. -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine Reloc

/-- The runtime's bit/range classifier, on the half-open young interval. -/
def YoungWord (lo hi : Nat) (w : BitVec 64) : Prop :=
  w.toNat % 2 = 0 ∧ lo ≤ w.toNat ∧ w.toNat < hi

/-- Abstract values encountered in roots or scanned live block fields. The
closure's code and infix-header words are included, so their safety matters. -/
def Scanned (P : Prog) (s : St) (v : Val) : Prop :=
  v ∈ roots P s ∨ ∃ l t fs, Live s.heap (roots P s) l ∧
    s.heap.get? l = some (.block t fs) ∧ t < 251 ∧ v ∈ fs

/-- No raw/code/atom/immediate scanned value is young-pointer-shaped.
Supplied by startup and preservation at every bytecode writing arm. -/
def NoForgery (P : Prog) (s : St) (pl : Place) (lo hi : Nat) : Prop :=
  ∀ v w, Scanned P s v → v.loc? = none → valWord pl v = some w → ¬ YoungWord lo hi w

/-- Every live scanned old-to-young field is a remembered slot. Supplied
by caml_modify/caml_initialize and their callers, including global writes. -/
def RememberedComplete (P : Prog) (s : St) (pl : Place) (lo hi : Nat)
    (remembered : List Nat) : Prop :=
  ∀ l a t fs i v w, Live s.heap (roots P s) l → pl.φ l = some a →
    s.heap.get? l = some (.block t fs) → t < 251 →
    ¬ YoungWord lo hi (BitVec.ofNat 64 a) → fs[i]? = some v →
    valWord pl v = some w → YoungWord lo hi w → a + 8 * i ∈ remembered

/-- Concrete contents of a ref-table window. The table-base/end pointer
loads and validity of this window must be supplied by the runtime invariant;
this predicate alone does not identify Caml_state->ref_table. -/
def RefTableView (c : Config) (base limit : Nat) (slots : List Nat) : Prop :=
  base + 8 * slots.length = limit ∧
  ∀ i a, slots[i]? = some a → word c (base + 8 * i) = BitVec.ofNat 64 a

/-- Positive-offset young pointers carry the actual Infix header. -/
def InfixValid (P : Prog) (s : St) (pl : Place) (c : Config) (lo hi : Nat) : Prop :=
  ∀ l k a, Scanned P s (.ptr l k) → pl.φ l = some a → k > 0 →
    YoungWord lo hi (BitVec.ofNat 64 (a + 8 * k)) →
    HeaderOk (word c (a + 8 * k - 8)) k 249

/-- Strengthened collector loop-head relation, parameterised by the current
remembered-table view. Startup/arm suppliers remain open. The nursery can
be nonempty; lo/hi specify bounds, not an empty allocation region. -/
structure LoopHead (L : OCaml.Layout) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (sp high lo hi : Nat)
    (remembered : List Nat) : Prop where
  data : VmReprAt P s c pl cp sp high
  platform : PlatformOk L.runtimeOk c
  loop : LoopRegisters c
  noForgery : NoForgery P s pl lo hi
  rememberedComplete : RememberedComplete P s pl lo hi remembered
  infixValid : InfixValid P s pl c lo hi

/-- Named obligations for each writing arm's summary. Instantiate for the
post-state of SETGLOBAL, SETFIELD0-3/SETFIELD, SETVECTITEM and primitives
that write scanned fields. The machine proof must splice caml_modify (or
caml_initialize for fresh major objects) to establish rememberedComplete.
Allocation/root writes must also maintain noForgery and infixValid.
This is an interface, not a claim that the current ArmSim supplies it. -/
structure WritingArmBarrier (P : Prog) (s' : St) (c' : Config) (pl' : Place)
    (lo hi : Nat) (remembered' : List Nat) : Prop where
  noForgery : NoForgery P s' pl' lo hi
  rememberedComplete : RememberedComplete P s' pl' lo hi remembered'
  infixValid : InfixValid P s' pl' c' lo hi

/-- The safety-enhanced loop head projects to the existing a1 relation. -/
theorem LoopHead.running {L P s c pl cp sp high lo hi remembered}
    (h : LoopHead L P s c pl cp sp high lo hi remembered) : Running L P s c :=
  ⟨⟨pl, cp, sp, high, h.data⟩, h.platform, h.loop⟩

/-- After every scanned field ceases to be young, an empty table is complete.
The collector's concrete reset proof must supply the no-young premise. -/
theorem rememberedComplete_empty {P s pl lo hi}
    (cleared : ∀ v w, Scanned P s v → valWord pl v = some w → ¬ YoungWord lo hi w) :
    RememberedComplete P s pl lo hi [] := by
  intro l a t fs i v w hl _ ho ht _ hv hw hy
  exact False.elim (cleared v w (Or.inr ⟨l, t, fs, hl, ho, ht, List.mem_of_getElem? hv⟩) hw hy)

/-- Reassemble the strengthened loop head after the machine summary has
supplied its images, platform frame, and new safety/barrier facts. -/
theorem LoopHead.reloc {L P s c c' pl cp sp high lo hi remembered remembered' μ}
    (h : LoopHead L P s c pl cp sp high lo hi remembered)
    (data : VmImage P s pl cp sp high μ c c')
    (platform : PlatformFrame L.runtimeOk c c')
    (loop : loopRegistersEqv.Img μ pl 0 0 c c')
    (safety : WritingArmBarrier P s c' (Reloc.reloc μ pl) lo hi remembered') :
    LoopHead L P s c' (Reloc.reloc μ pl) cp sp high lo hi remembered' :=
  ⟨vmReprAt_reloc h.data data, platformOk_reloc μ pl h.platform platform,
    loopRegisters_reloc μ pl h.loop loop,
    safety.noForgery, safety.rememberedComplete, safety.infixValid⟩

end OCaml.Vm.Gc
