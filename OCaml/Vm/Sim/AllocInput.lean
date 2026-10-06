import OCaml.Vm.Sim.PlacePut
import OCaml.Vm.Gc.NurseryGeometry
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Sim.ClosureLayout
import OCaml.Vm.Sim.NurseryInput

/-!
# Allocation logs at the loop head

An allocating arm's log is the young-pointer store (`grabReserveLog`) followed
by stores into the reserved nursery block. The store sits inside the
`Caml_state` record, which the stack geometry keeps apart from everything the
payload observes; the block lies in the free nursery (`NurseryGeometry`).
Certificates of the two parts combine (`PayloadOutside.append`, …).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-! ## Certificates of an appended log -/

theorem objectOutside_append {l1 l2 : List WEntry} {a : Nat} {o : Obj}
    (h1 : ObjectOutside l1 a o) (h2 : ObjectOutside l2 a o) : ObjectOutside (l1 ++ l2) a o :=
  ⟨outLRange_append h1.header h2.header, outLRange_append h1.payload h2.payload⟩

theorem _root_.OCaml.Vm.Primitives.PayloadOutside.append {l1 l2 : List WEntry} {P : Prog} {s : St}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp : Nat}
    (h1 : PayloadOutside l1 P s c pl cp sp) (h2 : PayloadOutside l2 P s c pl cp sp) :
    PayloadOutside (l1 ++ l2) P s c pl cp sp :=
  ⟨outLRange_append h1.domain h2.domain, outLRange_append h1.stackHigh h2.stackHigh,
   outLRange_append h1.trapsp h2.trapsp, outLRange_append h1.codeBase h2.codeBase,
   outLRange_append h1.atomBase h2.atomBase, outLRange_append h1.globals h2.globals,
   fun i w hw => outLRange_append (h1.code i w hw) (h2.code i w hw),
   fun i v hv => outLRange_append (h1.stack i v hv) (h2.stack i v hv),
   fun l a o live placed object => objectOutside_append (h1.heap l a o live placed object)
     (h2.heap l a o live placed object),
   fun id ch a hch hcp => outLRange_append (h1.channels id ch a hch hcp) (h2.channels id ch a hch hcp)⟩

theorem _root_.OCaml.Vm.Primitives.ImageOutside.append {l1 l2 : List WEntry}
    (h1 : ImageOutside l1) (h2 : ImageOutside l2) : ImageOutside (l1 ++ l2) :=
  ⟨outLRange_append h1.text h2.text, outLRange_append h1.rodata h2.rodata⟩

theorem _root_.OCaml.Vm.Primitives.BindingsOutside.append {l1 l2 : List WEntry} {P : Prog} {c : Config}
    (h1 : BindingsOutside l1 P c) (h2 : BindingsOutside l2 P c) : BindingsOutside (l1 ++ l2) P c :=
  ⟨outLRange_append h1.contents h2.contents,
   fun i name hi => outLRange_append (h1.entries i name hi) (h2.entries i name hi)⟩

/-! ## The young-pointer store -/

/-- The young-pointer store misses a range apart from its word. -/
theorem grab_out {domain a x n : Nat}
    (h : x + n ≤ domain + Layout.off_young_ptr ∨ domain + Layout.off_young_ptr + 8 ≤ x) :
    OutLRange (grabReserveLog domain a) x n := ⟨h, trivial⟩

/-- A range apart from the whole `Caml_state` record misses its young-pointer word. -/
theorem young_apart {c : Config} {x n : Nat} {v : BitVec 64}
    (apart : OutWRange [⟨(word c Layout.sym_Caml_state).toNat,
      (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] x n) :
    OutLRange [((word c Layout.sym_Caml_state).toNat + Layout.off_young_ptr, 8, v)] x n := by
  obtain ⟨h, -⟩ := apart
  have : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
  exact ⟨by dsimp only at h ⊢; omega, trivial⟩

/-- **The young-pointer store misses the represented payload.** -/
theorem StackGeometry.young_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high a : Nat} (g : StackGeometry P s c pl cp high) (stack : StackRepr c pl sp high s.stack)
    (space : high - Layout.stackBytes ≤ sp) :
    PayloadOutside (grabReserveLog (word c Layout.sym_Caml_state).toNat a) P s c pl cp sp := by
  have hs := stack.1
  have hl := g.domainLow
  have hd := g.domain.1
  simp only [stackWindow] at hd
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have static : ∀ x, x + 8 ≤ Layout.sym_bss_end →
      OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a) x 8 := fun x hx =>
    grab_out (by simp only [Layout.off_young_ptr]; omega)
  have field : ∀ off, off + 8 ≤ Layout.off_young_ptr ∨ Layout.off_young_ptr + 8 ≤ off →
      OutLRange (grabReserveLog (word c Layout.sym_Caml_state).toNat a)
        ((word c Layout.sym_Caml_state).toNat + off) 8 := fun off h =>
    grab_out (by omega)
  refine ⟨static _ (by decide), field _ (by decide), field _ (by decide), static _ (by decide),
    static _ (by decide), static _ (by decide), ?_, ?_, ?_, ?_⟩
  · intro i w hw
    obtain ⟨hc, -⟩ := g.domainCode
    have bound : i < P.code.size := (Array.getElem?_eq_some_iff.mp hw).1
    have hy : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
    dsimp only at hc
    exact grab_out (by omega)
  · intro i v hv
    have bound : i < s.stack.length := (List.getElem?_eq_some_iff.1 hv).1
    have : Layout.off_young_ptr + 8 ≤ Layout.domainStateBytes := by decide
    exact grab_out (by omega)
  · intro l b o _ placed object
    have apart := g.domainHeap l b o placed object
    exact ⟨young_apart (Gc.outW_sub apart (by omega) (by omega)), young_apart (Gc.outW_sub apart (by omega) (by omega))⟩
  · exact fun id ch b hch hcp => young_apart (g.domainChannels id ch b hch hcp)

/-- The young-pointer store misses the executable image. -/
theorem StackGeometry.young_image {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a : Nat} (g : StackGeometry P s c pl cp high) :
    ImageOutside (grabReserveLog (word c Layout.sym_Caml_state).toNat a) := by
  have hl := g.domainLow
  have t : Image.textBase + Image.textSize ≤ Layout.sym_bss_end := by decide
  have r : Image.rodataBase + Image.rodataSize ≤ Layout.sym_bss_end := by decide
  exact ⟨grab_out (by omega), grab_out (by omega)⟩

/-- The young-pointer store misses the primitive bindings. -/
theorem StackGeometry.young_bindings {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high a : Nat} (g : StackGeometry P s c pl cp high) :
    BindingsOutside (grabReserveLog (word c Layout.sym_Caml_state).toNat a) P c := by
  have hl := g.domainLow
  have t : Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Layout.sym_bss_end := by decide
  exact ⟨grab_out (by omega), fun i name hi => young_apart (g.domainPrims i name hi)⟩

end OCaml.Vm.Sim
