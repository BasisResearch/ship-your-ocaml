import OCaml.Vm.Primitives.Uncaught.FatalSuspend
import OCaml.Vm.Primitives.Uncaught.FormatSummary

/-!
# `caml_fatal_uncaught_exception`: `msg = caml_format_exception(exn)`

At `caml_format_exception`'s entry (`AtFormat`), its `FormatInput` and
`FormatHeap` come from the fatal path's entry: the exception block and its
name (`ExnAt`) survive memprof's three stores (`exnApart`), and the
allocator's readiness survives them too (`FatalHeap.storesApart`,
`ready_transport_framed`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some NameAt)
open OCaml.Vm.Primitives.Uncaught.FormatException (FormatInput FormatHeap FormatDone format_exception_constant
  ready_transport_framed)

/-- **The uncaught exception at the entry**: a constant exception whose
name is a C string in the arena (the facts `FormatInput` reads). -/
structure ExnAt (m : Mem) (exn np : BitVec 64) (name : List (BitVec 8)) : Prop where
  constant : (m[(exn + 18446744073709551608#64).toNat]?).getD 0 ≠ 0#8
  namePtr : bytesVal .ld (read8 m exn.toNat) = np
  exnLow : Layout.sym_tohost + 16 ≤ exn.toNat
  exnHigh : exn.toNat + 8 ≤ heapEnd
  named : NameAt m np name
  nameLow : Layout.sym_bss_end ≤ np.toNat
  nameHigh : np.toNat + name.length + 8 ≤ heapEnd
  nonempty : 0 < name.length
  fits : name.length ≤ 255

/-- The bytes `ExnAt` reads: the header, field 0, and the name with its terminator. -/
def ExnBytes (exn np : BitVec 64) (len : Nat) (a : Nat) : Prop :=
  (exn.toNat - 8 ≤ a ∧ a < exn.toNat + 8) ∨ (np.toNat ≤ a ∧ a ≤ np.toNat + len)

theorem ExnAt.transport {m m' : Mem} {exn np : BitVec 64} {name : List (BitVec 8)} (h : ExnAt m exn np name)
    (same : ∀ a, ExnBytes exn np name.length a → (m'[a]?).getD 0 = (m[a]?).getD 0) : ExnAt m' exn np name := by
  have lo := h.exnLow
  have hi := h.nameHigh
  have he : heapEnd < 2 ^ 64 := by decide
  have hdr : (exn + 18446744073709551608#64).toNat = exn.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Layout.sym_tohost] at lo; omega
  have name (i : Nat) (hi' : i ≤ name.length) : (np + BitVec.ofNat 64 i).toNat = np.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, h.exnLow, h.exnHigh, ⟨fun i hi' => ?_, h.named.nonzero, ?_, h.named.window⟩, h.nameLow,
    h.nameHigh, h.nonempty, h.fits⟩
  · rw [hdr, same _ (Or.inl ⟨Nat.le_refl _, by omega⟩), ← hdr]; exact h.constant
  · rw [ConsoleWrite.read8_same (m := m) fun i hi' => same _ (Or.inl ⟨by omega, by omega⟩)]
    exact h.namePtr
  · rw [name i (Nat.le_of_lt hi'), same _ (Or.inr ⟨by omega, by omega⟩), ← name i (Nat.le_of_lt hi')]
    exact h.named.bytes i hi'
  · rw [name _ (Nat.le_refl _), same _ (Or.inr ⟨by omega, Nat.le_refl _⟩), ← name _ (Nat.le_refl _)]
    exact h.named.nul

/-- **The allocator at the fatal path's entry**: readiness with room for the
message, stack for the fatal frame, `caml_format_exception`'s frame and the
allocator below it, and memprof's stores apart from the allocator's state. -/
structure FatalHeap (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra : BitVec 64) (len : Nat)
    (p dom start trig : BitVec 64) (c : Config) : Prop where
  ready : RuntimeReadyL imageLive H (capacity + charge) sp ra c
  frame : NativeFrame sp (48 + (432 + allocHeadroom))
  charged : vsaChg (len + 1) charge
  /-- memprof's stores miss the allocator's footprint, its code pins, the
  `Caml_state` word and the pool word -/
  storesApart : ∀ a, (vsaFoot H a ∨ (∃ pin ∈ VsaIris.Sym.allocText, pin.1 = a) ∨
      (Layout.sym_Caml_state ≤ a ∧ a < Layout.sym_Caml_state + 8) ∨ (Layout.sym_pool ≤ a ∧ a < Layout.sym_pool + 8)) →
    OutL (memprofStores p dom start trig) a

theorem FatalHeap.formatFrame {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra : BitVec 64} {len : Nat}
    {p dom start trig : BitVec 64} {c : Config} (h : FatalHeap H capacity charge sp ra len p dom start trig c) :
    NativeFrame (sp + 18446744073709551568#64) (432 + allocHeadroom) := by
  have nested := h.frame.nested (front := 48) (by decide)
  unfold nativeStack at nested
  rwa [show -BitVec.ofNat 64 48 = 18446744073709551568#64 by decide] at nested

/-- **`msg = caml_format_exception(exn)`** from the call, under the entry's
exception and allocator facts. -/
theorem fatal_format {H : List (Nat × Nat)} {capacity charge : Nat} {sp ra exn np s2 s3 p dom start trig : BitVec 64}
    {name : List (BitVec 8)} {c0 f : Config}
    (heap : FatalHeap H capacity charge sp ra name.length p dom start trig c0)
    (exnAt : ExnAt c0.σ.mem exn np name)
    (exnApart : ∀ a, ExnBytes exn np name.length a → OutL (memprofStores p dom start trig) a)
    (atf : AtFormat c0 sp exn s2 s3 p dom start trig f) :
    ∃ res r, Steps f r ∧ FormatDone H capacity 0x8000dfc8#64 (sp + 18446744073709551568#64) 0#64 exn s2
      (regsAt f 20) (regsAt f 21) name res f r := by
  have low (a : Nat) (ha : a < heapEnd) (out : OutL (memprofStores p dom start trig) a) :
      (f.σ.mem[a]?).getD 0 = (c0.σ.mem[a]?).getD 0 := by rw [atf.kept a ha out]
  have ex : ExnAt f.σ.mem exn np name := exnAt.transport fun a ha => low a (by
    have := exnAt.exnHigh; have := exnAt.nameHigh
    rcases ha with ⟨-, h⟩ | ⟨-, h⟩ <;> omega) (exnApart a ha)
  have fr := heap.formatFrame
  have input : FormatInput 0x8000dfc8#64 (sp + 18446744073709551568#64) exn np 0#64 exn s2 (regsAt f 20)
      (regsAt f 21) name f :=
    { leaf := atf.leaf, ready := atf.ready, pc := atf.pc
      frame := fr.resize (by decide) (by decide)
      stack := atf.stack, arg := atf.arg, saved0 := atf.saved0, saved1 := atf.saved1, saved2 := atf.saved2
      saved4 := gpr_some (atf.ready.gprs 20 (by decide) (by decide))
      saved5 := gpr_some (atf.ready.gprs 21 (by decide) (by decide))
      constant := ex.constant, namePtr := ex.namePtr, exnLow := ex.exnLow, exnHigh := ex.exnHigh
      named := ex.named, nameLow := ex.nameLow, nameHigh := ex.nameHigh, nonempty := ex.nonempty, fits := ex.fits }
  have order : heapStart ≤ heapEnd := by decide
  have fh : FormatHeap H capacity charge (sp + 18446744073709551568#64) 0x8000dfc8#64 name.length f :=
    { ready := ready_transport_framed heap.ready atf.leaf atf.ready
        (fun pin hp => low pin.1 (by have := (allocator_sources pin hp).geometry.high; omega)
          (heap.storesApart _ (Or.inr (Or.inl ⟨pin, hp, rfl⟩))))
        (fun i hi => low _ (by unfold Layout.sym_Caml_state heapEnd; omega)
          (heap.storesApart _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
        (fun i hi => low _ (by unfold Layout.sym_pool heapEnd; omega)
          (heap.storesApart _ (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))
        (fun a ha => low a (allocator_foot_below ha) (heap.storesApart _ (Or.inl ha)))
        atf.stack
      frame := fr
      charged := heap.charged }
  exact format_exception_constant input fh

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
