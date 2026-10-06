import OCaml.Vm.Sim.StackLog
import OCaml.Vm.Sim.PayloadRestore
import OCaml.Vm.Sim.PayloadWindows

/-!
# Certificates for arm logs that also write VM-owned `Caml_state` fields

Exception, re-entry and C-call setup arms write both the free part of the VM
stack and a few `Caml_state` fields (`trapsp`, `extern_sp`, ...). For any log
whose windows are of those two kinds, `VmLogOk.of_windows` derives every
payload separation fact the arms need from the placement geometry.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- An arm write window: in the free part of the VM stack allocation, or one
VM-owned `Caml_state` field. -/
def VmWriteWindow (c : Config) (sp high : Nat) (w : W) : Prop :=
  (high - Layout.stackBytes ≤ w.lo ∧ w.hi ≤ sp) ∨
    ∃ off ∈ vmDomainOffsets,
      w = ⟨(word c Layout.sym_Caml_state).toNat + off, (word c Layout.sym_Caml_state).toNat + off + 8⟩

/-- Everything such a log leaves untouched. -/
structure VmLogOk (log : List WEntry) (P : Prog) (s : St) (c : Config) (pl : Place)
    (cp : ChanPlace) (sp : Nat) : Prop where
  core : PayloadCoreOutside log P s c pl cp
  stack : ∀ i v, s.stack[i]? = some v → OutLRange log (sp + 8 * i) 8
  heap : ∀ l a o, pl.φ l = some a → s.heap.get? l = some o → ObjectOutside log a o
  image : ImageOutside log
  young : YoungOutside log c
  bindings : BindingsOutside log P c

/-- **One derivation for every VM write log.** -/
theorem VmLogOk.of_windows {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ws : List W} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (stackRepr : StackRepr c pl sp high s.stack) (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (inside : LogInW ws log)
    (vm : ∀ w ∈ ws, VmWriteWindow c sp high w) : VmLogOk log P s c pl cp sp := by
  have hs := stackRepr.1
  have lw : LogWindows log P s c pl cp sp high vmDomainOffsets :=
    ⟨g.toStackGeometry, ⟨ws, inside, fun w hw => by
      rcases vm w hw with ⟨lo, hi⟩ | ⟨off, member, rfl⟩
      · exact .belowStack lo hi
      · exact .field member⟩, by omega, by decide⟩
  refine ⟨lw.core (by decide), fun i v hv => ?_, fun _ _ _ placed got => lw.objectOutside placed got,
    lw.image, lw.young (by decide), lw.bindings⟩
  have := (List.getElem?_eq_some_iff.1 hv).1
  exact lw.stackSlot (by omega) (by omega) (by omega)

end OCaml.Vm.Sim
