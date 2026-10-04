import OCaml.Vm.Boot.Startup.RuntimeReady
import OCaml.Vm.Boot.Startup.NativeFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst OCaml.Vm.Primitives

/-- Native stack saves cannot change the allocator arena or runtime globals.
This transports the complete startup contract across generated frame effects. -/
theorem RuntimeReady.stack_log {H capacity oldsp oldra before after writes log pc value regs sp ra frameSp size}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (frame : NativeFrame frameSp size)
    (inside : LogInW [⟨nativeFrameBase frameSp size, frameSp.toNat⟩] log) :
    RuntimeReady H capacity sp ra after := by
  have lower : heapEnd ≤ nativeFrameBase frameSp size := by
    have := frame.lower
    unfold nativeFrameBase
    omega
  have preserved (a : Nat) (ha : a < heapEnd) : (writeLog before.σ.mem log)[a]? = before.σ.mem[a]? := by
    apply frameOn_writeLog _ _ _ inside
    change (a < nativeFrameBase frameSp size ∨ frameSp.toNat ≤ a) ∧ True
    exact ⟨Or.inl (by omega), trivial⟩
  apply ready.effect post keys cover gpFrame stack link aligned
  · intro a ha
    have bound : heapStart ≤ heapEnd := by decide
    exact preserved a (by omega)
  · intro a ha
    rw [preserved a (allocator_foot_below ha)]
  · intro a ha
    exact writeLog_present _ _ _ ha
end OCaml.Vm.Boot.Startup
