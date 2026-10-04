import OCaml.Vm.Boot.Startup.CustomAllocate
import OCaml.Vm.Boot.Startup.CustomRequest
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem CustomLater.link (kind : CustomLater) : kind.call.link = kind.kind.entry := by cases kind <;> rfl
theorem CustomLater.target (kind : CustomLater) : kind.call.target = 0x8000bb2c#64 := by cases kind <;> rfl

structure CustomNextRegistered (H : List (Nat × Nat)) (capacity : Nat) (kind : CustomLater)
    (sp head : BitVec 64) (before after : Config) where
  request : Config
  setup : WriteRegistersPost [10, 1] [] before kind.call.target 16#64
    ((1, kind.call.link) :: customRequestRegs sp) request
  registration : CustomRegistered H capacity kind.kind sp customTable head request after

/-- Every subsequent custom registration reuses the same request, allocation
and publication summaries, charging one 16-byte node. -/
theorem custom_next (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (kind : CustomLater) (sp ra head : BitVec 64)
    (ready : RuntimeReady H (capacity + 32) sp ra c) (frame : NativeFrame sp 544)
    (table : gprGet c.σ 8 = some customTable)
    (headWord : bytesT c.σ.mem Layout.sym_custom_ops_table 8 = head) :
    FnSummary kind.entry (fun d => d = c)
      (fun after => Nonempty (CustomNextRegistered H capacity kind sp head c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := (custom_request c kind sp ra ready.toLeafInput
    ⟨ready.stack, table, trivial⟩).run c ⟨pc, rfl⟩
  have input := ready.effect setup (by decide)
    (by simp only [customRequestRegs, customParked, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ setup.regs (by rfl))
    (gholds_lookup (n := 1) _ setup.regs (by rfl)) (by cases kind <;> decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have called : RuntimeReady H (capacity + 32) sp kind.kind.entry request := by
    simpa only [kind.link] using input
  obtain ⟨after, run2, ⟨registered⟩⟩ := (custom_allocate_publish request H capacity kind.kind sp customTable head
    called frame (gholds_lookup (n := 8) _ setup.regs (by rfl)) (fun _ => rfl) setup.result
    (by rw [setup.memory]; exact headWord)).run request ⟨by rw [← kind.target]; exact setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, ⟨request, setup, registered⟩⟩
end OCaml.Vm.Boot.Startup
