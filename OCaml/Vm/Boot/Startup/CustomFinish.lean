import OCaml.Vm.Boot.Startup.CustomCaller
import OCaml.Vm.Boot.Startup.NativeReturnPair
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim VsaIris.Inst OCaml.Vm.Primitives

structure CustomReturned (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (before after : Config) where
  atReturn : Config
  nodes : CustomNodes H capacity sp ra s0 head before atReturn
  post : WriteRegistersPost [1, 8, 2] [] atReturn ra
    (vsaReg nodes.bigarray.registration.allocated 10)
    (nativePairRegs sp ra s0 (vsaReg nodes.bigarray.registration.allocated 10)) after
  ready : RuntimeReady (((vsaReg nodes.bigarray.registration.allocated 10).toNat, 16) :: nodes.H3)
    capacity sp ra after

/-- Restore the initializer's actual saved caller after all four registrations. -/
theorem custom_finish (before c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (w : CustomNodes H capacity sp ra s0 head before c)
    (frame : NativeFrame sp 560) (aligned : ra.toNat % 4 = 0) :
    FnSummary NativePairKind.custom.entry (fun d => d = c)
      (fun after => Nonempty (CustomReturned H capacity sp ra s0 head before after)) := by
  have ready := w.bigarray.registration.ready
  have input : NativePairInput .custom sp ra s0 (vsaReg w.bigarray.registration.allocated 10) 0x80024aa8#64 c := {
    toLeafInput := ready.toLeafInput
    frame := frame.resize (by decide) (by decide)
    regs := ⟨ready.stack, w.bigarray.registration.publication.result, trivial⟩
    savedRa := w.saved_word frame (by simp [NativePairKind.raOffset])
    savedS0 := w.saved_word frame (by simp [NativePairKind.s0Offset])
    returnAligned := aligned }
  constructor
  intro current ⟨pc, eq⟩
  subst current
  obtain ⟨after, run, post⟩ := (native_return_pair c .custom sp ra s0 _ _ input).run c ⟨pc, rfl⟩
  have finalReady := ready.effect post (by decide)
    (by simp only [nativePairRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  exact ⟨after, run, ⟨c, w, post, finalReady⟩⟩

/-- Complete custom-operation initialization from its native entry to the
original caller, using four successful allocator summaries and shared restore. -/
theorem custom_init (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra s0 head : BitVec 64) (ready : RuntimeReady H (capacity + 128) sp ra c)
    (frame : NativeFrame sp 560) (saved0 : gprGet c.σ 8 = some s0)
    (headWord : bytesT c.σ.mem Layout.sym_custom_ops_table 8 = head) :
    FnSummary 0x80024a2c#64 (fun d => d = c)
      (fun after => Nonempty (CustomReturned H capacity sp ra s0 head c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨atReturn, run1, ⟨w⟩⟩ := (custom_nodes c H capacity sp ra s0 head ready frame saved0 headWord).run c ⟨pc, rfl⟩
  obtain ⟨after, run2, returned⟩ := (custom_finish c atReturn H capacity sp ra s0 head w frame ready.aligned).run
    atReturn ⟨w.bigarray.registration.publication.pc, rfl⟩
  exact ⟨after, run1.trans run2, returned⟩
end OCaml.Vm.Boot.Startup
