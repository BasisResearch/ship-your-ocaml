import OCaml.Vm.Boot.Startup.ExtTableSaved
import OCaml.Vm.Boot.Startup.ExtTablePublish
import OCaml.Vm.Boot.Startup.NativeReturnPair
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

structure ExtTableReturned (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 t n : BitVec 64)
    (before after : Config) where
  allocated : Config
  allocation : ExtTableAllocated H capacity sp ra s0 t n before allocated
  published : Config
  publication : WriteRegistersPost [] (extTablePublishLog t (vsaReg allocation.allocation.allocated 10)) allocated
    0x80003ddc#64 (vsaReg allocation.allocation.allocated 10)
    (extTablePublishRegs t (vsaReg allocation.allocation.allocated 10)) published
  post : WriteRegistersPost [1, 8, 2] [] published ra (vsaReg allocation.allocation.allocated 10)
    (nativePairRegs sp ra s0 (vsaReg allocation.allocation.allocated 10)) after
  ready : RuntimeReady (((vsaReg allocation.allocation.allocated 10).toNat, (extTableRequest n).toNat) :: H)
    capacity sp ra after

/-- Complete caml_ext_table_init for an `n`-slot table at `t`: header writes,
checked allocation, contents publication and caller restoration. -/
theorem ext_table_init (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 t n : BitVec 64) (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp 560) (site : ExtTableSite sp t) (saved0 : gprGet c.σ 8 = some s0)
    (table : gprGet c.σ 10 = some t) (count : gprGet c.σ 11 = some n)
    (charged : vsaChg (extTableRequest n).toNat charge) :
    FnSummary 0x80003db8#64 (fun d => d = c)
      (fun after => Nonempty (ExtTableReturned H capacity sp ra s0 t n c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have short := frame.resize (small := 16) (by decide) (by decide)
  obtain ⟨allocated, run1, ⟨w⟩⟩ := (ext_table_allocate c H capacity charge sp ra s0 t n ready frame site
    saved0 table count charged).run c ⟨pc, rfl⟩
  have allocReady := w.allocation.ready
  have regs : GHolds allocated.σ (extTablePublishRegs t (vsaReg w.allocation.allocated 10)) :=
    ⟨gholds_lookup (n := 8) _ w.allocation.returned.regs (by rfl), w.allocation.returned.result, trivial⟩
  obtain ⟨published, run2, publication⟩ := (ext_table_publish allocated sp _ t _ allocReady.toLeafInput
    short site regs).run allocated ⟨w.allocation.returned.pc, rfl⟩
  have publishedReady := ext_table_publish_ready allocReady short site publication
  have saved (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(0, s0), (8, ra)]) :
      bytesT published.σ.mem (nativeFrameBase sp 16 + off) 8 = value := by
    have small : off ≤ 8 := by
      have choices : (off, value) = (0, s0) ∨ (off, value) = (8, ra) := by simpa using member
      rcases choices with eq | eq <;> cases eq <;> decide
    rw [publication.memory, bytesT_writeLog_out _ (show OutLRange (extTablePublishLog t _) (nativeFrameBase sp 16 + off) 8 from ?_)]
    · exact w.saved_word frame site member
    · have lower := short.lower
      have place := site.frame short
      simp only [extTablePublishLog, OutLRange]
      unfold nativeFrameBase Layout.off_ext_table_contents Layout.ext_table_bytes at *
      refine ⟨?_, trivial⟩
      omega
  have input : NativePairInput .extTable sp ra s0 (vsaReg w.allocation.allocated 10) jal_80003dd4_call.link published := {
    toLeafInput := publishedReady.toLeafInput
    frame := short
    regs := ⟨publishedReady.stack, publication.result, trivial⟩
    savedRa := saved _ ra (by simp [NativePairKind.raOffset])
    savedS0 := saved _ s0 (by simp [NativePairKind.s0Offset])
    returnAligned := ready.aligned }
  obtain ⟨after, run3, post⟩ := (native_return_pair published .extTable sp ra s0 _ _ input).run published ⟨publication.pc, rfl⟩
  have finalReady := publishedReady.effect post (by decide)
    (by simp only [nativePairRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  exact ⟨after, run1.trans (run2.trans run3), ⟨allocated, w, published, publication, post, finalReady⟩⟩
end OCaml.Vm.Boot.Startup
