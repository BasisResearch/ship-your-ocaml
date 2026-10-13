import OCaml.Vm.Boot.Startup.PageTableSteps
import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Boot.Startup.MemsetWords
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.ReadyPerm
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `caml_page_table_initialize(0x2f8000)` from caml_init_gc: 2048 entries,
shift 53, mask 2047, no occupancy, and a fresh cleared 16 KB table. -/

/-- The `caml_page_table` record. -/
def pageTableWindows : List W := [⟨pageTable, pageTable + 0x28⟩]

theorem pageTableWindows_out_pins (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) :
    OutW pageTableWindows pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  simp only [OutW, pageTableWindows, and_true]
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, pageTable,
    Layout.sym_caml_page_table] at * <;> omega

theorem pageTableWindows_out_foot {H : List (Nat × Nat)} {a : Nat} (foot : vsaFoot H a) :
    OutW pageTableWindows a := by
  simp only [OutW, pageTableWindows, and_true, pageTable, Layout.sym_caml_page_table]
  rcases foot with global | ⟨lo, _, _⟩
  · unfold allocGlobal InRange at global; omega
  · unfold heapStart at lo; omega

theorem RuntimeReadyL.pageTable_log {live : Nat → Prop} {H capacity oldsp oldra before after writes log pc value regs sp ra}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (inside : LogInW pageTableWindows log) : RuntimeReadyL live H capacity sp ra after :=
  ready.window_log post keys cover gpFrame stack link aligned inside pageTableWindows_out_pins
    ⟨Or.inl (by decide), trivial⟩ ⟨Or.inl (by decide), trivial⟩ (fun _ foot => pageTableWindows_out_foot foot)

/-- caml_init_gc calls `caml_page_table_initialize(0x2f8000)`. -/
structure PageTableCall (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x8000acdc#64 c
  regs : GHolds c.σ [(2, sp), (1, ra), (10, 0x2f8000#64)]
  ready : RuntimeReady H (capacity + charge) sp ra c
  frame : NativeFrame sp (32 + allocHeadroom)
  charged : vsaChg 16384 charge

theorem page_table_geometry (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra : BitVec 64)
    (A : PageTableCall H capacity charge sp ra c) :
    ∃ d, Steps c d ∧ PCAt 0x8000ad40#64 d ∧ GHolds d.σ [(12, 2048#64), (2, nativeStack sp 32)] ∧
      RuntimeReady H (capacity + charge) (nativeStack sp 32) ra d := by
  have frame32 : NativeFrame sp 32 := A.frame.resize (by decide) (by decide)
  have regs := A.regs
  have frameA : NativeFrame (nativeStack sp 32) allocHeadroom := A.frame.nested (front := 32) (by decide)
  have frameIn : NativeFrame (nativeStack sp 32) 32 := frameA.resize (by decide) (by decide)
  obtain ⟨d1, run1, p1⟩ := (page_table_save c sp ra A.ready.toLeafInput frame32 0x2f8000#64 1520#64
    ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 1) _ regs rfl, gholds_lookup (n := 10) _ regs rfl,
      trivial⟩ page_table_pages).run c ⟨A.pc, rfl⟩
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) A.ready.aligned frame32
    (frame32.word_log_inside fun off value member => by simp at member; omega)
  obtain ⟨d2, run2, p2⟩ := (page_table_top d1 ra 1520#64 ready1.toLeafInput
    ⟨gholds_lookup (n := 12) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have ready2 := ready1.pageTable_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready1.stack)
    ((p2.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready1.raReg)
    A.ready.aligned (by simp only [LogInW, InsideW, pageTableWindows]; decide)
  obtain ⟨d3, run3, p3⟩ := (page_table_shift d2 ra 1520#64 ready2.toLeafInput
    ⟨(p2.toEffectPost.gpr_frame (by decide) 15 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 15) _ p1.regs rfl), gholds_lookup (n := 12) _ p2.regs rfl,
      gholds_lookup (n := 10) _ p2.regs rfl, trivial⟩ (by decide)).run d2 ⟨p2.pc, rfl⟩
  have ready3 := ready2.pageTable_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready2.stack)
    ((p3.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready2.raReg)
    A.ready.aligned (by simp only [LogInW, InsideW, pageTableWindows]; decide)
  obtain ⟨d4, run4, D⟩ := page_table_doubling_loop frameIn (start := d3) {
    pc := p3.pc
    regs := ⟨gholds_lookup (n := 12) _ p3.regs rfl, gholds_lookup (n := 15) _ p3.regs rfl,
      gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩
    shift := fun h => absurd h (by decide)
    ready := ready3
    bound := by decide
    mem := rfl }
  have pc4 : PCAt 0x8000ad1c#64 d4 := by have := D.pc; simp only [Nat.lt_irrefl, ite_false] at this; exact this
  obtain ⟨d5, run5, p5⟩ := (page_table_fields d4 ra D.ready.toLeafInput
    ⟨gholds_lookup (n := 12) _ D.regs rfl, D.shift (by decide), gholds_lookup (n := 10) _ D.regs rfl, trivial⟩).run d4
    ⟨pc4, rfl⟩
  have ready5 := D.ready.pageTable_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans D.ready.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans D.ready.raReg)
    A.ready.aligned (by simp only [pageTableFieldsLog, LogInW, InsideW, pageTableWindows]; decide)
  exact ⟨d5, run1.trans (run2.trans (run3.trans (run4.trans run5))), p5.pc,
    ⟨gholds_lookup (n := 12) _ p5.regs rfl, ready5.stack, trivial⟩, ready5⟩
end OCaml.Vm.Boot.Startup
