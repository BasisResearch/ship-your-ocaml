import OCaml.Vm.Boot.Startup.EnvironmentHistoryFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

/-- Domain initialization may write its published pointer, allocator ownership,
and native stack. Every other low global and byte above the heap is retained. -/
def StartupDataBytes (a : Nat) : Prop :=
  (a < heapStart ∧ ¬ allocGlobal a ∧ (a < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ a)) ∨
    (heapEnd ≤ a ∧ a < Layout.sym_stack_top - 1024)

structure StartupDataFrame (before after : Config) : Prop where
  byte : ∀ a, StartupDataBytes a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0

theorem StartupDataFrame.trans {before middle after} (h : StartupDataFrame before middle)
    (g : StartupDataFrame middle after) : StartupDataFrame before after :=
  ⟨fun a ha => (g.byte a ha).trans (h.byte a ha)⟩

theorem StartupDataFrame.of_memory {before after} (memory : after.σ.mem = before.σ.mem) :
    StartupDataFrame before after := ⟨fun _ _ => by rw [memory]⟩

theorem StartupDataFrame.of_log {before after log windows}
    (memory : after.σ.mem = writeLog before.σ.mem log) (inside : LogInW windows log)
    (outside : ∀ a, StartupDataBytes a → OutW windows a) : StartupDataFrame before after := by
  constructor
  intro a ha
  rw [memory, frameOn_writeLog _ _ _ inside a (outside a ha)]

theorem startupData_stack_outside {a} (ha : StartupDataBytes a) : a < Layout.sym_stack_top - 1024 := by
  have bound : heapStart ≤ Layout.sym_stack_top - 1024 := by decide
  unfold StartupDataBytes at ha
  omega

theorem StartupDataFrame.stack {before after log}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (inside : LogInW [⟨Layout.sym_stack_top - 1024, Layout.sym_stack_top⟩] log) : StartupDataFrame before after :=
  .of_log memory inside (fun a ha => ⟨Or.inl (startupData_stack_outside ha), trivial⟩)

theorem startupData_heap_outside {a base size} (ha : StartupDataBytes a)
    (lower : heapStart ≤ base) (upper : base + size ≤ heapEnd) : a < base ∨ base + size ≤ a := by
  unfold StartupDataBytes at ha
  omega

theorem startupData_allocator_outside {H} {sp : BitVec 64} {a}
    (stack : Layout.sym_stack_top - 512 ≤ sp.toNat) (ha : StartupDataBytes a) : ¬ mS H sp a := by
  have high := startupData_stack_outside ha
  change ¬ (stackWin sp allocHeadroom a ∨ vsaFoot H a)
  intro owned
  rcases owned with scratch | heap
  · unfold stackWin InExt allocHeadroom at scratch
    omega
  · unfold vsaFoot at heap
    rcases ha with ⟨lower, outside, _⟩ | ⟨lower, _⟩
    · rcases heap with global | allocated
      · exact outside global
      · omega
    · rcases heap with global | allocated
      · have below : a < heapEnd := allocator_foot_below (Or.inl global : vsaFoot H a)
        omega
      · omega

theorem StartupDataFrame.allocator {H Q before after sp}
    (stack : Layout.sym_stack_top - 512 ≤ sp.toNat)
    (post : LocalPost startupLive VsaIris.MallocFast.roR VsaIris.Sym.allocText VsaIris.Sym.aRegs
      (mS H sp) Q before after) : StartupDataFrame before after :=
  ⟨fun a ha => post.memory a (startupData_allocator_outside stack ha)⟩

theorem StartupDataFrame.zero {base before after writes pc value regs}
    (region : Memset56Region base)
    (post : RegistersPost writes (memset56Memory before.σ.mem base) before pc value regs after) :
    StartupDataFrame before after := by
  constructor
  intro a ha
  rw [post.memory, memset56Memory_out region _ a (startupData_heap_outside ha region.lower region.upper)]

theorem StartupDataFrame.environment {before after} (h : StartupDataFrame before after) :
    EnvironmentFrame before after := by
  constructor
  intro a ha
  apply h.byte a
  unfold EnvironmentBytes at ha
  rcases ha with global | embedded
  · apply Or.inl
    simp only [allocGlobal, InRange]
    unfold Layout.sym_environ at global
    unfold heapStart Layout.sym_Caml_state
    exact ⟨by omega, by omega, Or.inl (by omega)⟩
  · apply Or.inr
    unfold Layout.sym_embedded_env WhileMinImage.envValue at embedded
    unfold heapEnd Layout.sym_stack_top
    exact ⟨by omega, by omega⟩
end OCaml.Vm.Boot.Startup
