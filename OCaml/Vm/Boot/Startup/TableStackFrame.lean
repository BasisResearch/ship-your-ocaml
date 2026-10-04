import OCaml.Vm.Boot.Startup.TableFinalAllocate
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

/-- The table function's saved caller frame lies at or above its current sp. -/
structure TableStackFrame (before after : Config) : Prop where
  byte : ∀ a : Nat, (firstMallocStack - 32#64).toNat ≤ a →
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0

theorem TableStackFrame.trans {before middle after : Config}
    (front : TableStackFrame before middle) (back : TableStackFrame middle after) : TableStackFrame before after :=
  ⟨fun a ha => (back.byte a ha).trans (front.byte a ha)⟩

theorem TableStackFrame.of_memory {before after : Config} (same : after.σ.mem = before.σ.mem) :
    TableStackFrame before after := ⟨fun _ _ => by rw [same]⟩

theorem TableStackFrame.word {before after : Config} (h : TableStackFrame before after)
    (a : Nat) (high : (firstMallocStack - 32#64).toNat ≤ a) : bytesT after.σ.mem a 8 = bytesT before.σ.mem a 8 :=
  word_observed a (fun i _ => h.byte _ (by omega))

/-- Allocator scratch is below sp, so it cannot touch the source's saved frame. -/
theorem allocator_table_stack_frame {H Q before after}
    (post : LocalPost startupLive VsaIris.MallocFast.roR VsaIris.Sym.allocText VsaIris.Sym.aRegs
      (mS H (firstMallocStack - 32#64)) Q before after) : TableStackFrame before after := by
  constructor
  intro a high
  apply post.memory a
  have stackHigh : heapEnd ≤ (firstMallocStack - 32#64).toNat := by decide
  change ¬ (stackWin (firstMallocStack - 32#64) allocHeadroom a ∨ vsaFoot H a)
  intro owned
  rcases owned with stack | heap
  · have enough : allocHeadroom ≤ (firstMallocStack - 32#64).toNat := by decide
    unfold stackWin InExt at stack
    omega
  · have := allocator_foot_below heap
    omega

/-- Publication modifies only its fixed domain field, below the saved stack. -/
theorem table_publish_stack_frame {slot p before after}
    (post : WriteRegistersPost [15, 10] (tablePublishLog slot p) before slot.exit p (tablePublishRegs p) after) :
    TableStackFrame before after := by
  constructor
  intro a high
  have bound : slot.address.toNat + 8 ≤ (firstMallocStack - 32#64).toNat := by cases slot <;> decide
  rw [post.memory, writeLog_out _ _ _ (show OutL (tablePublishLog slot p) a from ⟨Or.inr (by change slot.address.toNat + 8 ≤ a; omega), trivial⟩)]

/-- Table zeroing is confined to its fresh payload below the saved stack. -/
theorem table_zero_stack_frame {base before after writes pc value regs}
    (region : Memset56Region base)
    (post : RegistersPost writes (memset56Memory before.σ.mem base) before pc value regs after) :
    TableStackFrame before after := by
  constructor
  intro a high
  have bound : heapEnd ≤ (firstMallocStack - 32#64).toNat := by decide
  have upper := region.upper
  rw [post.memory, memset56Memory_out region _ a (Or.inr (by omega))]

theorem TableNextAllocated.stack_frame {H capacity last before after}
    (w : TableNextAllocated H capacity last before after) : TableStackFrame before after :=
  (TableStackFrame.of_memory w.setup.memory).trans
    ((TableStackFrame.of_memory w.dispatch.memory).trans (allocator_table_stack_frame w.allocation))

theorem TableNextInitialized.stack_frame {H capacity before after}
    (w : TableNextInitialized H capacity before after) : TableStackFrame before after :=
  w.allocation.stack_frame.trans ((table_publish_stack_frame w.publication).trans
    (table_zero_stack_frame w.allocation.region w.zeroing))

theorem TableFinalAllocated.stack_frame {H capacity before after}
    (w : TableFinalAllocated H capacity before after) : TableStackFrame before after :=
  w.initialized.stack_frame.trans w.allocation.stack_frame
end OCaml.Vm.Boot.Startup
