import OCaml.Vm.Boot.Startup.TableStackFrame
import OCaml.Vm.Boot.WhileMinEnvironment
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

/-- Only the mutable environ global and the pinned embedded header/entry bytes
are needed to identify the startup parameter value. -/
def EnvironmentBytes (a : Nat) : Prop :=
  (Layout.sym_environ ≤ a ∧ a < Layout.sym_environ + 8) ∨
    (Layout.sym_embedded_env ≤ a ∧ a < WhileMinImage.envValue + 1)

structure EnvironmentFrame (before after : Config) : Prop where
  byte : ∀ a, EnvironmentBytes a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0

theorem EnvironmentFrame.trans {before middle after} (h : EnvironmentFrame before middle)
    (g : EnvironmentFrame middle after) : EnvironmentFrame before after :=
  ⟨fun a ha => (g.byte a ha).trans (h.byte a ha)⟩

theorem EnvironmentFrame.of_memory {before after} (memory : after.σ.mem = before.σ.mem) :
    EnvironmentFrame before after := ⟨fun _ _ => by rw [memory]⟩

theorem EnvironmentFrame.word {before after} (h : EnvironmentFrame before after)
    (a : Nat) (inside : ∀ i, i < 8 → EnvironmentBytes (a + i)) :
    bytesT after.σ.mem a 8 = bytesT before.σ.mem a 8 :=
  word_observed a (fun i hi => h.byte _ (inside i hi))

/-- Native stack and heap/global write windows frame the observed environment
bytes whenever their ordinary window-separation certificate holds. -/
theorem EnvironmentFrame.of_log {before after log windows}
    (memory : after.σ.mem = writeLog before.σ.mem log) (inside : LogInW windows log)
    (outside : ∀ a, EnvironmentBytes a → OutW windows a) : EnvironmentFrame before after := by
  constructor
  intro a ha
  rw [memory, frameOn_writeLog _ _ _ inside a (outside a ha)]

/-- All native saves made before the parser are in the top kilobyte. -/
theorem EnvironmentFrame.stack {before after log}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (inside : LogInW [⟨Layout.sym_stack_top - 1024, Layout.sym_stack_top⟩] log) :
    EnvironmentFrame before after := by
  apply EnvironmentFrame.of_log memory inside
  intro a ha
  have bound : WhileMinImage.envValue + 1 ≤ Layout.sym_stack_top - 1024 ∧
      Layout.sym_environ + 8 ≤ Layout.sym_stack_top - 1024 := by decide
  exact ⟨Or.inl (by unfold EnvironmentBytes at ha; dsimp only; omega), trivial⟩

/-- The allocator's ownership excludes both the environ global and .embed;
its scratch frame is far above these bytes during domain startup. -/
theorem allocator_environment_outside {H} {sp : BitVec 64} {a} (stack : Layout.sym_stack_top - 1024 ≤ sp.toNat)
    (address : EnvironmentBytes a) : ¬ mS H sp a := by
  change ¬ (stackWin sp allocHeadroom a ∨ vsaFoot H a)
  simp only [stackWin, InExt, vsaFoot, allocGlobal, InRange]
  unfold EnvironmentBytes Layout.sym_environ Layout.sym_embedded_env WhileMinImage.envValue at address
  unfold Layout.sym_stack_top at stack
  unfold heapStart heapEnd allocHeadroom
  omega

theorem EnvironmentFrame.allocator {H Q before after sp}
    (stack : Layout.sym_stack_top - 1024 ≤ sp.toNat)
    (post : LocalPost startupLive VsaIris.MallocFast.roR VsaIris.Sym.allocText VsaIris.Sym.aRegs
      (mS H sp) Q before after) : EnvironmentFrame before after :=
  ⟨fun a ha => post.memory a (allocator_environment_outside stack ha)⟩

theorem EnvironmentFrame.zero {base before after writes pc value regs}
    (region : Memset56Region base)
    (post : RegistersPost writes (memset56Memory before.σ.mem base) before pc value regs after) :
    EnvironmentFrame before after := by
  constructor
  intro a ha
  rw [post.memory, memset56Memory_out region _ a ?_]
  have lower := region.lower
  have upper := region.upper
  unfold EnvironmentBytes Layout.sym_environ Layout.sym_embedded_env WhileMinImage.envValue at ha
  simp only [heapStart, heapEnd] at lower upper
  omega
end OCaml.Vm.Boot.Startup
