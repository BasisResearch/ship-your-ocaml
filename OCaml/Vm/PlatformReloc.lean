import OCaml.Vm.Platform
import OCaml.Vm.Reloc

/-! Relocation interface for the placement-independent platform component.
The collector supplies control/runtime restoration and a frame for immutable
bytes. This does not assert that an arbitrary collector preserves them. -/
namespace OCaml.Vm.Reloc
open Vsa.Machine

/-- Concrete obligations left to the collector or an arm's machine summary.
Only immutable image bytes are framed; the heap may change freely. -/
structure PlatformFrame (runtimeOk : Config → Prop) (c c' : Config) : Prop where
  control : Vsa.Sim.GoodState c'.σ
  text : ∀ i, i < Image.textSize →
    c'.σ.mem[Image.textBase + i]? = c.σ.mem[Image.textBase + i]?
  rodata : ∀ i, i < Image.rodataSize →
    c'.σ.mem[Image.rodataBase + i]? = c.σ.mem[Image.rodataBase + i]?
  runtime : runtimeOk c'

/-- A placement-independent atom for the existing equivariance calculus.
There are no abstract pointers to rename; the machine frame is still required. -/
def platformEqv (runtimeOk : Config → Prop) : Eqv where
  P := fun _ _ c => PlatformOk runtimeOk c
  Img := fun _ _ _ _ c c' => PlatformFrame runtimeOk c c'
  transport := fun _ _ _ _ _ _ h f =>
    ⟨f.control, ⟨fun i hi => (f.text i hi).trans (h.image.text i hi),
      fun i hi => (f.rodata i hi).trans (h.image.rodata i hi)⟩, f.runtime⟩

/-- The collector's platform side of a relocation uses `Eqv.transport`.
Its obligations are independent of the old and new abstract placements. -/
theorem platformOk_reloc {runtimeOk : Config → Prop} {c c' : Config}
    (μ : Nat → Nat) (pl : Place) (h : PlatformOk runtimeOk c)
    (frame : PlatformFrame runtimeOk c c') : PlatformOk runtimeOk c' :=
  (platformEqv runtimeOk).transport μ pl 0 0 c c' h frame

/-- Fixed GPR pins have a register-read frame and no abstract heap pointers. -/
def fixedGprEqv (r : Nat) (v : BitVec 64) : Eqv where
  P := fun _ _ c => gpr c r = some v
  Img := fun _ _ _ _ c c' => gpr c' r = gpr c r
  transport := fun _ _ _ _ _ _ h f => f.trans h

/-- The idle HTIF payload counter: a register read, no heap pointer. -/
def htifIdleEqv : Eqv where
  P := fun _ _ c => c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some 0#4
  Img := fun _ _ _ _ c c' => c'.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes =
    c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes
  transport := fun _ _ _ _ _ _ h f => f.trans h

/-- Product of the fixed loop-register atoms. -/
def loopRegistersEqv : Eqv :=
  Eqv.and (fixedGprEqv Layout.reg_dispatchTable (BitVec.ofNat 64 Layout.jumpTable)) <|
  Eqv.and (fixedGprEqv Layout.reg_opcodeBound (BitVec.ofNat 64 Layout.opcodeBound)) <|
  Eqv.and (fixedGprEqv Layout.reg_pending (BitVec.ofNat 64 Layout.sym_caml_something_to_do)) <|
  Eqv.and (fixedGprEqv Layout.reg_domain (BitVec.ofNat 64 Layout.sym_Caml_state)) htifIdleEqv

/-- Named interface to the product assertion. -/
theorem loopRegisters_iff (pl : Place) (c : Config) :
    LoopRegisters c ↔ loopRegistersEqv.P pl 0 c :=
  ⟨fun h => ⟨h.dispatchTable, h.opcodeBound, h.pending, h.domain, h.htifIdle⟩,
    fun ⟨table, bound, pending, domain, idle⟩ => ⟨table, bound, pending, domain, idle⟩⟩

/-- Relocation of heap pointers does not change these fixed-address registers. -/
theorem loopRegisters_reloc {c c' : Config} (μ : Nat → Nat) (pl : Place)
    (h : LoopRegisters c) (frame : loopRegistersEqv.Img μ pl 0 0 c c') :
    LoopRegisters c' :=
  (loopRegisters_iff _ _).2 <|
    loopRegistersEqv.transport μ pl 0 0 c c' ((loopRegisters_iff _ _).1 h) frame

end OCaml.Vm.Reloc
