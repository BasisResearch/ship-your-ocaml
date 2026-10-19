import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Primitives.LibraryEffects
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {live : Nat → Prop}

/-- Readiness across a call known only by its leaf facts, its register
presence (`GprsKept`) and a write log inside windows that miss the runtime's
state: a call whose post is not an `EffectPost`. -/
theorem RuntimeReadyL.of_kept {H capacity oldsp oldra before after log sp ra windows}
    (ready : RuntimeReadyL live H capacity oldsp oldra before) (leaf : LeafInput ra after)
    (stack : gprGet after.σ 2 = some sp) (kept : GprsKept before after)
    (htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes)
    (memory : after.σ.mem = writeLog before.σ.mem log) (inside : LogInW windows log)
    (pins : ∀ pin ∈ VsaIris.Sym.allocText, OutW windows pin.1)
    (domain : OutWRange windows Layout.sym_Caml_state 8)
    (pool : OutWRange windows Layout.sym_pool 8)
    (heap : ∀ a, vsaFoot H a → OutW windows a) : RuntimeReadyL live H capacity sp ra after where
  good := leaf.good
  image := leaf.image
  minstret := leaf.minstret
  raReg := leaf.raReg
  aligned := leaf.aligned
  tick := leaf.tick
  platform := ⟨leaf.good, leaf.tick, fun n lo hi => kept.present n lo hi (ready.platform.gpr n lo hi),
    fun a ha => by rw [memory]; exact writeLog_isSome _ _ _ (ready.platform.live a ha),
    by rw [htif]; exact ready.platform.htifIdle⟩
  readOnly := by
    constructor
    · intro pin hp
      have eq : pin = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
      subst pin
      have same : (vsaModel live).reg after 3 = (vsaModel live).reg before 3 := by
        change vsaReg after 3 = vsaReg before 3
        rw [vsaReg_gpr (by decide), vsaReg_gpr (by decide)]
        have := kept.gp
        unfold gpr at this
        rw [this]
      exact same.trans (ready.readOnly.1 _ hp)
    · intro pin hp
      change (after.σ.mem[pin.1]?).getD 0 = pin.2
      rw [memory, frameOn_writeLog _ _ _ inside pin.1 (pins pin hp)]
      exact ready.readOnly.2 pin hp
  room := by
    apply roomLocal_vsaRoomB H _ _ capacity ?_ ready.room
    intro a ha
    change (before.σ.mem[a]?).getD 0 = (after.σ.mem[a]?).getD 0
    rw [memory, frameOn_writeLog _ _ _ inside a (heap a ha)]
  stack := stack
  domainWord := by
    rw [memory, bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows inside domain)]
    exact ready.domainWord
  poolZero := by
    rw [memory]
    exact lpins8_writeLog ready.poolZero (OCaml.Vm.Sim.outLRange_of_windows inside pool)
end OCaml.Vm.Boot.Startup
