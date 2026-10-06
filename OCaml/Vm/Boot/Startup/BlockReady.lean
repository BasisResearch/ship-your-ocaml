import OCaml.Vm.Boot.Startup.RuntimeReady
import OCaml.Vm.Boot.Startup.TableHeap
import OCaml.Vm.Primitives.LocalRunBridge
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- A library call that writes only inside one live block keeps startup readiness. -/
theorem RuntimeReady.of_block_frame {H capacity oldsp oldra sp ra before after text rs dst n}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (frame : LocalFrame startupLive [] text rs (InExt (dst, n)) before after)
    (gpKept : 3 ∉ rs) (leaf : LeafInput ra after) (stack : gprGet after.σ 2 = some sp)
    (member : (dst, n) ∈ H) (lower : heapStart ≤ dst) : RuntimeReady H capacity sp ra after := by
  have low (a : Nat) (below : a < heapStart) : (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 :=
    frame.memory a (fun inside => by unfold InExt at inside; omega)
  refine ⟨leaf, frame.good, ⟨?_, ?_⟩, ?_, stack, ?_, ?_⟩
  · intro pin hp
    have eq : pin = (3, gpV) := List.mem_singleton.mp hp
    subst eq
    exact (frame.registers 3 gpKept).trans (ready.readOnly.1 _ hp)
  · intro pin hp
    change (after.σ.mem[pin.1]?).getD 0 = pin.2
    rw [low _ (allocator_sources pin hp).geometry.high]
    exact ready.readOnly.2 pin hp
  · apply roomLocal_vsaRoomB H _ _ capacity ?_ ready.room
    intro a ha
    exact (frame.memory a (fun inside => by
      unfold InExt at inside
      rcases allocator_payload_outside member lower ha with h | h <;> omega)).symm
  · rw [word_observed (m := before.σ.mem) _ (fun i _ => low _ (by unfold heapStart Layout.sym_Caml_state; omega))]
    exact ready.domainWord
  · exact lpins8_observed ready.poolZero (fun i _ => low _ (by unfold heapStart Layout.sym_pool; omega))
end OCaml.Vm.Boot.Startup
