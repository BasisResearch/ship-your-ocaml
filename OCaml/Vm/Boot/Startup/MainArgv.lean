import OCaml.Vm.Boot.Startup.SharedTableReset
import OCaml.Vm.Boot.Startup.AllocatorRun
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris.Inst

/-! caml_main keeps `argv` in s1 (x9) from its prologue until it builds
`exe_name`. Every caml_main-level callee either never writes s1 or restores
it; these lemmas carry `gprGet · 9` across each summary shape. -/

theorem RegistersPost.keep9 {writes mem before pc value regs after v}
    (post : RegistersPost writes mem before pc value regs after) (keys : KeysOK writes)
    (unwritten : 9 ∉ writes) (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v :=
  (post.toEffectPost.gpr_frame keys 9 (by decide) (by decide) unwritten).trans h

theorem BoundaryPost.keep9 {writes before ra pc regs after v}
    (post : BoundaryPost writes before ra pc regs after) (keys : KeysOK writes)
    (unwritten : 9 ∉ writes) (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v := by
  refine Eq.trans ?_ h
  apply gprGet_of_frame 9 (by decide) (by decide) (gpr_avoids_noise 9 (by decide) (by decide))
  · intro m hm
    have bounds := keys m hm
    exact gprReg_beq_false m (by omega) 9 (by decide) bounds.1 (by decide)
      (fun e => unwritten (e ▸ hm))
  · intro r noise outside
    exact post.frame r (fun m hm => by
      have ne := outside m hm
      exact fun eq => by rw [eq, beq_self_eq_true] at ne; contradiction) noise

end OCaml.Vm.Primitives

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

theorem vsaReg_of_gprGet {c : Config} {n : Nat} {v : BitVec 64} (pc : n ≠ VsaIris.PC)
    (h : gprGet c.σ n = some v) : vsaReg c n = v := by
  rw [vsaReg_gpr pc, h]
  rfl

/-- The landed allocator contracts restore every library-saved register. -/
theorem allocator_keep9 {before after : Config} {r s v : BitVec 64}
    (post : VsaOk startupLive after)
    (frame : RetFrame ((vsaModel startupLive).reg after) r s (firstMallocSaved (vsaReg before)))
    (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v := by
  have saved := frame.saved (9, vsaReg before 9) (by
    change (9, vsaReg before 9) ∈ vsaSaved.map (fun k => (k, vsaReg before k))
    exact List.mem_map.mpr ⟨9, by decide, rfl⟩)
  rw [vsaReg_of_gprGet (by decide) h] at saved
  exact library_gpr post (by decide) (by decide) saved

theorem StatCheckedReturned.keep9 {H capacity sp ra s0 n before after v}
    (w : StatCheckedReturned H capacity sp ra s0 n before after)
    (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v := by
  have a := w.allocation.setup.keep9 (by decide) (by decide) h
  have b := w.allocation.call.keep9 (by decide) (by decide) a
  have c := allocator_keep9 w.allocation.allocation.good w.allocation.allocation.result.frame b
  exact w.returned.keep9 (by decide) (by decide) c

theorem ExtTableReturned.keep9 {H capacity sp ra s0 t n before after v}
    (w : ExtTableReturned H capacity sp ra s0 t n before after)
    (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v := by
  have a := w.allocation.setup.keep9 (by decide) (by decide) h
  have b := w.allocation.call.keep9 (by decide) (by decide) a
  have c := w.allocation.allocation.keep9 b
  have d := w.publication.keep9 (by decide) (by decide) c
  exact w.post.keep9 (by decide) (by decide) d

theorem CustomRegistered.keep9 {H capacity kind sp s0 head before after v}
    (w : CustomRegistered H capacity kind sp s0 head before after)
    (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v :=
  w.publication.keep9 (by decide) (by decide) (w.allocation.keep9 h)

theorem CustomNextRegistered.keep9 {H capacity kind sp head before after v}
    (w : CustomNextRegistered H capacity kind sp head before after)
    (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v :=
  w.registration.keep9 (w.setup.keep9 (by decide) (by decide) h)

theorem CustomReturned.keep9 {H capacity sp ra s0 head before after v}
    (w : CustomReturned H capacity sp ra s0 head before after)
    (h : gprGet before.σ 9 = some v) : gprGet after.σ 9 = some v := by
  have a := w.nodes.int32.setup.keep9 (by decide) (by decide) h
  have b := w.nodes.int32.call.keep9 (by decide) (by decide) a
  have c := w.nodes.int32.registration.keep9 b
  have d := w.nodes.int64.keep9 (w.nodes.nativeint.keep9 c)
  exact w.post.keep9 (by decide) (by decide) (w.nodes.bigarray.keep9 d)
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

theorem DomainHistory.argv {initial after} (w : DomainHistory initial after) :
    gprGet after.σ 9 = some (resetArgv initial) := by
  have tables := w.witness.tables.third.first.published.allocation.before.request.tables
  have main := gholds_lookup (n := 9) _ tables.allocation.before.alloc.domain.post.regs (by rfl)
  have alloc := tables.allocation.before.alloc.post.keep9 (by decide) (by decide) main
  have malloc := tables.allocation.before.post.keep9 (by decide) (by decide) alloc
  have first := allocator_keep9 tables.allocation.post.good tables.allocation.post.result.frame malloc
  have atTables := tables.post.keep9 (by decide) (by decide) first
  have returned : gprGet w.returned.σ 9 = some ((gprGet w.atTables.σ 9).getD 0) :=
    gholds_lookup (n := 9) _ w.witness.tables.post.regs (by rfl)
  rw [atTables] at returned
  exact w.witness.post.keep9 (by decide) (by decide) (w.witness.fields.keep9 (by decide) (by decide) returned)

theorem ResetParameterReturned.argv {initial after} (w : ResetParameterReturned initial after) :
    gprGet after.σ 9 = some (resetArgv initial) := by
  have entry := w.before.post.keep9 (by decide) (by decide) w.before.domain.argv
  have pinned : gprGet after.σ 9 = some (vsaReg w.entry 9) :=
    gholds_lookup (n := 9) _ w.post.regs (by rfl)
  rw [pinned, vsaReg_of_gprGet (by decide) entry]

theorem ResetCustomEntry.argv {initial entry} (w : ResetCustomEntry initial entry) :
    gprGet entry.σ 9 = some (resetArgv initial) := by
  have called := w.auxiliary.call.keep9 (by decide) (by decide) w.auxiliary.parameter.argv
  have aux := w.auxiliary.post.keep9 (by decide) (by decide) called
  exact w.call.keep9 (by decide) (by decide) (w.locale.keep9 (by decide) (by decide) aux)

theorem ResetSharedTableReturned.argv {initial after} (w : ResetSharedTableReturned initial after) :
    gprGet after.σ 9 = some (resetArgv initial) := by
  have custom := w.custom.returned.keep9 w.custom.source.source.argv
  exact w.returned.keep9 (w.call.keep9 (by decide) (by decide) custom)
end OCaml.Vm.Boot.WhileMinElfParse
