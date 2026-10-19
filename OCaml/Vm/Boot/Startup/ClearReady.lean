import OCaml.Vm.Boot.Startup.RuntimeReady
import OCaml.Vm.Boot.Startup.AllocatorReads
import OCaml.Vm.Boot.Startup.ToCamlMain
import OCaml.Vm.Boot.Startup.TableHeap
import OCaml.Vm.Boot.Startup.StatAllocReady
import OCaml.Vm.Boot.Startup.AllocatorPins
import OCaml.Vm.Primitives.Boundary
import OCaml.Vm.Primitives.LibraryFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {live : Nat → Prop}

/-- A byte below the arena's end outside the allocator's footprint misses a
fresh block. -/
theorem FreshBlock.out_kept {H : List (Nat × Nat)} {p n x : Nat} (fresh : FreshBlock vsaLayoutP H p n)
    (hx : x < heapEnd) (kept : ¬ vsaFoot H x) : x < p ∨ p + n ≤ x := by
  have lo : heapStart ≤ p := fresh.2.1
  by_cases low : x < heapStart
  · omega
  · have owned : ∃ e ∈ H, InExt e x := Classical.byContradiction fun none =>
      kept (Or.inr ⟨by omega, hx, fun e he inside => none ⟨e, he, inside⟩⟩)
    obtain ⟨e, he, inside⟩ := owned
    exact Classical.byContradiction fun apart =>
      fresh.2.2.2 e he x (show p ≤ x ∧ x < p + n by omega) inside

/-- Clearing words inside one live payload preserves runtime readiness. -/
theorem RuntimeReadyL.clear {H capacity oldsp oldra before after writes pc value regs sp ra base size n}
    (ready : RuntimeReadyL live H capacity oldsp oldra before)
    (post : RegistersPost writes (clearWords before.σ.mem base n) before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (member : (base, size) ∈ H) (lower : heapStart ≤ base) (fits : 8 * n ≤ size) :
    RuntimeReadyL live H capacity sp ra after := by
  apply RuntimeReadyL.effect ready post keys cover gpFrame stack link aligned
  · intro a ha
    exact clearWords_below _ _ _ _ (Nat.lt_of_lt_of_le ha lower)
  · intro a ha
    rcases allocator_payload_outside member lower ha with low | high
    · rw [clearWords_below _ _ _ _ low]
    · rw [clearWords_above _ _ _ _ (by omega)]
  · intro a ha
    exact clearWords_present _ _ _ _ ha

/-- The allocation keeps every byte below its scratch window that the
allocator did not own. -/
theorem StatAllocatedL.kept_byte {H capacity n sp ra before after a}
    (w : StatAllocatedL live H capacity n sp ra before after)
    (low : a < sp.toNat - allocHeadroom) (outside : ¬ vsaFoot H a) :
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 := by
  have unowned : ¬ mS H sp a := by
    rintro (scratch | heap)
    · unfold stackWin InExt at scratch; omega
    · exact outside heap
  have unchanged := w.allocation.memory a unowned
  change (after.σ.mem[a]?).getD 0 = (w.atMalloc.σ.mem[a]?).getD 0 at unchanged
  rw [unchanged, w.dispatch.memory]

/-- Every GPR of a ready configuration holds a value. -/
theorem RuntimeReadyL.gpr_some {H capacity sp ra c} (ready : RuntimeReadyL live H capacity sp ra c) (n : Nat)
    (lo : 1 ≤ n) (hi : n ≤ 31) : (gprGet c.σ n).isSome := by
  have h : gprGet c.σ n = some _ := library_gpr ready.platform lo hi rfl
  rw [h]; rfl

/-- A read-only boundary that keeps `sp`, `ra` and `gp` keeps readiness. -/
theorem RuntimeReadyL.boundary {H capacity sp ra before after writes pc regs}
    (ready : RuntimeReadyL live H capacity sp ra before) (post : BoundaryPost writes before ra pc regs after)
    (keys : KeysOK writes) (gpFrame : 3 ∉ writes) (stackFrame : 2 ∉ writes) :
    RuntimeReadyL live H capacity sp ra after := by
  have present (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : (gprGet after.σ n).isSome :=
    post.kept.present n lo hi (ready.gpr_some n lo hi)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (present 10 (by decide) (by decide))
  have rp : RegistersPost writes before.σ.mem before pc v [] after :=
    ⟨⟨post.good, post.image, post.minstret, post.tick, post.pc, hv, post.memory, post.output, post.frame, post.kept⟩,
      trivial⟩
  exact ready.effect_written rp keys (fun n _ lo hi => present n lo hi) gpFrame
    (by
      refine Eq.trans ?_ ready.stack
      apply gprGet_of_frame 2 (by decide) (by decide) (gpr_avoids_noise 2 (by decide) (by decide))
      · intro m hm
        have bounds := keys m hm
        exact gprReg_beq_false m (by omega) 2 (by decide) bounds.1 (by decide) (fun e => stackFrame (e ▸ hm))
      · intro r noise outside
        exact post.frame r (fun m hm => by
          have ne := outside m hm
          exact fun eq => by rw [eq, beq_self_eq_true] at ne; contradiction) noise)
    post.raReg ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
/-- A block of the arena avoids the allocator's text pins. -/
theorem arenaWindow_out_pins {p n : Nat} (lo : heapStart ≤ p) (pin : Nat × BitVec 8)
    (member : pin ∈ VsaIris.Sym.allocText) : OutW [⟨p, p + n⟩] pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  simp only [OutW, and_true]
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, heapStart] at * <;> omega

end OCaml.Vm.Boot.Startup
