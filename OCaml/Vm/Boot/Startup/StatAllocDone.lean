import OCaml.Vm.Boot.Startup.ClearReady
import OCaml.Vm.Primitives.LibraryFrame

/-! The named destructuring of `StatAllocatedL`: one lemma turns a
`caml_stat_alloc_noexc(n)` run into its caller-facing facts (return, result,
fresh aligned block, readiness, saved registers, kept bytes), so call sites
stop unpacking `allocation.result`, `library_pc` and `library_gpr` by hand. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {live : Nat → Prop}

/-- `caml_stat_alloc_noexc(n)` returned the fresh block `p`. -/
structure StatAllocDone (live : Nat → Prop) (H : List (Nat × Nat)) (capacity : Nat) (n sp ra p : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt ra after
  result : gprGet after.σ 10 = some p
  fresh : FreshBlock vsaLayoutP H p.toNat n.toNat
  align : p.toNat % 16 = 0
  ready : RuntimeReadyL live ((p.toNat, n.toNat) :: H) capacity sp ra after
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k
  caller : ∀ x, sp.toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  kept : ∀ x, x < sp.toNat - allocHeadroom → ¬ vsaFoot H x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem StatAllocatedL.done {H capacity n sp ra before after} (w : StatAllocatedL live H capacity n sp ra before after)
    (frame : NativeFrame sp allocHeadroom) :
    StatAllocDone live H capacity n sp ra (vsaReg after 10) before after where
  pc := library_pc w.allocation.good w.allocation.result.frame.pc
  result := library_gpr w.ready.platform (by decide) (by decide) rfl
  fresh := w.allocation.result.fresh
  align := w.allocation.result.align
  ready := w.ready
  saved := fun _ member => w.saved_gpr member
  caller := fun _ above => w.caller_byte frame above
  kept := fun _ low foot => w.kept_byte low foot

/-- `caml_stat_alloc_noexc(n)` from readiness, destructured. -/
theorem stat_alloc_done [LibraryLive live] (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (n sp ra : BitVec 64) (ready : RuntimeReadyL live H (capacity + charge) sp ra c)
    (frame : NativeFrame sp allocHeadroom) (request : gprGet c.σ 10 = some n) (charged : vsaChg n.toNat charge)
    (pc : PCAt (BitVec.ofNat 64 Layout.sym_caml_stat_alloc_noexc) c) :
    ∃ p after, Steps c after ∧ StatAllocDone live H capacity n sp ra p c after := by
  obtain ⟨after, run, ⟨w⟩⟩ := (stat_alloc_ready c H capacity charge n sp ra ready frame request charged).run c ⟨pc, rfl⟩
  exact ⟨_, after, run, w.done frame⟩

end OCaml.Vm.Boot.Startup
