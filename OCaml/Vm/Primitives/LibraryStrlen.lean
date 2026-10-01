import OCaml.Vm.Primitives.LocalRunBridge
import VsaIris.Vsa.SnpStrlen

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The string reader returns to its caller with a byte length, preserves
all owned bytes, and preserves the callee's non-scratch register observations. -/
structure StrlenResult (S : Nat → Prop) (R : Nat → BitVec 64)
    (Mt : Vsa.MemRepr.Mem) (len : Nat) (rv : Nat → BitVec 64)
    (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = R 1
  length : rv 10 = BitVec.ofNat 64 len
  registers : ∀ r ∈ nRegs, r ≠ VsaIris.PC → (r < 10 ∨ 15 < r) → rv r = R r
  memory : ∀ a, S a → mv a = imgM Mt a

/-- Close the landed strlen continuation with its concrete return facts. -/
theorem strlen_symbolic {live Dt DA S Mt a len g}
    (codeLive : ∀ p ∈ snpText, live p.1)
    (string : StrRead Dt DA S Mt a len g) (R : Nat → BitVec 64)
    (argument : R 10 = BitVec.ofNat 64 a) (aligned : (R 1).toNat % 4 = 0) :
    SnpW live Dt DA S (StrlenResult S R Mt len) 0x80042970#64 R Mt := by
  apply strlen_nw codeLive string R argument aligned
  intro next length kept
  apply swp_done
  intro rv mv observed
  exact ⟨observed.pc, (observed.regs 10 (by decide) (by decide)).trans length,
    fun r hr ne outside => (observed.regs r hr ne).trans (kept.get r outside), observed.img⟩

/-- Whole-machine strlen summary, reusing the retargeted library proof. -/
theorem strlen_summary {live Dt DA S Mt a len g} (R : Nat → BitVec 64) (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1)
    (string : StrRead Dt DA S Mt a len g)
    (argument : R 10 = BitVec.ofNat 64 a) (aligned : (R 1).toNat % 4 = 0)
    (separate : LocalSeparation roR (snpText ++ dataOf Dt DA) nRegs S)
    (input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs S R Mt c) :
    FnSummary 0x80042970#64 (fun d => d = c)
      (LocalPost live roR (snpText ++ dataOf Dt DA) nRegs S (StrlenResult S R Mt len) c) :=
  symbolic_summary c separate input (strlen_symbolic codeLive string R argument aligned)

/-- Combining the owned-byte result with the local frame recovers equality
of every total byte, without requiring equality of optional memory maps. -/
theorem strlen_memory {live Dt DA S Mt len R before after}
    (input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs S R Mt before)
    (post : LocalPost live roR (snpText ++ dataOf Dt DA) nRegs S
      (StrlenResult S R Mt len) before after) (a : Nat) :
    (vsaModel live).mem after a = (vsaModel live).mem before a := by
  by_cases owned : S a
  · exact (post.result.memory a owned).trans (input.memory a owned).symm
  · exact post.memory a owned

end OCaml.Vm.Primitives
