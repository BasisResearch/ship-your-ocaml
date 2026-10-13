import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Primitives.Blocks
import Vsa.Sim.SegToTripleFramed

/-! Register presence across a generated block chain: every register the
chain writes is among the final symbolic registers, which the post pins. -/

namespace OCaml.Vm.Primitives
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

theorem keysG_eraseG_of_ne {n r : Nat} (hne : n ≠ r) :
    ∀ {L : GRegs}, n ∈ keysG L → n ∈ keysG (eraseG r L)
  | [], h => h
  | (m, v) :: L, h => by
    simp only [keysG, List.mem_cons] at h
    simp only [eraseG]
    split
    · next hm =>
      rcases h with rfl | h
      · exact absurd hm hne
      · exact keysG_eraseG_of_ne hne h
    · simp only [keysG, List.mem_cons]
      rcases h with rfl | h
      · exact .inl rfl
      · exact .inr (keysG_eraseG_of_ne hne h)

/-- A key that was present, or that a block body writes, is a key of its
final register list. -/
theorem keysG_runGM {n : Nat} :
    ∀ (is : List MInstr) (L : GRegs) (lds : List (List (BitVec 8))),
      n ∈ keysG L ∨ n ∈ wrRegsM is → n ∈ keysG (runGM is L lds)
  | [], _, _, h => h.elim id (fun h => nomatch h)
  | a :: r, L, lds, h => by
    simp only [runGM]
    apply keysG_runGM r
    have step : ∀ v, n ∈ keysG L ∨ n ∈ a.rd :: wrRegsM r →
        n ∈ keysG ((a.rd, v) :: eraseG a.rd L) ∨ n ∈ wrRegsM r := by
      intro v h
      by_cases e : n = a.rd
      · exact .inl (by simp only [keysG, List.mem_cons]; exact .inl e)
      · rcases h with h | h
        · exact .inl (by simp only [keysG, List.mem_cons]; exact .inr (keysG_eraseG_of_ne e h))
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h e
          · exact .inr h
    cases hk : a.kind <;> simp only [wrRegsM, stepGM, hk] at h ⊢ <;> first | exact h | exact step _ h

/-- A key that was present, or that a block chain writes, is a key of its
final register list. -/
theorem keysG_runChain {n : Nat} :
    ∀ (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))),
      n ∈ keysG L ∨ n ∈ wrChain bs → n ∈ keysG (runChain bs L lds)
  | [], _, _, h => h.elim id (fun h => nomatch h)
  | b :: bs, L, lds, h => by
    simp only [runChain]
    apply keysG_runChain bs
    simp only [wrChain, List.mem_append] at h
    rcases h with h | h | h
    · exact .inl (keysG_runGM b.body L lds (.inl h))
    · exact .inl (keysG_runGM b.body L lds (.inr h))
    · exact .inr h

/-- **A generated block chain keeps register presence**: what it writes is
pinned, the rest is framed, and it does not write `gp` (two `decide`s). -/
theorem BlockPost.kept {bs : List BBlock} {entry : BitVec 64} {L : GRegs}
    {loads : List (List (BitVec 8))} {before after : Config}
    (h : BlockPost bs entry L loads before after) (keys : KeysOK (wrChain bs))
    (no3 : 3 ∉ wrChain bs) : GprsKept before after := by
  have frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ wrChain bs → gprGet after.σ n = gprGet before.σ n :=
    fun n lo hi w => gprGet_of_frame n lo hi (by gpr_cases n => decide)
      (fun m hm => by
        obtain ⟨b1, b2⟩ := keys m hm
        exact gprReg_beq_false m (by omega) n (by omega) b1 lo (fun e => w (e ▸ hm)))
      h.frame
  refine ⟨fun n lo hi p => ?_, frame 3 (by decide) (by decide) no3⟩
  by_cases w : n ∈ wrChain bs
  · have mem := keysG_runChain bs L loads (.inr w)
    rw [show runChain bs L loads = (evalBlocks bs (SegEvalState.init L loads)).regs from
      (evalBlocks_regs bs (SegEvalState.init L loads)).symm] at mem
    obtain ⟨v, hv⟩ := lookup_of_mem _ mem
    rw [gholds_lookup _ h.regs hv]; rfl
  · rw [frame n lo hi w]; exact p

end OCaml.Vm.Primitives
