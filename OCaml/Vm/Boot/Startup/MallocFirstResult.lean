import OCaml.Vm.Boot.Startup.MallocBootstrap
namespace OCaml.Vm.Boot.Startup
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap

/-- The first allocation returns the first heap payload and an initialized heap. -/
structure FirstMallocEnd (r s : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  frame : RetFrame rv r s saved
  pointer : rv 10 = BitVec.ofNat 64 (heapStart + 16)
  shape : vsaLayoutP.Shape mv [((rv 10).toNat, 928)]
  room : ∀ k, 2 * k + extendSlack ≤ heapEnd - (heapStart + 944) →
    vsaRoomB mv [((rv 10).toNat, 928)] k

def firstMallocCtx (live : Nat → Prop) (r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (R : Nat → BitVec 64) (m : Mem) : MCtx :=
  ⟨live, mS [] s, FirstMallocEnd r s saved, [], 928#64, r, s, R, m, heapStart⟩

/-- Reuse the library return rule, strengthening its result with the unique
first pointer; the out-of-memory branch contradicts the initial capacity. -/
theorem firstMalloc_ok {live : Nat → Prop} {r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {R : Nat → BitVec 64} {m : Mem}
    (hlive : AllocLive live) (hsv : saved.map Prod.fst = vsaSaved)
    (hsp : SpOKA s) (hral : r.toNat % 4 = 0)
    (entry : EntryRegs R mallocEntryBV r 928#64 s saved) :
    MOK (firstMallocCtx live r s saved R m) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := mChg_own hsp
  ral := hral
  ok := by
    intro R' m' h
    have ptr := MRet.first_pointer h rfl rfl
    obtain ⟨top, brkv, chunks, bins, heap, bound, _⟩ := h.heap
    change top ≤ heapStart + physSize 928 at bound
    have rounding : physSize 928 = 944 := by decide
    rw [rounding] at bound
    refine malloc_ret (F := vsaFoot [((R' 10).toNat, 928)]) hsv h.regs.ra h.regs.sp
      (saved_of_regs hsv entry h.regs)
      (fun a ha => .inr (vsaFoot_cons_sub a ha))
      (fun a ha => h.pres a (vsaFoot_cons_sub a ha)) ?_
    intro rv mv frame a0 image
    have starts : Starts [((R' 10).toNat, 928)] := (show Starts [] from by constructor).cons h.fresh.start
    change rv 10 = R' 10 at a0
    refine ⟨frame, a0.trans ptr, ?_, ?_⟩
    · rw [a0]
      exact ⟨starts, m', top, brkv, chunks, bins, image, heap⟩
    · intro k cap
      rw [a0]
      exact ⟨starts, m', top, brkv, chunks, bins, image, heap, Nat.le_trans cap (Nat.sub_le_sub_left bound heapEnd)⟩
  null := by
    intro R' m' h
    have impossible := h.starved
    exact False.elim ((by unfold Starved; decide : ¬ Starved heapStart 928) impossible)
end OCaml.Vm.Boot.Startup
