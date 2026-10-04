import OCaml.Vm.Boot.Startup.MemsetGeometry
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-- The native loop cursor determines the number of completed word pairs. -/
def zeroPairIndex (base : Nat) (c : Config) : Nat :=
  (((gprGet c.σ 14).getD 0).toNat - base) / 16

structure ZeroPairsAt (base count k : Nat) (ra : BitVec 64) (initial c : Config) : Prop where
  leaf : LeafInput ra c
  bound : k ≤ count
  pc : PCAt (if k < count then 0x80042790#64 else 0x800427a0#64) c
  destination : gprGet c.σ 10 = some (BitVec.ofNat 64 base)
  zero : gprGet c.σ 11 = some 0#64
  cursor : gprGet c.σ 14 = some (pairCursor base k)
  limitReg : gprGet c.σ 13 = some (pairCursor base count)
  memory : c.σ.mem = clearWords initial.σ.mem base (2 * k)
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [14], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = initial.σ.regs.get? r

theorem ZeroPairsAt.index {base count k ra initial c} (region : ZeroPairRegion base count)
    (h : ZeroPairsAt base count k ra initial c) : zeroPairIndex base c = k := by
  simp only [zeroPairIndex, h.cursor, Option.getD_some, region.cursor_nat h.bound]
  omega

theorem zeroPair_branch {base count k} (region : ZeroPairRegion base count) (hk : k < count) :
    guardB bop.BLTU (pairCursor base k + 16#64) (pairCursor base count) = decide (k + 1 < count) := by
  unfold guardB Functions.zopz0zI_u
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.ofNat_lt]
  rw [pairCursor_next, region.cursor_nat (by omega), region.cursor_nat (Nat.le_refl count)]
  omega

/-- One generated iteration advances the exact zero-word memory effect and
retains all nonwritten registers. -/
theorem zero_pair_iteration {base count k ra initial c} (region : ZeroPairRegion base count)
    (h : ZeroPairsAt base count k ra initial c) (hk : k < count) :
    ∃ d, Steps c d ∧ ZeroPairsAt base count (k + 1) ra initial d := by
  have input : MemsetPairInput (BitVec.ofNat 64 base) (pairCursor base k) (pairCursor base count)
      ra (decide (k + 1 < count)) c :=
    ⟨h.leaf, h.destination, h.zero, h.cursor, h.limitReg,
      region.window0 hk, region.window8 hk, region.outside hk, zeroPair_branch region hk⟩
  have pc : PCAt 0x80042790#64 c := by simpa only [if_pos hk] using h.pc
  obtain ⟨d, run, post⟩ := (memset_pair c _ _ _ _ _ input).run c ⟨pc, rfl⟩
  refine ⟨d, run, ⟨?_, by omega, ?_, post.result, ?_, ?_, ?_, ?_, post.output.trans h.output, ?_⟩⟩
  · exact ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
  · change pcOf d = some _
    simpa using post.pc
  · exact gholds_lookup _ post.regs (by rfl)
  · have cursor := gholds_lookup (n := 14) _ post.regs (by rfl)
    rw [pairCursor_next] at cursor
    exact cursor
  · exact gholds_lookup _ post.regs (by rfl)
  · rw [post.memory, h.memory]
    simp only [memsetPairLog, region.cursor_nat h.bound, pairCursor_second,
      region.clear.cursor_nat (k := 2 * k + 1) (by omega)]
    exact (clearWords_pair _ _ _).symm
  · intro r outside noise
    exact (post.frame r outside noise).trans (h.frame r outside noise)

/-- Fold an arbitrary number of native memset word-pairs, without evaluating
the loop in the kernel. -/
theorem zero_pairs {base count ra} (region : ZeroPairRegion base count) (initial : Config) :
    Triple (ZeroPairsAt base count 0 ra initial) (ZeroPairsAt base count count ra initial) := by
  let I := fun c => ZeroPairsAt base count (zeroPairIndex base c) ra initial c
  let B := fun c => zeroPairIndex base c < count
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ count - zeroPairIndex base c = n)
      (fun c => I c ∧ count - zeroPairIndex base c < n) := by
    intro n c ⟨h, hk, hn⟩
    obtain ⟨d, run, post⟩ := zero_pair_iteration region h hk
    have index := post.index region
    refine ⟨d, run, ?_, ?_⟩
    · change ZeroPairsAt base count (zeroPairIndex base d) ra initial d
      rw [index]
      exact post
    · rw [index]
      dsimp [B] at hk
      omega
  apply (loopFromBody (fun c => count - zeroPairIndex base c) body).conseq
  · intro c h
    change ZeroPairsAt base count (zeroPairIndex base c) ra initial c
    rw [h.index region]
    exact h
  · intro c ⟨h, stop⟩
    have bound := h.bound
    have eq : zeroPairIndex base c = count := by dsimp [B] at stop; omega
    simpa only [I, eq] using h
end OCaml.Vm.Boot.Startup
