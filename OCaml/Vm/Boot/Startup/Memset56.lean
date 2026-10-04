import OCaml.Vm.Boot.Startup.MemsetLoop
import OCaml.Vm.Boot.Startup.MemsetTail
import OCaml.Vm.Boot.Startup.MemsetBytes
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives

/-- The allocated object contains the complete 56-byte memset extent. -/
structure Memset56Region (base : Nat) : Prop where
  lower : heapStart ≤ base
  upper : base + 56 ≤ heapEnd
  aligned : base % 16 = 0

theorem Memset56Region.pairs {base} (r : Memset56Region base) : ZeroPairRegion base 3 :=
  ⟨r.lower, by have := r.upper; omega, r.aligned⟩

theorem Memset56Region.tail_nat {base} (r : Memset56Region base) (i : Nat) (hi : i < 8) :
    (pairCursor base 3 + BitVec.ofNat 64 i).toNat = base + 48 + i := by
  simp only [pairCursor, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := r.upper
  unfold heapEnd at this
  omega

theorem Memset56Region.tail_windows {base} (r : Memset56Region base) (i : Nat) (hi : i < 8) :
    WriteWindow (pairCursor base 3 + BitVec.ofNat 64 i) 1 := by
  constructor
  · rw [r.tail_nat i hi]; have := r.lower; unfold heapStart at this; omega
  · rw [r.tail_nat i hi]; have := r.upper; unfold heapEnd at this; omega
  · rw [r.tail_nat i hi]; have := r.lower; unfold heapStart Layout.sym_tohost at *; omega
  · exact Nat.mod_one _

theorem Memset56Region.tail_outside {base} (r : Memset56Region base) :
    ImageOutside (memsetBytesLog (pairCursor base 3)) := by
  have lower := r.lower
  have text : Image.textBase + Image.textSize ≤ heapStart := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ heapStart := by decide
  have hn := r.pairs.cursor_nat (Nat.le_refl 3)
  constructor <;> simp only [memsetBytesLog, OutLRange, hn]
  all_goals simp only [r.tail_nat 7 (by decide), r.tail_nat 6 (by decide),
    r.tail_nat 5 (by decide), r.tail_nat 4 (by decide), r.tail_nat 3 (by decide),
    r.tail_nat 2 (by decide), r.tail_nat 1 (by decide)]
  all_goals repeat' apply And.intro
  all_goals first | trivial | exact Or.inl (by omega)

def memset56Memory (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) :=
  writeLog (clearWords m base 6) (memsetBytesLog (pairCursor base 3))

/-- Complete native aligned 56-byte zeroing, assembled from generated prefix,
a parameterized word loop, computed tail dispatch, and byte stores. -/
theorem memset56 (c : Config) (base : Nat) (ra : BitVec 64)
    (region : Memset56Region base) (h : Memset56Input (BitVec.ofNat 64 base) ra c) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (EffectPost [6, 14, 15, 13, 12, 5] (memset56Memory c.σ.mem base) c ra (BitVec.ofNat 64 base)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, front, frontPost⟩ := (memset56_prefix c _ ra h).run c ⟨pc, rfl⟩
  have entry : ZeroPairsAt base 3 0 ra a a := {
    leaf := frontPost.toLeafInput
    bound := by decide
    pc := frontPost.pc
    destination := gholds_lookup _ frontPost.regs (by rfl)
    zero := gholds_lookup _ frontPost.regs (by rfl)
    cursor := gholds_lookup _ frontPost.regs (by rfl)
    limitReg := by
      have v := gholds_lookup (n := 13) _ frontPost.regs (by rfl)
      have addr : 48#64 + BitVec.ofNat 64 base = pairCursor base 3 := by
        simp only [pairCursor, ← BitVec.ofNat_add]
        congr 1 <;> omega
      rw [addr] at v
      exact v
    memory := rfl
    output := rfl
    frame := fun _ _ _ => rfl }
  obtain ⟨b, loop, pairs⟩ := zero_pairs region.pairs a a entry
  have size : gprGet b.σ 12 = some 8#64 :=
    (pairs.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ frontPost.regs (by rfl))
  have mask : gprGet b.σ 6 = some 15#64 :=
    (pairs.frame .x6 (by decide) (by decide)).trans (gholds_lookup (n := 6) _ frontPost.regs (by rfl))
  obtain ⟨d, dispatch, tail⟩ := (memset_tail_dispatch b ra pairs.leaf size mask).run b ⟨pairs.pc, rfl⟩
  have bytesInput : MemsetBytesInput (BitVec.ofNat 64 base) (pairCursor base 3) ra d := {
    toLeafInput := tail.toLeafInput
    destination := (tail.frame .x10 (by decide) (by decide)).trans pairs.destination
    cursor := (tail.frame .x14 (by decide) (by decide)).trans pairs.cursor
    zero := (tail.frame .x11 (by decide) (by decide)).trans pairs.zero
    windows := region.tail_windows
    outside := region.tail_outside }
  obtain ⟨e, bytes, post⟩ := (memset_bytes d _ _ ra bytesInput).run d ⟨tail.pc, rfl⟩
  refine ⟨e, front.trans (loop.trans (dispatch.trans bytes)), ?_⟩
  refine { post.toEffectPost with memory := ?_, output := ?_, frame := ?_ }
  · rw [post.memory, tail.memory, pairs.memory, frontPost.memory]
    rfl
  · exact post.output.trans (tail.output.trans (pairs.output.trans frontPost.output))
  · have tailIncl : ∀ n ∈ [13, 5], n ∈ [6, 14, 15, 13, 12, 5] := by decide
    have loopIncl : ∀ n ∈ [14], n ∈ [6, 14, 15, 13, 12, 5] := by decide
    have frontIncl : ∀ n ∈ [6, 14, 15, 13, 12], n ∈ [6, 14, 15, 13, 12, 5] := by decide
    intro r outside noise
    exact (post.frame r (by simp) noise).trans ((tail.frame r
      (fun n hn => outside n (tailIncl n hn)) noise).trans ((pairs.frame r
      (fun n hn => outside n (loopIncl n hn)) noise).trans (frontPost.frame r
      (fun n hn => outside n (frontIncl n hn)) noise)))
end OCaml.Vm.Boot.Startup
