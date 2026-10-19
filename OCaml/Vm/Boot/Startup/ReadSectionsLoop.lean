import OCaml.Vm.Boot.Startup.ReadSections
import OCaml.Vm.Boot.Startup.NewNode
import Vsa.Sim.IndexedLoop
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_read_section_descriptors' loop: each descriptor's big-endian length
reversed in place. -/

/-- Where byte `k` of the swapped table comes from in the file's table. -/
def sectionSwap (k : Nat) : Nat := if k % 8 < 4 then k else k - k % 8 + (11 - k % 8)

/-- Byte `k` of the section table as read. -/
def sectionRaw (k : Nat) : BitVec 8 := (WhileMinImage.initialMem[sectionSource + k]?).getD 0

/-- Byte `k` of the section table with every length's byte order reversed. -/
def sectionByte (k : Nat) : BitVec 8 := sectionRaw (sectionSwap k)

/-- The loop at descriptor `i`: the first `i` lengths reversed. -/
structure SwapAt (H : List (Nat × Nat)) (capacity : Nat) (blk : BitVec 64) (start : Config) (i : Nat)
    (d : Config) : Prop where
  pc : PCAt (if i < 7 then 0x80004b70#64 else 0x80004ba8#64) d
  regs : GHolds d.σ [(8, WhileMinElfParse.trailSlot), (14, BitVec.ofNat 64 i), (2, sectionsStack)]
  result : ∃ v, gprGet d.σ 10 = some v
  ready : RuntimeReady ((blk.toNat, 56) :: H) capacity sectionsStack jal_80004b5c_call.link d
  bound : i ≤ 7
  table : ∀ k, k < 56 → (d.σ.mem[blk.toNat + k]?).getD 0 = if k / 8 < i then sectionByte k else sectionRaw k
  kept : ∀ x, x < blk.toNat ∨ blk.toNat + 56 ≤ x → (d.σ.mem[x]?).getD 0 = (start.σ.mem[x]?).getD 0

theorem SwapAt.index {H capacity blk start i d} (S : SwapAt H capacity blk start i d) :
    ((gprGet d.σ 14).getD 0).toNat = i := by
  rw [gholds_lookup (n := 14) _ S.regs rfl]
  have := S.bound
  simp only [Option.getD_some, BitVec.toNat_ofNat]
  omega

theorem read_sections_iteration {H capacity blk start i d} (S : SwapAt H capacity blk start i d) (hi : i < 7)
    (blkWord : bytesT start.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk)
    (numWord : read4 start.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord)
    (lo : heapStart ≤ blk.toNat) (hiB : blk.toNat + 56 ≤ heapEnd) :
    ∃ d', Steps d d' ∧ SwapAt H capacity blk start (i + 1) d' := by
  have pc : PCAt 0x80004b70#64 d := by have := S.pc; simp only [hi, ite_true] at this; exact this
  have htr : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
  have htr16 : (WhileMinElfParse.trailSlot + 16#64).toNat = WhileMinElfParse.trailSlot.toNat + 16 := by decide
  have text : Image.textBase + Image.textSize ≤ heapStart := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ heapStart := by decide
  have globals : Layout.sym_Caml_state + 8 ≤ heapStart ∧ Layout.sym_pool + 8 ≤ heapStart := by decide
  unfold heapEnd at hiB
  unfold heapStart at lo text rodata globals
  let T : Nat → BitVec 8 := fun j => sectionRaw (8 * i + 4 + j)
  have entNat (j : Nat) (hj : j < 8) :
      (blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = blk.toNat + 8 * i + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (a := blk.toNat + 8 * i) (by omega),
      Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]
  have blkW : bytesT d.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk := by
    rw [word_observed (m := start.σ.mem) _ fun k hk => S.kept _ (Or.inr (by omega))]; exact blkWord
  have num : read4 d.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord := by
    rw [read4_observed (m := start.σ.mem) _ fun k hk => S.kept _ (Or.inr (by omega))]; exact numWord
  have field (j : Nat) (hj : j < 4) : WriteWindow (blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (4 + j)) 1 := by
    constructor <;> rw [entNat (4 + j) (by omega)]
    · omega
    · omega
    · unfold Layout.sym_tohost; omega
    · omega
  have len (j : Nat) (hj : j < 4) :
      (d.σ.mem[(blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (4 + j)).toNat]?).getD 0 = T j := by
    rw [entNat (4 + j) (by omega), show blk.toNat + 8 * i + (4 + j) = blk.toNat + (8 * i + 4 + j) by omega,
      S.table _ (by omega), show (8 * i + 4 + j) / 8 = i by omega]
    simp only [Nat.lt_irrefl, ite_false, T]
  have outside : ImageOutside (sectionSwapLog (blk + BitVec.ofNat 64 (8 * i)) T) := by
    constructor <;> simp only [sectionSwapLog, OutLRange, and_true] <;>
      rw [entNat 4 (by decide), entNat 7 (by decide), entNat 5 (by decide), entNat 6 (by decide)] <;> omega
  obtain ⟨d1, run1, p1⟩ := (read_sections_swap d jal_80004b5c_call.link WhileMinElfParse.trailSlot blk
    (blk + BitVec.ofNat 64 (8 * i)) i hi T S.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ S.regs rfl, gholds_lookup (n := 14) _ S.regs rfl, trivial⟩ (by constructor <;> decide)
    blkW rfl field len outside).run d ⟨pc, rfl⟩
  have inside : LogInW [⟨blk.toNat, blk.toNat + 56⟩] (sectionSwapLog (blk + BitVec.ofNat 64 (8 * i)) T) := by
    simp only [sectionSwapLog, LogInW, InsideW]
    rw [entNat 4 (by decide), entNat 7 (by decide), entNat 5 (by decide), entNat 6 (by decide)]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> omega
  have ready1 := S.ready.window_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p1.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans S.ready.stack)
    ((p1.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans S.ready.raReg)
    S.ready.aligned inside (arenaWindow_out_pins (by unfold heapStart; omega))
    (by simp only [OutWRange, and_true]; omega) (by simp only [OutWRange, and_true]; omega)
    (fun a foot => by
      simp only [OutW, and_true]
      rcases foot with global | ⟨_, _, out⟩
      · left; unfold allocGlobal InRange at *; omega
      · have := out (blk.toNat, 56) (List.mem_cons_self ..)
        unfold InExt at this; omega)
  have num1 : read4 d1.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord := by
    rw [read4_observed (m := d.σ.mem) _ fun k hk => by
      rw [p1.memory, writeLog_out _ _ _ (by
        simp only [sectionSwapLog, OutL, and_true]
        rw [entNat 4 (by decide), entNat 7 (by decide), entNat 5 (by decide), entNat 6 (by decide)]; omega)]]
    exact num
  -- the table after this descriptor
  have table1 (k : Nat) (hk : k < 56) : (d1.σ.mem[blk.toNat + k]?).getD 0 =
      if k / 8 < i + 1 then sectionByte k else sectionRaw k := by
    rw [p1.memory]
    by_cases mine : k / 8 = i ∧ 4 ≤ k % 8
    · have byte (idx j : Nat) (hj : j < 8) (e : k = 8 * i + j)
          (entry : (sectionSwapLog (blk + BitVec.ofNat 64 (8 * i)) T)[idx]? =
            some ((blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat, 1, lbuWord (T (7 - j))))
          (out : OutL ((sectionSwapLog (blk + BitVec.ofNat 64 (8 * i)) T).drop (idx + 1))
            ((blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat)) :
          ((writeLog d.σ.mem (sectionSwapLog (blk + BitVec.ofNat 64 (8 * i)) T))[blk.toNat + k]?).getD 0 =
            T (7 - j) := by
        rw [show blk.toNat + k = (blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat by
          rw [entNat j hj]; omega, byte_writeLog_at _ _ idx _ _ entry out, sb_lbu]
      have swapped (j : Nat) (hj : 4 ≤ j ∧ j < 8) (e : k = 8 * i + j) :
          (if k / 8 < i + 1 then sectionByte k else sectionRaw k) = T (7 - j) := by
        simp only [show k / 8 < i + 1 by omega, ite_true]
        simp only [sectionByte, sectionSwap, T, show ¬ k % 8 < 4 by omega, ite_false]
        congr 1; omega
      have outs : ∀ j, j < 8 → (blk + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = blk.toNat + 8 * i + j :=
        entNat
      rcases (by omega : k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7) with r | r | r | r
      · rw [byte 0 4 (by decide) (by omega) rfl (by
          simp only [sectionSwapLog, List.drop, OutL, and_true]
          rw [outs 7 (by decide), outs 5 (by decide), outs 6 (by decide), outs 4 (by decide)]; omega),
          swapped 4 (by omega) (by omega)]
      · rw [byte 2 5 (by decide) (by omega) rfl (by
          simp only [sectionSwapLog, List.drop, OutL, and_true]
          rw [outs 6 (by decide), outs 5 (by decide)]; omega), swapped 5 (by omega) (by omega)]
      · rw [byte 3 6 (by decide) (by omega) rfl (by simp only [sectionSwapLog, List.drop, OutL]),
          swapped 6 (by omega) (by omega)]
      · rw [byte 1 7 (by decide) (by omega) rfl (by
          simp only [sectionSwapLog, List.drop, OutL, and_true]
          rw [outs 5 (by decide), outs 6 (by decide), outs 7 (by decide)]; omega),
          swapped 7 (by omega) (by omega)]
    · rw [writeLog_out _ _ _ (by
          simp only [sectionSwapLog, OutL, and_true]
          rw [entNat 4 (by decide), entNat 7 (by decide), entNat 5 (by decide), entNat 6 (by decide)]; omega),
        S.table k hk]
      by_cases below : k / 8 < i
      · simp only [below, show k / 8 < i + 1 by omega, ite_true]
      · simp only [below, ite_false]
        by_cases same : k / 8 = i
        · simp only [show k / 8 < i + 1 by omega, ite_true, sectionByte, sectionSwap, show k % 8 < 4 by omega]
        · simp only [show ¬ k / 8 < i + 1 by omega, ite_false]
  have kept1 (x : Nat) (out : x < blk.toNat ∨ blk.toNat + 56 ≤ x) :
      (d1.σ.mem[x]?).getD 0 = (start.σ.mem[x]?).getD 0 := by
    rw [p1.memory, writeLog_out _ _ _ (by
      simp only [sectionSwapLog, OutL, and_true]
      rw [entNat 4 (by decide), entNat 7 (by decide), entNat 5 (by decide), entNat 6 (by decide)]; omega)]
    exact S.kept x out
  have next {d2 : Config} {pc2 : BitVec 64} {regs2 : GRegs}
      (p2 : WriteRegistersPost [15] [] d1 pc2 (lbuWord (T 3)) regs2 d2)
      (pcOk : PCAt (if i + 1 < 7 then 0x80004b70#64 else 0x80004ba8#64) d2)
      (r14 : gprGet d2.σ 14 = some (BitVec.ofNat 64 (i + 1))) (cover : ∀ n ∈ [15], n ∈ keysG regs2) :
      SwapAt H capacity blk start (i + 1) d2 := by
    have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ≠ 15) : gprGet d2.σ n = gprGet d1.σ n :=
      p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have stack2 : gprGet d2.σ 2 = some sectionsStack :=
      (keep 2 (by decide) (by decide) (by decide)).trans ready1.stack
    have mem2 : d2.σ.mem = d1.σ.mem := p2.memory
    exact {
      pc := pcOk
      regs := ⟨(keep 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ p1.regs rfl), r14,
        stack2, trivial⟩
      result := ⟨_, (keep 10 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 10) _ p1.regs rfl)⟩
      ready := ready1.stack_log p2 (by decide) cover (by decide) stack2
        ((keep 1 (by decide) (by decide) (by decide)).trans ready1.raReg) ready1.aligned
        (show NativeFrame sectionsStack 32 by constructor <;> decide) (by simp only [LogInW])
      bound := by omega
      table := fun k hk => by rw [mem2]; exact table1 k hk
      kept := fun x out => by rw [mem2]; exact kept1 x out }
  by_cases more : i + 1 < 7
  · obtain ⟨d2, run2, p2⟩ := (read_sections_again d1 jal_80004b5c_call.link WhileMinElfParse.trailSlot
      (lbuWord (T 3)) (i + 1) more ready1.toLeafInput
      ⟨gholds_lookup (n := 8) _ p1.regs rfl, gholds_lookup (n := 14) _ p1.regs rfl,
        gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩ (by constructor <;> decide) num1).run d1 ⟨p1.pc, rfl⟩
    exact ⟨d2, run1.trans run2, next p2 (by simp only [more, ite_true]; exact p2.pc) (gholds_lookup (n := 14) _ p2.regs rfl)
      (by simp only [keysG]; decide)⟩
  · have six : i = 6 := by omega
    subst six
    obtain ⟨d2, run2, p2⟩ := (read_sections_done d1 jal_80004b5c_call.link WhileMinElfParse.trailSlot
      (lbuWord (T 3)) ready1.toLeafInput
      ⟨gholds_lookup (n := 8) _ p1.regs rfl, gholds_lookup (n := 14) _ p1.regs rfl,
        gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩ (by constructor <;> decide) num1).run d1 ⟨p1.pc, rfl⟩
    exact ⟨d2, run1.trans run2, next p2 (by simp only [more, ite_false]; exact p2.pc) (gholds_lookup (n := 14) _ p2.regs rfl)
      (by simp only [keysG]; decide)⟩
theorem read_sections_loop {H capacity node ra s0 s1 s2 blk c start}
    (L : ReadSectionsLoaded H capacity node ra s0 s1 s2 blk c start) :
    ∃ d, Steps start d ∧ SwapAt H capacity blk start 7 d := by
  have lo : heapStart ≤ blk.toNat := L.fresh.2.1
  have hi : blk.toNat + 56 ≤ heapEnd := L.fresh.2.2.1
  have loop := indexedLoop (I := SwapAt H capacity blk start) (index := fun d => ((gprGet d.σ 14).getD 0).toNat)
    (start := 0) (count := 7) (fun _ _ h => h.index) (fun _ _ h => h.bound)
    (fun i d ⟨h, lt⟩ => read_sections_iteration h lt L.blkWord L.numWord lo hi)
  exact loop start {
    pc := by simp only [show 0 < 7 by decide, ite_true]; exact L.pc
    regs := ⟨gholds_lookup (n := 8) _ L.regs rfl, gholds_lookup (n := 14) _ L.regs rfl,
      gholds_lookup (n := 2) _ L.regs rfl, trivial⟩
    result := ⟨_, gholds_lookup (n := 10) _ L.regs rfl⟩
    ready := L.ready
    bound := by decide
    table := fun k hk => by simp only [Nat.not_lt_zero, ite_false]; exact L.table k hk
    kept := fun _ _ => rfl }

/-- caml_read_section_descriptors returned: the section table, lengths in host
order, is in the fresh block `blk` and `trail.section` points at it. -/
structure ReadSectionsDone (H : List (Nat × Nat)) (capacity : Nat) (node ra s0 s1 s2 blk : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, parameterStack), (18, s2), (9, s1), (8, s0), (1, ra)]
  ready : RuntimeReady ((blk.toNat, 56) :: H) capacity parameterStack ra after
  fresh : FreshBlock vsaLayoutP H blk.toNat 56
  blkWord : bytesT after.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk
  numWord : read4 after.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord
  table : ∀ k, k < 56 → (after.σ.mem[blk.toNat + k]?).getD 0 = sectionByte k
  pos : bytesT after.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64
  file : OpenFile after.σ.mem node
  embed : EmbedImage after
  /-- The caller's frame, apart from `trail.section`. -/
  caller : ∀ x, parameterStack.toNat ≤ x →
    (x < WhileMinElfParse.trailSlot.toNat + 16 ∨ WhileMinElfParse.trailSlot.toNat + 24 ≤ x) →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  /-- Low memory outside the allocator, `errno` and the file position. -/
  globals : ∀ x, x < heapEnd → ¬ vsaFoot H x → OutW errnoWindows x →
    (x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem read_section_descriptors (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (node ra s0 s1 s2 : BitVec 64) (A : ReadSectionsCall H capacity charge node ra s0 s1 s2 c) :
    ∃ blk after, Steps c after ∧ ReadSectionsDone H capacity node ra s0 s1 s2 blk c after := by
  obtain ⟨blk, d1, run1, L⟩ := read_sections_load c H capacity charge node ra s0 s1 s2 A
  obtain ⟨d2, run2, S⟩ := read_sections_loop L
  have lo : heapStart ≤ blk.toNat := L.fresh.2.1
  have hi : blk.toNat + 56 ≤ heapEnd := L.fresh.2.2.1
  obtain ⟨v, hv⟩ := S.result
  have frame32 : NativeFrame parameterStack 32 := by constructor <;> decide
  have kept (x : Nat) (hx : heapEnd ≤ x) : (d2.σ.mem[x]?).getD 0 = (d1.σ.mem[x]?).getD 0 :=
    S.kept x (Or.inr (by omega))
  obtain ⟨d3, run3, p3⟩ := (read_sections_return d2 parameterStack ra s0 s1 s2 v jal_80004b5c_call.link
    S.ready.toLeafInput frame32 ⟨gholds_lookup (n := 2) _ S.regs rfl, hv, trivial⟩
    (fun off value member => by
      have range : off + 8 ≤ 32 := by
        simp only [readSectionsSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      rw [word_observed (m := d1.σ.mem) _ fun i hi => kept _ (by
        unfold nativeFrameBase heapEnd; rw [show parameterStack.toNat = 0x87ffff80 by decide]; omega)]
      exact L.saved off value member)
    A.ready.aligned).run d2 ⟨S.pc, rfl⟩
  have mem3 : d3.σ.mem = d2.σ.mem := p3.memory
  have htr16 : (WhileMinElfParse.trailSlot + 16#64).toNat = WhileMinElfParse.trailSlot.toNat + 16 := by decide
  have htr : WhileMinElfParse.trailSlot.toNat = 0x87ffffa8 := by decide
  have hsp : parameterStack.toNat = 0x87ffff80 := by decide
  unfold heapEnd at hi kept
  unfold heapStart at lo
  refine ⟨blk, d3, run1.trans (run2.trans run3), {
    pc := p3.pc
    regs := ⟨gholds_lookup (n := 2) _ p3.regs rfl, gholds_lookup (n := 18) _ p3.regs rfl,
      gholds_lookup (n := 9) _ p3.regs rfl, gholds_lookup (n := 8) _ p3.regs rfl,
      gholds_lookup (n := 1) _ p3.regs rfl, trivial⟩
    ready := S.ready.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p3.regs rfl) (gholds_lookup (n := 1) _ p3.regs rfl) A.ready.aligned frame32
      (by simp only [LogInW])
    fresh := L.fresh
    blkWord := by
      rw [mem3, word_observed (m := d1.σ.mem) _ fun i hi => kept _ (by omega)]; exact L.blkWord
    numWord := by
      rw [mem3, read4_observed (m := d1.σ.mem) _ fun i hi => kept _ (by omega)]; exact L.numWord
    table := fun k hk => by
      rw [mem3, S.table k hk]; simp only [show k / 8 < 7 by omega, ite_true]
    pos := by
      rw [mem3, word_observed (m := d1.σ.mem) _ fun i hi => S.kept _ (Or.inl (by unfold Layout.sym_fds; omega))]
      exact L.pos
    file := L.file.transport fun x hx => by
      have k := A.file_kept hx
      rw [mem3]; exact S.kept x (FreshBlock.out_kept L.fresh k.1 k.2)
    embed := ⟨fun a ha => by rw [mem3, kept a ha.1]; exact L.embed.byte a ha⟩
    caller := fun x hx out => by rw [mem3, kept x (by omega)]; exact L.caller x hx out
    globals := fun x hx nf errno pos => by
      rw [mem3, S.kept x (FreshBlock.out_kept L.fresh hx nf)]; exact L.globals x hx nf errno pos }⟩
end OCaml.Vm.Boot.Startup
