import OCaml.Vm.Boot.Startup.StrchrSteps
import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.IndexedLoop
import OCaml.Vm.Primitives.LibraryEffects
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

/-! `strchr(s, '/')` over a string without '/': it returns NULL. -/

def strByte (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 8 := (m[a]?).getD 0

/-- The scan from `s`: `K` bytes that are neither NUL nor '/', then a NUL. -/
structure ScanTail (m : Std.ExtHashMap Nat (BitVec 8)) (s : BitVec 64) (K : Nat) : Prop where
  region : ReadWindow s (K + 1)
  free : ∀ j, j < K → strByte m (s.toNat + j) ≠ 0#8 ∧ strByte m (s.toNat + j) ≠ 47#8
  nul : strByte m (s.toNat + K) = 0#8

/-- The byte scan at offset `k` of a scan tail. -/
structure ScanAt (s : BitVec 64) (K : Nat) (ra : BitVec 64) (base : Config) (k : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  bound : k ≤ K
  pc : PCAt (if k < K then 0x800407d0#64 else 0x800407e0#64) c
  regs : GHolds c.σ [(10, nameCursor s k), (13, 47#64), (15, nameByteWord (strByte base.σ.mem (s.toNat + k)))]
  memory : c.σ.mem = base.σ.mem
  output : c.σ.sailOutput = base.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [10, 15], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = base.σ.regs.get? r

def scanIndex (s : BitVec 64) (c : Config) : Nat := ((gprGet c.σ 10).getD 0).toNat - s.toNat

theorem ScanAt.index {s K ra base k c} (region : ReadWindow s (K + 1)) (h : ScanAt s K ra base k c) :
    scanIndex s c = k := by
  simp only [scanIndex, gholds_lookup (n := 10) _ h.regs (by rfl), Option.getD_some,
    nameCursor_nat region h.bound]
  omega

theorem scan_iteration {s K ra base k c} (tail : ScanTail base.σ.mem s K) (h : ScanAt s K ra base k c)
    (hk : k < K) : ∃ d, Steps c d ∧ ScanAt s K ra base (k + 1) d := by
  have pc : PCAt 0x800407d0#64 c := by simpa only [hk, ite_true] using h.pc
  have nextAddr : (nameCursor s k + 1#64).toNat = s.toNat + (k + 1) := by
    rw [nameCursor_next, nameCursor_nat tail.region (by omega)]
  obtain ⟨d, run, post⟩ := (strchr_scan_step c (nameCursor s k) ra (strByte base.σ.mem (s.toNat + k))
    (strByte base.σ.mem (s.toNat + (k + 1))) h.leaf h.regs (tail.free k hk).2
    (by rw [nameCursor_next]; exact name_window tail.region (by omega))
    (by rw [nextAddr, h.memory]; rfl)).run c ⟨pc, rfl⟩
  refine ⟨d, run, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
    bound := by omega
    pc := ?_
    regs := ?_
    memory := post.memory.trans h.memory
    output := post.output.trans h.output
    frame := fun r outside noise => (post.frame r outside noise).trans (h.frame r outside noise) }⟩
  · change pcOf d = some _
    by_cases last : k + 1 = K
    · have zero : strByte base.σ.mem (s.toNat + (k + 1)) = 0#8 := by rw [last]; exact tail.nul
      have p := post.pc
      rw [if_pos zero] at p
      rw [if_neg (by omega)]
      exact p
    · have less : k + 1 < K := by omega
      have nz := (tail.free (k + 1) less).1
      simpa [nz, less] using post.pc
  · rw [← nameCursor_next]
    exact ⟨gholds_lookup (n := 10) _ post.regs (by rfl), gholds_lookup (n := 13) _ post.regs (by rfl),
      gholds_lookup (n := 15) _ post.regs (by rfl), trivial⟩

theorem scan_loop {s K ra} (base : Config) (tail : ScanTail base.σ.mem s K) :
    Triple (ScanAt s K ra base 0) (ScanAt s K ra base K) :=
  indexed_loop (scanIndex s) K 0 _ (fun _ _ h => h.bound) (fun _ _ h => h.index tail.region)
    (fun _ _ h hk => scan_iteration tail h hk)
def wordAt (m : Std.ExtHashMap Nat (BitVec 8)) (w : BitVec 64) : BitVec 64 := bytesT m w.toNat 8

/-- `n` aligned words from `base`: words 1 to n-1 test clear, word n hits. -/
structure WordRun (m : Std.ExtHashMap Nat (BitVec 8)) (base : BitVec 64) (n : Nat) : Prop where
  positive : 1 ≤ n
  window : ReadWindow base (8 * (n + 1))
  clear : ∀ i, 1 ≤ i → i < n → loopTest (wordAt m (nameCursor base (8 * i))) = 0#64
  hit : loopTest (wordAt m (nameCursor base (8 * n))) ≠ 0#64

theorem WordRun.word_window {m base n} (h : WordRun m base n) {i : Nat} (hi : i ≤ n) :
    ReadWindow (nameCursor base (8 * i)) 8 := by
  have lo := h.window.lower
  have hi' := h.window.upper
  have win : ReadWindow base (8 * n + 7 + 1) := by
    rw [show 8 * n + 7 + 1 = 8 * (n + 1) by omega]; exact h.window
  have nat := nameCursor_nat (k := 8 * i) win (by omega)
  constructor <;> rw [nat]
  · omega
  · omega
  · rcases h.window.htif with b | a
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- The word loop before word `j + 1`. -/
structure WordAt (base ra : BitVec 64) (n : Nat) (start : Config) (j : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  bound : j ≤ n
  pc : PCAt (if j < n then 0x80040798#64 else 0x800407c8#64) c
  regs : GHolds c.σ [(10, nameCursor base (8 * j)), (17, slashPattern), (16, lowOnes), (6, highBits)]
  memory : c.σ.mem = start.σ.mem
  output : c.σ.sailOutput = start.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [14, 10, 15, 11, 12], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = start.σ.regs.get? r
  present : ∀ k ∈ [14, 15, 11, 12], (gprGet c.σ k).isSome

def wordIndex (base : BitVec 64) (c : Config) : Nat := (((gprGet c.σ 10).getD 0).toNat - base.toNat) / 8
theorem nameCursor_add8 (p : BitVec 64) (k : Nat) : nameCursor p k + 8#64 = nameCursor p (k + 8) := by
  unfold nameCursor
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem WordRun.cursor_nat {m base n} (h : WordRun m base n) {i : Nat} (hi : i ≤ n) :
    (nameCursor base (8 * i)).toNat = base.toNat + 8 * i := by
  have win : ReadWindow base (8 * n + 7 + 1) := by
    rw [show 8 * n + 7 + 1 = 8 * (n + 1) by omega]; exact h.window
  exact nameCursor_nat win (by omega)

theorem WordAt.index {base ra n start j c} {m : Std.ExtHashMap Nat (BitVec 8)} (run : WordRun m base n)
    (h : WordAt base ra n start j c) : wordIndex base c = j := by
  simp only [wordIndex, gholds_lookup (n := 10) _ h.regs (by rfl), Option.getD_some, run.cursor_nat h.bound]
  omega

theorem word_iteration {base ra n start j c} (run : WordRun start.σ.mem base n) (h : WordAt base ra n start j c)
    (hj : j < n) : ∃ d, Steps c d ∧ WordAt base ra n start (j + 1) d := by
  have pc : PCAt 0x80040798#64 c := by simpa only [hj, ite_true] using h.pc
  have next : nameCursor base (8 * j) + 8#64 = nameCursor base (8 * (j + 1)) := by
    rw [nameCursor_add8]; congr 1
  obtain ⟨d, run1, post⟩ := (strchr_word_step c (nameCursor base (8 * j)) ra h.leaf h.regs
    (by rw [next]; exact run.word_window (by omega))).run c ⟨pc, rfl⟩
  have wordEq : bytesT c.σ.mem (nameCursor base (8 * j) + 8#64).toNat 8 =
      wordAt start.σ.mem (nameCursor base (8 * (j + 1))) := by
    rw [next, h.memory]; rfl
  refine ⟨d, run1, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
    bound := by omega
    pc := ?_
    regs := ?_
    memory := post.memory.trans h.memory
    output := post.output.trans h.output
    frame := fun r outside noise => (post.frame r (fun k hk => outside k (by simp at hk ⊢; omega)) noise).trans
      (h.frame r outside noise)
    present := ?_ }⟩
  · change pcOf d = some _
    have p := post.pc
    rw [wordEq] at p
    by_cases last : j + 1 = n
    · rw [if_neg (by omega)]
      rw [if_neg (by rw [last]; exact run.hit)] at p
      exact p
    · rw [if_pos (by omega)]
      rw [if_pos (run.clear (j + 1) (by omega) (by omega))] at p
      exact p
  · rw [← next]
    exact ⟨gholds_lookup (n := 10) _ post.regs (by rfl), gholds_lookup (n := 17) _ post.regs (by rfl),
      gholds_lookup (n := 16) _ post.regs (by rfl), gholds_lookup (n := 6) _ post.regs (by rfl), trivial⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [gholds_lookup (n := 14) _ post.regs (by rfl)]; rfl
    · rw [gholds_lookup (n := 15) _ post.regs (by rfl)]; rfl
    · rw [gholds_lookup (n := 11) _ post.regs (by rfl)]; rfl
    · rw [gholds_lookup (n := 12) _ post.regs (by rfl)]; rfl

theorem word_loop {base ra n} (start : Config) (run : WordRun start.σ.mem base n) :
    Triple (WordAt base ra n start 0) (WordAt base ra n start n) :=
  indexed_loop (wordIndex base) n 0 _ (fun _ _ h => h.bound) (fun _ _ h => h.index run)
    (fun _ _ h hk => word_iteration run h hk)
/-- The byte phase at offset `k`, heading for alignment after `K` bytes. -/
structure ByteAt (a ra : BitVec 64) (K : Nat) (start : Config) (k : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  bound : k ≤ K
  pc : PCAt (if (a.toNat + k) % 8 = 0 then 0x8004072c#64 else 0x80040714#64) c
  regs : GHolds c.σ [(10, nameCursor a k), (13, 47#64), (11, 47#64), (1, ra)]
  memory : c.σ.mem = start.σ.mem
  output : c.σ.sailOutput = start.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [15, 10], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = start.σ.regs.get? r

/-- `K` bytes up to the first aligned address, none NUL or '/'. -/
structure ByteRun (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (K : Nat) : Prop where
  region : ReadWindow a (K + 1)
  free : ∀ j, j < K → strByte m (a.toNat + j) ≠ 0#8 ∧ strByte m (a.toNat + j) ≠ 47#8
  first : ∀ j, j < K → (a.toNat + j) % 8 ≠ 0

def byteIndex (a : BitVec 64) (c : Config) : Nat := ((gprGet c.σ 10).getD 0).toNat - a.toNat

theorem ByteAt.index {a ra K start k c} (region : ReadWindow a (K + 1)) (h : ByteAt a ra K start k c) :
    byteIndex a c = k := by
  simp only [byteIndex, gholds_lookup (n := 10) _ h.regs (by rfl), Option.getD_some, nameCursor_nat region h.bound]
  omega

theorem byte_iteration {a ra K start k c} (run : ByteRun start.σ.mem a K) (h : ByteAt a ra K start k c)
    (hk : k < K) : ∃ d, Steps c d ∧ ByteAt a ra K start (k + 1) d := by
  have pc : PCAt 0x80040714#64 c := by
    have p := h.pc
    rw [if_neg (run.first k hk)] at p
    exact p
  have nat := nameCursor_nat run.region (Nat.le_of_lt hk)
  obtain ⟨d, run1, post⟩ := (strchr_byte_step c (nameCursor a k) ra (strByte start.σ.mem (a.toNat + k)) h.leaf
    h.regs (name_window run.region (by omega)) (by rw [nat, h.memory]; rfl) (run.free k hk).1
    (run.free k hk).2).run c ⟨pc, rfl⟩
  have nextNat : (nameCursor a k + 1#64).toNat = a.toNat + (k + 1) := by
    rw [nameCursor_next, nameCursor_nat run.region (by omega)]
  refine ⟨d, run1, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
    bound := by omega
    pc := ?_
    regs := ?_
    memory := post.memory.trans h.memory
    output := post.output.trans h.output
    frame := fun r outside noise => (post.frame r outside noise).trans (h.frame r outside noise) }⟩
  · change pcOf d = some _
    have p := post.pc
    rw [nextNat] at p
    exact p
  · rw [← nameCursor_next]
    exact ⟨gholds_lookup (n := 10) _ post.regs (by rfl), gholds_lookup (n := 13) _ post.regs (by rfl),
      gholds_lookup (n := 11) _ post.regs (by rfl), gholds_lookup (n := 1) _ post.regs (by rfl), trivial⟩

theorem byte_loop {a ra K} (start : Config) (run : ByteRun start.σ.mem a K) :
    Triple (ByteAt a ra K start 0) (ByteAt a ra K start K) :=
  indexed_loop (byteIndex a) K 0 _ (fun _ _ h => h.bound) (fun _ _ h => h.index run.region)
    (fun _ _ h hk => byte_iteration run h hk)
end OCaml.Vm.Boot.Startup
