import OCaml.Vm.Boot.Startup.StrchrSteps
import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.IndexedLoop
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Boot.Startup.GprPresence
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- A covered register post keeps every register present. -/
theorem RegistersPost.present {writes mem before pc value regs after}
    (post : RegistersPost writes mem before pc value regs after) (p : OCaml.Vm.Boot.Startup.GprPresent before.σ)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) : OCaml.Vm.Boot.Startup.GprPresent after.σ :=
  p.of_regs keys post.regs cover (fun r noise ws => post.frame r (fun n hn h => by
    have := ws n hn
    rw [h, beq_self_eq_true] at this
    contradiction) noise)

end OCaml.Vm.Primitives

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
  present : GprPresent c.σ

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
    frame := fun r outside noise => (post.frame r outside noise).trans (h.frame r outside noise)
    present := post.present h.present (by decide) (by simp only [keysG]; decide) }⟩
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
  present : GprPresent c.σ

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
    present := post.present h.present (by decide) (by simp only [strchrLooped, keysG]; decide) }⟩
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
  present : GprPresent c.σ

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
    frame := fun r outside noise => (post.frame r outside noise).trans (h.frame r outside noise)
    present := post.present h.present (by decide) (by simp only [keysG]; decide) }⟩
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
def strchrWrites : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 6, 28]

/-- Registers outside `strchr`'s writes keep their values. -/
structure StrchrFrame (before after : Config) : Prop where
  regs : ∀ r : Register, (∀ n ∈ strchrWrites, gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem StrchrFrame.trans {a b c} (f : StrchrFrame a b) (g : StrchrFrame b c) : StrchrFrame a c :=
  ⟨fun r out noise => (g.regs r out noise).trans (f.regs r out noise)⟩

theorem StrchrFrame.of_post {writes mem before pc value regs after}
    (post : RegistersPost writes mem before pc value regs after) (sub : ∀ n ∈ writes, n ∈ strchrWrites) :
    StrchrFrame before after :=
  ⟨fun r out noise => post.frame r (fun n hn => out n (sub n hn)) noise⟩

theorem readWindow_shift {a : BitVec 64} {len j : Nat} (h : ReadWindow a (len + 1)) (hj : j ≤ len) :
    ReadWindow (nameCursor a j) (len - j + 1) := by
  have nat := nameCursor_nat h hj
  have lo := h.lower
  have hi := h.upper
  constructor <;> rw [nat]
  · omega
  · omega
  · rcases h.htif with b | t
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- A string of `len` bytes, none '/', NUL-terminated. -/
structure SlashString (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (len : Nat) : Prop where
  region : ReadWindow a (len + 1)
  free : ∀ j, j < len → strByte m (a.toNat + j) ≠ 0#8 ∧ strByte m (a.toNat + j) ≠ 47#8
  nul : strByte m (a.toNat + len) = 0#8

theorem SlashString.tail {m a len} (h : SlashString m a len) {j : Nat} (hj : j ≤ len) :
    ScanTail m (nameCursor a j) (len - j) := by
  have nat := nameCursor_nat h.region hj
  refine ⟨readWindow_shift h.region hj, fun i hi => ?_, ?_⟩
  · rw [nat, Nat.add_assoc]; exact h.free (j + i) (by omega)
  · rw [nat, Nat.add_assoc, Nat.add_sub_cancel' hj]; exact h.nul

/-- How `strchr` reaches the NUL: in the byte phase, at the first aligned
word, or at a later word. -/
inductive StrchrPlan (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (len : Nat) : Prop
  | bytes : (∀ j, j ≤ len → (a.toNat + j) % 8 ≠ 0) → StrchrPlan m a len
  | first (K : Nat) : K ≤ len → (∀ j, j < K → (a.toNat + j) % 8 ≠ 0) → (a.toNat + K) % 8 = 0 →
      ReadWindow (nameCursor a K) 8 → setupTest (wordAt m (nameCursor a K)) ≠ 0#64 → StrchrPlan m a len
  | later (K n : Nat) : K ≤ len → (∀ j, j < K → (a.toNat + j) % 8 ≠ 0) → (a.toNat + K) % 8 = 0 →
      ReadWindow (nameCursor a K) 8 → setupTest (wordAt m (nameCursor a K)) = 0#64 →
      WordRun m (nameCursor a K) n → K + 8 * n ≤ len → StrchrPlan m a len

/-- `strchr(s, '/')` returned NULL. -/
structure StrchrMissDone (ra : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(10, 0#64), (1, ra), (15, 0#64), (13, 47#64)]
  present : GprPresent after.σ
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : StrchrFrame before after
theorem nameCursor_comp (a : BitVec 64) (j k : Nat) : nameCursor (nameCursor a j) k = nameCursor a (j + k) := by
  unfold nameCursor
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem byteAt_frame {a ra K start k c} (h : ByteAt a ra K start k c) : StrchrFrame start c :=
  ⟨fun r out noise => h.frame r (fun n hn => out n (by
    have sub : ∀ k ∈ [15, 10], k ∈ strchrWrites := by decide
    exact sub n hn)) noise⟩

theorem wordAt_frame {base ra n start j c} (h : WordAt base ra n start j c) : StrchrFrame start c :=
  ⟨fun r out noise => h.frame r (fun n hn => out n (by
    have sub : ∀ k ∈ [14, 10, 15, 11, 12], k ∈ strchrWrites := by decide
    exact sub n hn)) noise⟩

theorem nameCursor_zero_mul (a : BitVec 64) : nameCursor a (8 * 0) = a := by
  unfold nameCursor; rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero]

theorem nameCursor_zero (a : BitVec 64) : nameCursor a 0 = a := by
  unfold nameCursor; rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]

/-- From the NUL's byte at 0x7e0, return NULL. -/
theorem strchr_finish {ra : BitVec 64} {before c : Config} (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, 0#64), (13, 47#64)]) (pc : PCAt 0x800407e0#64 c) (present : GprPresent c.σ)
    (memory : c.σ.mem = before.σ.mem) (output : c.σ.sailOutput = before.σ.sailOutput)
    (frame : StrchrFrame before c) : ∃ d, Steps c d ∧ StrchrMissDone ra before d := by
  obtain ⟨d, run, post⟩ := (strchr_none c ra 0#64 leaf
    ⟨leaf.raReg, gholds_lookup (n := 15) _ regs (by rfl), gholds_lookup (n := 13) _ regs (by rfl), trivial⟩).run
    c ⟨pc, rfl⟩
  exact ⟨d, run, {
    pc := post.pc
    regs := ⟨gholds_lookup (n := 10) _ post.regs (by rfl), gholds_lookup (n := 1) _ post.regs (by rfl),
      gholds_lookup (n := 15) _ post.regs (by rfl), gholds_lookup (n := 13) _ post.regs (by rfl), trivial⟩
    present := post.present present (by decide) (by simp only [keysG]; decide)
    memory := (show d.σ.mem = c.σ.mem from post.memory).trans memory
    output := post.output.trans output
    frame := frame.trans (StrchrFrame.of_post post (by decide)) }⟩

/-- A scan tail from its first loaded byte to NULL. -/
theorem strchr_finish_scan {ra s : BitVec 64} {K : Nat} {before c : Config} (tail : ScanTail c.σ.mem s K)
    (at0 : ScanAt s K ra c 0 c) (memory : c.σ.mem = before.σ.mem) (output : c.σ.sailOutput = before.σ.sailOutput)
    (frame : StrchrFrame before c) : ∃ d, Steps c d ∧ StrchrMissDone ra before d := by
  obtain ⟨e, run1, scanned⟩ := scan_loop c tail c at0
  have pcE : PCAt 0x800407e0#64 e := by simpa using scanned.pc
  have nul : nameByteWord (strByte c.σ.mem (s.toNat + K)) = 0#64 := by rw [tail.nul]; rfl
  have r15 := gholds_lookup (n := 15) _ scanned.regs (by rfl)
  rw [nul] at r15
  obtain ⟨d, run2, done⟩ := strchr_finish scanned.leaf ⟨r15, gholds_lookup (n := 13) _ scanned.regs (by rfl), trivial⟩
    pcE scanned.present (scanned.memory.trans memory) (scanned.output.trans output)
    (frame.trans ⟨fun r out noise => scanned.frame r (fun n hn => out n (by
      have sub : ∀ k ∈ [10, 15], k ∈ strchrWrites := by decide
      exact sub n hn)) noise⟩)
  exact ⟨d, run1.trans run2, done⟩
/-- **`strchr(a, '/')` over a string without '/'** returns NULL. -/
theorem strchr_miss (c : Config) (a ra : BitVec 64) (len : Nat) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, 47#64), (10, a), (1, ra)]) (present : GprPresent c.σ)
    (string : SlashString c.σ.mem a len) (plan : StrchrPlan c.σ.mem a len) :
    FnSummary 0x80040704#64 (fun e => e = c) (StrchrMissDone ra c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨e0, run1, entered⟩ := (strchr_entry c a ra leaf regs).run c ⟨pc, rfl⟩
  have frame0 := StrchrFrame.of_post entered (by decide)
  have start (K : Nat) : ByteAt a ra K e0 0 e0 :=
    { leaf := ⟨entered.good, entered.image, entered.minstret, gholds_lookup (n := 1) _ entered.regs (by rfl),
        leaf.aligned, entered.tick⟩
      bound := Nat.zero_le _
      pc := by
        change pcOf e0 = some _
        rw [Nat.add_zero]
        exact entered.pc
      regs := by
        rw [nameCursor_zero]
        exact ⟨gholds_lookup (n := 10) _ entered.regs (by rfl), gholds_lookup (n := 13) _ entered.regs (by rfl),
          gholds_lookup (n := 11) _ entered.regs (by rfl), gholds_lookup (n := 1) _ entered.regs (by rfl), trivial⟩
      memory := rfl
      output := rfl
      frame := fun _ _ _ => rfl
      present := entered.present present (by decide) (by simp only [keysG]; decide) }
  have mem0 : e0.σ.mem = c.σ.mem := entered.memory
  have sub (K : Nat) (hK : K ≤ len) : ReadWindow a (K + 1) := by
    have r := string.region
    exact ⟨r.lower, by have := r.upper; omega, by rcases r.htif with b | t; exact Or.inl (by omega); exact Or.inr t⟩
  -- the aligned-word paths share load, masks and test
  have wordPath (K : Nat) (hK : K ≤ len) (first : ∀ j, j < K → (a.toNat + j) % 8 ≠ 0)
      (aligned : (a.toNat + K) % 8 = 0) (window : ReadWindow (nameCursor a K) 8)
      (finish : ∀ t, (t.σ.mem = c.σ.mem) → t.σ.sailOutput = c.σ.sailOutput → StrchrFrame c t →
        GprPresent t.σ →
        PCAt (if setupTest (wordAt c.σ.mem (nameCursor a K)) = 0#64 then 0x80040798#64 else 0x800407d8#64) t →
        GHolds t.σ (strchrTested (nameCursor a K) ra (wordAt c.σ.mem (nameCursor a K))) →
        LeafInput ra t → ∃ d, Steps t d ∧ StrchrMissDone ra c d) :
      ∃ d, Steps c d ∧ StrchrMissDone ra c d := by
    have run : ByteRun e0.σ.mem a K :=
      ⟨sub K hK, fun j hj => by rw [mem0]; exact string.free j (by omega), first⟩
    obtain ⟨b, run2, ba⟩ := byte_loop e0 run e0 (start K)
    have pcB : PCAt 0x8004072c#64 b := by
      have p := ba.pc
      rw [if_pos aligned] at p
      exact p
    obtain ⟨l, run3, loaded⟩ := (strchr_load b (nameCursor a K) ra ba.leaf
      ⟨gholds_lookup (n := 11) _ ba.regs (by rfl), gholds_lookup (n := 10) _ ba.regs (by rfl),
        gholds_lookup (n := 13) _ ba.regs (by rfl), gholds_lookup (n := 1) _ ba.regs (by rfl), trivial⟩
      window).run b ⟨pcB, rfl⟩
    have wordEq : bytesT b.σ.mem (nameCursor a K).toNat 8 = wordAt c.σ.mem (nameCursor a K) := by
      rw [ba.memory, mem0]; rfl
    rw [wordEq] at loaded
    have leafL : LeafInput ra l := ⟨loaded.good, loaded.image, loaded.minstret,
      gholds_lookup (n := 1) _ loaded.regs (by rfl), leaf.aligned, loaded.tick⟩
    obtain ⟨m1, run4, masked⟩ := (strchr_masks l (nameCursor a K) ra (wordAt c.σ.mem (nameCursor a K)) leafL
      loaded.regs).run l ⟨loaded.pc, rfl⟩
    have leafM : LeafInput ra m1 := ⟨masked.good, masked.image, masked.minstret,
      gholds_lookup (n := 1) _ masked.regs (by rfl), leaf.aligned, masked.tick⟩
    obtain ⟨t, run5, tested⟩ := (strchr_test m1 (nameCursor a K) ra (wordAt c.σ.mem (nameCursor a K)) leafM
      masked.regs).run m1 ⟨masked.pc, rfl⟩
    have leafT : LeafInput ra t := ⟨tested.good, tested.image, tested.minstret,
      gholds_lookup (n := 1) _ tested.regs (by rfl), leaf.aligned, tested.tick⟩
    have memT : t.σ.mem = c.σ.mem := (show t.σ.mem = m1.σ.mem from tested.memory).trans
      ((show m1.σ.mem = l.σ.mem from masked.memory).trans ((show l.σ.mem = b.σ.mem from loaded.memory).trans
        (ba.memory.trans mem0)))
    have presT := tested.present (masked.present (loaded.present ba.present (by decide)
      (by simp only [keysG]; decide)) (by decide) (by simp only [strchrMasked, keysG]; decide)) (by decide)
      (by simp only [strchrTested, keysG]; decide)
    have pre := run2.trans (run3.trans (run4.trans run5))
    exact finish t memT
      (tested.output.trans (masked.output.trans (loaded.output.trans (ba.output.trans entered.output))))
      (frame0.trans ((byteAt_frame ba).trans ((StrchrFrame.of_post loaded (by decide)).trans
        ((StrchrFrame.of_post masked (by decide)).trans (StrchrFrame.of_post tested (by decide))))))
      presT tested.pc tested.regs leafT |>.elim fun d ⟨r, done⟩ => ⟨d, run1.trans (pre.trans r), done⟩
  -- scanning from a hit word's start to the NUL
  have scanFrom (f : Config) (j : Nat) (hj : j ≤ len) (memF : f.σ.mem = c.σ.mem)
      (outF : f.σ.sailOutput = c.σ.sailOutput) (frameF : StrchrFrame c f) (presF : GprPresent f.σ)
      (leafF : LeafInput ra f)
      (pcF : PCAt (if strByte c.σ.mem (a.toNat + j) = 0#8 then 0x800407e0#64 else 0x800407d0#64) f)
      (regsF : GHolds f.σ [(15, nameByteWord (strByte c.σ.mem (a.toNat + j))), (10, nameCursor a j), (13, 47#64)]) :
      ∃ d, Steps f d ∧ StrchrMissDone ra c d := by
    have tail : ScanTail f.σ.mem (nameCursor a j) (len - j) := by rw [memF]; exact string.tail hj
    have byteNat : strByte f.σ.mem ((nameCursor a j).toNat + 0) = strByte c.σ.mem (a.toNat + j) := by
      rw [memF, nameCursor_nat string.region hj, Nat.add_zero]
    have at0 : ScanAt (nameCursor a j) (len - j) ra f 0 f :=
      { leaf := leafF
        bound := Nat.zero_le _
        pc := by
          by_cases last : j = len
          · subst last
            rw [if_neg (by omega)]
            have p := pcF
            rw [if_pos string.nul] at p
            exact p
          · rw [if_pos (by omega)]
            have p := pcF
            rw [if_neg (string.free j (by omega)).1] at p
            exact p
        regs := by
          rw [nameCursor_comp, Nat.add_zero, byteNat]
          exact ⟨gholds_lookup (n := 10) _ regsF (by rfl), gholds_lookup (n := 13) _ regsF (by rfl),
            gholds_lookup (n := 15) _ regsF (by rfl), trivial⟩
        memory := rfl
        output := rfl
        frame := fun _ _ _ => rfl
        present := presF }
    exact strchr_finish_scan tail at0 memF outF frameF
  cases plan with
  | bytes unaligned =>
    have run : ByteRun e0.σ.mem a len :=
      ⟨string.region, fun j hj => by rw [mem0]; exact string.free j hj, fun j hj => unaligned j (by omega)⟩
    obtain ⟨b, run2, ba⟩ := byte_loop e0 run e0 (start len)
    have pcB : PCAt 0x80040714#64 b := by
      have p := ba.pc
      rw [if_neg (unaligned len (Nat.le_refl _))] at p
      exact p
    obtain ⟨n0, run3, nul⟩ := (strchr_byte_nul b (nameCursor a len) ra ba.leaf ba.regs
      (name_window string.region (Nat.le_refl _))
      (by rw [nameCursor_nat string.region (Nat.le_refl _), ba.memory, mem0]; exact string.nul)).run b ⟨pcB, rfl⟩
    obtain ⟨d, run4, done⟩ := strchr_finish ⟨nul.good, nul.image, nul.minstret,
        gholds_lookup (n := 1) _ nul.regs (by rfl), leaf.aligned, nul.tick⟩
      ⟨gholds_lookup (n := 15) _ nul.regs (by rfl), gholds_lookup (n := 13) _ nul.regs (by rfl), trivial⟩ nul.pc
      (nul.present ba.present (by decide) (by simp only [keysG]; decide))
      ((show n0.σ.mem = b.σ.mem from nul.memory).trans (ba.memory.trans mem0))
      (nul.output.trans (ba.output.trans entered.output))
      (frame0.trans ((byteAt_frame ba).trans (StrchrFrame.of_post nul (by decide))))
    exact ⟨d, run1.trans (run2.trans (run3.trans run4)), done⟩
  | first K hK firstBytes aligned window hit =>
    apply wordPath K hK firstBytes aligned window
    intro t memT outT frameT presT pcT regsT leafT
    rw [if_neg hit] at pcT
    obtain ⟨f, run6, scanned⟩ := (strchr_scan_first t (nameCursor a K) ra (strByte c.σ.mem (a.toNat + K)) leafT
      ⟨gholds_lookup (n := 10) _ regsT (by rfl), gholds_lookup (n := 13) _ regsT (by rfl), trivial⟩
      ⟨window.lower, by have := window.upper; omega, by rcases window.htif with b | h; exact Or.inl (by omega); exact Or.inr h⟩
      (by rw [memT, nameCursor_nat string.region hK]; rfl)).run t ⟨pcT, rfl⟩
    obtain ⟨d, run7, done⟩ := scanFrom f K hK ((show f.σ.mem = t.σ.mem from scanned.memory).trans memT)
      (scanned.output.trans outT) (frameT.trans (StrchrFrame.of_post scanned (by decide)))
      (scanned.present presT (by decide) (by simp only [keysG]; decide))
      ⟨scanned.good, scanned.image, scanned.minstret, (scanned.frame .x1 (by decide) (by decide)).trans leafT.raReg,
        leaf.aligned, scanned.tick⟩ scanned.pc scanned.regs
    exact ⟨d, run6.trans run7, done⟩
  | later K n hK firstBytes aligned window clear words reach =>
    apply wordPath K hK firstBytes aligned window
    intro t memT outT frameT presT pcT regsT leafT
    rw [if_pos clear] at pcT
    have wordsT : WordRun t.σ.mem (nameCursor a K) n := by rw [memT]; exact words
    have at0 : WordAt (nameCursor a K) ra n t 0 t :=
      { leaf := leafT
        bound := Nat.zero_le _
        pc := by rw [if_pos (show 0 < n from words.positive)]; exact pcT
        regs := by
          rw [nameCursor_zero_mul]
          exact ⟨gholds_lookup (n := 10) _ regsT (by rfl), gholds_lookup (n := 17) _ regsT (by rfl),
            gholds_lookup (n := 16) _ regsT (by rfl), gholds_lookup (n := 6) _ regsT (by rfl), trivial⟩
        memory := rfl
        output := rfl
        frame := fun _ _ _ => rfl
        present := presT }
    obtain ⟨w, run6, looped⟩ := word_loop t wordsT t at0
    have pcW : PCAt 0x800407c8#64 w := by simpa using looped.pc
    have sNat : nameCursor (nameCursor a K) (8 * n) = nameCursor a (K + 8 * n) := nameCursor_comp a K (8 * n)
    have r10 := gholds_lookup (n := 10) _ looped.regs (by rfl)
    rw [sNat] at r10
    have r13 : gprGet w.σ 13 = some 47#64 :=
      (looped.frame .x13 (by decide) (by decide)).trans (gholds_lookup (n := 13) _ regsT (by rfl))
    obtain ⟨f, run7, scanned⟩ := (strchr_scan_word w (nameCursor a (K + 8 * n)) ra
      (strByte c.σ.mem (a.toNat + (K + 8 * n))) looped.leaf ⟨r10, r13, trivial⟩
      (name_window string.region reach)
      (by rw [looped.memory, memT, nameCursor_nat string.region reach]; rfl)).run w ⟨pcW, rfl⟩
    obtain ⟨d, run8, done⟩ := scanFrom f (K + 8 * n) reach
      ((show f.σ.mem = w.σ.mem from scanned.memory).trans (looped.memory.trans memT))
      (scanned.output.trans (looped.output.trans outT))
      (frameT.trans ((wordAt_frame looped).trans (StrchrFrame.of_post scanned (by decide))))
      (scanned.present looped.present (by decide) (by simp only [keysG]; decide))
      ⟨scanned.good, scanned.image, scanned.minstret, (scanned.frame .x1 (by decide) (by decide)).trans
        looped.leaf.raReg, leaf.aligned, scanned.tick⟩ scanned.pc scanned.regs
    exact ⟨d, run6.trans (run7.trans run8), done⟩
theorem testBit7_mod (n : Nat) : n.testBit 7 = (n % 256).testBit 7 := by
  have h := Nat.testBit_mod_two_pow n 8 7
  simp only [show (2 : Nat) ^ 8 = 256 from rfl, show (7 < 8) = True from by decide, decide_true,
    Bool.true_and] at h
  exact h.symm

theorem sum_bit7 (x y : BitVec 64) (hx : x.toNat % 256 = 0) (hy : y.toNat % 256 = 255) :
    (x + y).getLsbD 7 = true := by
  rw [BitVec.getLsbD, BitVec.toNat_add, testBit7_mod]
  have : (x.toNat + y.toNat) % 2 ^ 64 % 256 = 255 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 64)]
    omega
  rw [this]; decide

theorem bit7_zero (x : BitVec 64) (hx : x.toNat % 256 = 0) : x.getLsbD 7 = false := by
  rw [BitVec.getLsbD, testBit7_mod, hx]; decide

/-- A word whose first byte is NUL always hits the loop's test. -/
theorem loopTest_low_zero {x : BitVec 64} (hx : x.toNat % 256 = 0) : loopTest x ≠ 0#64 := by
  intro z
  have bit := congrArg (fun v : BitVec 64 => v.getLsbD 7) z
  simp only [loopTest, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor] at bit
  rw [sum_bit7 x lowOnes hx (by decide), bit7_zero x hx] at bit
  generalize ((x ^^^ slashPattern) + lowOnes).getLsbD 7 = t at bit
  cases t <;> revert bit <;> decide

/-- A word whose first byte is NUL always hits the first test. -/
theorem setupTest_low_zero {x : BitVec 64} (hx : x.toNat % 256 = 0) : setupTest x ≠ 0#64 := by
  intro z
  have bit := congrArg (fun v : BitVec 64 => v.getLsbD 7) z
  simp only [setupTest, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor] at bit
  rw [sum_bit7 x lowOnes hx (by decide), bit7_zero x hx] at bit
  generalize ((slashPattern ^^^ x) + lowOnes).getLsbD 7 = t at bit
  cases t <;> revert bit <;> decide
end OCaml.Vm.Boot.Startup
