import OCaml.Vm.Boot.Startup.SearchInPathSteps
import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.IndexedLoop
import OCaml.Vm.Boot.Startup.StrdupMeasure
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic VsaIris VsaIris.Sym VsaIris.MallocFast LeanRV64DExecutable OCaml.Vm.Primitives

/-- A slash-free C string of `len` bytes, read from total-byte memory. -/
structure PlainName (m : Vsa.MemRepr.Mem) (p : BitVec 64) (len : Nat) : Prop where
  bytes : CBytes m p.toNat len
  region : ReadWindow p (len + 1)
  noSlash : ∀ k, k < len → imgM m (p.toNat + k) ≠ 47#8
  positive : 0 < len

def slashScanIndex (p : BitVec 64) (c : Config) : Nat := ((gprGet c.σ 14).getD 0).toNat - p.toNat

structure SlashScanAt (p : BitVec 64) (len k : Nat) (ra a0 : BitVec 64) (initial c : Config) : Prop where
  leaf : LeafInput ra c
  bound : k ≤ len
  pc : PCAt (if k < len then 0x8002543c#64 else 0x8002546c#64) c
  cursor : gprGet c.σ 14 = some (nameCursor p k)
  current : gprGet c.σ 15 = some (nameByteWord (imgM initial.σ.mem (p.toNat + k)))
  slash : gprGet c.σ 13 = some 47#64
  value : gprGet c.σ 10 = some a0
  memory : c.σ.mem = initial.σ.mem
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [14, 15], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = initial.σ.regs.get? r

theorem SlashScanAt.index {p len k ra a0 initial c} (region : ReadWindow p (len + 1))
    (h : SlashScanAt p len k ra a0 initial c) : slashScanIndex p c = k := by
  simp only [slashScanIndex, h.cursor, Option.getD_some, nameCursor_nat region h.bound]
  omega

theorem slash_scan_iteration {p len k ra a0 initial c} (name : PlainName initial.σ.mem p len)
    (h : SlashScanAt p len k ra a0 initial c) (hk : k < len) :
    ∃ d, Steps c d ∧ SlashScanAt p len (k + 1) ra a0 initial d := by
  have pc : PCAt 0x8002543c#64 c := by simpa only [hk, ite_true] using h.pc
  have nextAddr : (nameCursor p k + 1#64).toNat = p.toNat + (k + 1) := by
    rw [nameCursor_next, nameCursor_nat name.region (by omega)]
  have zero : imgM initial.σ.mem (p.toNat + (k + 1)) = 0#8 ↔ decide (k + 1 = len) = true := by
    simp only [decide_eq_true_eq]
    constructor
    · intro z
      rcases Nat.lt_or_ge (k + 1) len with lt | ge
      · exact absurd z (name.bytes.nz (k + 1) lt)
      · omega
    · intro eq
      rw [eq]
      exact name.bytes.nul
  obtain ⟨d, run, post⟩ := (search_scan_step c ra (nameCursor p k) a0 (imgM initial.σ.mem (p.toNat + k))
    (imgM initial.σ.mem (p.toNat + (k + 1))) (decide (k + 1 = len)) h.leaf
    ⟨h.cursor, h.current, h.slash, h.value, trivial⟩ (name.noSlash k hk)
    (by rw [nameCursor_next]; exact name_window name.region (by omega))
    (by rw [nextAddr, h.memory]; rfl) zero).run c ⟨pc, rfl⟩
  refine ⟨d, run, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
    bound := by omega
    pc := ?_
    cursor := ?_
    current := gholds_lookup (n := 15) _ post.regs (by rfl)
    slash := gholds_lookup (n := 13) _ post.regs (by rfl)
    value := gholds_lookup (n := 10) _ post.regs (by rfl)
    memory := post.memory.trans h.memory
    output := post.output.trans h.output
    frame := fun r outside noise => (post.frame r outside noise).trans (h.frame r outside noise) }⟩
  · change pcOf d = some _
    by_cases last : k + 1 = len
    · simpa [last] using post.pc
    · have less : k + 1 < len := by omega
      simpa [last, less] using post.pc
  · have cursor := gholds_lookup (n := 14) _ post.regs (by rfl)
    rw [nameCursor_next] at cursor
    exact cursor

theorem slash_scan_loop {p len ra a0} (initial : Config) (name : PlainName initial.σ.mem p len) :
    Triple (SlashScanAt p len 0 ra a0 initial) (SlashScanAt p len len ra a0 initial) :=
  indexed_loop (slashScanIndex p) len 0 _ (fun _ _ h => h.bound)
    (fun _ _ h => h.index name.region) (fun _ _ h hk => slash_scan_iteration name h hk)

/-- The whole slash scan of a nonempty slash-free name, as one register post. -/
theorem slash_scan (c : Config) (p ra a0 : BitVec 64) (len : Nat) (name : PlainName c.σ.mem p len)
    (leaf : LeafInput ra c) (regs : GHolds c.σ [(14, p), (15, nameByteWord (imgM c.σ.mem (p.toNat + 0))),
      (13, 47#64), (10, a0)]) :
    FnSummary 0x8002543c#64 (fun d => d = c)
      (RegistersPost [14, 15] c.σ.mem c 0x8002546c#64 a0
        [(14, nameCursor p len), (15, 0#64), (13, 47#64), (10, a0)]) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have start : SlashScanAt p len 0 ra a0 c c :=
    { leaf := leaf
      bound := Nat.zero_le _
      pc := by simpa only [if_pos name.positive] using pc
      cursor := by
        change gprGet c.σ 14 = some (p + 0#64)
        rw [BitVec.add_zero]; exact regs.1
      current := regs.2.1
      slash := regs.2.2.1
      value := regs.2.2.2.1
      memory := rfl
      output := rfl
      frame := fun _ _ _ => rfl }
  obtain ⟨after, run, post⟩ := slash_scan_loop c name c start
  have zero : nameByteWord (imgM c.σ.mem (p.toNat + len)) = 0#64 := by rw [name.bytes.nul]; rfl
  refine ⟨after, run, ⟨⟨post.leaf.good, post.leaf.image, post.leaf.minstret, post.leaf.tick, ?_, post.value,
    post.memory, post.output, post.frame⟩, ⟨post.cursor, ?_, post.slash, post.value, trivial⟩⟩⟩
  · change PCAt _ after
    simpa only [Nat.lt_irrefl, ite_false] using post.pc
  · rw [← zero]; exact post.current
end OCaml.Vm.Boot.Startup
