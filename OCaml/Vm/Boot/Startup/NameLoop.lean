import OCaml.Vm.Boot.Startup.NameData
import OCaml.Vm.Boot.Startup.IndexedLoop
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic LeanRV64DExecutable OCaml.Vm.Primitives

def nameScanIndex (p : BitVec 64) (c : Config) : Nat := ((gprGet c.σ 12).getD 0).toNat - p.toNat

def nameEndRegs : GRegs := [(14, 0#64), (15, -61#64)]

structure NameScanAt (p : BitVec 64) (count k : Nat) (ra value : BitVec 64) (initial c : Config) : Prop where
  leaf : LeafInput ra c
  bound : k ≤ count
  pc : PCAt (if k < count then 0x80037490#64 else 0x800374a8#64) c
  valueReg : gprGet c.σ 10 = some value
  cursorReg : gprGet c.σ 12 = some (nameCursor p k)
  endRegs : k = count → GHolds c.σ nameEndRegs
  memory : c.σ.mem = initial.σ.mem
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [14, 12, 15], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = initial.σ.regs.get? r

theorem NameScanAt.index {p count k ra value initial c} (region : ReadWindow p (count + 1))
    (h : NameScanAt p count k ra value initial c) : nameScanIndex p c = k := by
  simp only [nameScanIndex, h.cursorReg, Option.getD_some, nameCursor_nat region h.bound]
  omega

/-- A C-string byte certificate supplies each native scan branch and load. -/
theorem name_scan_iteration {p cs k ra value initial c} (data : EnvName p cs initial)
    (h : NameScanAt p cs.length k ra value initial c) (hk : k < cs.length) :
    ∃ d, Steps c d ∧ NameScanAt p cs.length (k + 1) ra value initial d := by
  obtain ⟨b, next⟩ := data.byte (k := k + 1) (by omega)
  have input : NameStepInput (nameCursor p k) value ra b (decide (k + 1 = cs.length)) c := {
    toLeafInput := h.leaf
    cursorReg := h.cursorReg
    valueReg := h.valueReg
    window := by rw [nameCursor_next]; exact name_window data.region (by omega)
    pin := by rw [h.memory, nameCursor_next, nameCursor_nat data.region (by omega)]; exact next.pin
    zero := by simpa only [decide_eq_true_eq] using next.zero
    notEquals := next.notEquals }
  have pc : PCAt 0x80037490#64 c := by simpa only [ite_true, hk] using h.pc
  obtain ⟨d, run, post⟩ := (name_step c _ _ _ _ _ input).run c ⟨pc, rfl⟩
  refine ⟨d, run, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
    bound := by omega
    pc := ?_
    valueReg := post.result
    cursorReg := ?_
    endRegs := ?_
    memory := post.memory.trans h.memory
    output := post.output.trans h.output
    frame := fun r outside noise => (post.frame r outside noise).trans (h.frame r outside noise) }⟩
  · change pcOf d = some _
    by_cases last : k + 1 = cs.length
    · simpa [last] using post.pc
    · have less : k + 1 < cs.length := by omega
      simpa [last, less] using post.pc
  · have cursor := gholds_lookup (n := 12) _ post.regs (by rfl)
    rw [nameCursor_next] at cursor
    exact cursor
  · intro last
    have zero := next.zero.mpr last
    have b14 := gholds_lookup (n := 14) _ post.regs (by rfl)
    have b15 := gholds_lookup (n := 15) _ post.regs (by rfl)
    rw [zero] at b14 b15
    refine ⟨?_, ?_, trivial⟩
    · simpa only [show nameByteWord 0#8 = 0#64 from rfl] using b14
    · simpa only [show nameSignedByte 0#8 = 0#64 from rfl, BitVec.zero_add] using b15

/-- Fold the native name scan using its cursor rank, independent of name length. -/
theorem name_scan_loop {p cs ra value} (initial : Config) (data : EnvName p cs initial) :
    Triple (NameScanAt p cs.length 0 ra value initial) (NameScanAt p cs.length cs.length ra value initial) :=
  indexed_loop (nameScanIndex p) cs.length 0 _ (fun _ _ h => h.bound)
    (fun _ _ h => h.index data.region) (fun _ _ h hk => name_scan_iteration data h hk)

/-- Scan a nonempty environment-variable name to its terminating zero. The
native loop is folded by its cursor; no name-length execution is evaluated. -/
theorem name_scan (c : Config) (p ra value : BitVec 64) (cs : List Char)
    (data : EnvName p cs c) (positive : 0 < cs.length) (leaf : LeafInput ra c)
    (cursor : gprGet c.σ 12 = some p) (argument : gprGet c.σ 10 = some value) :
    FnSummary 0x80037490#64 (fun d => d = c)
      (RegistersPost [14, 12, 15] c.σ.mem c 0x800374a8#64 value
        (nameEndRegs ++ [(12, nameCursor p cs.length), (10, value)])) := by
  constructor
  intro before input
  obtain ⟨pc, eq⟩ := input
  subst before
  have start : NameScanAt p cs.length 0 ra value c c := {
    leaf := leaf
    bound := Nat.zero_le _
    pc := by simpa only [if_pos positive] using pc
    valueReg := argument
    cursorReg := by
      change gprGet c.σ 12 = some (p + 0#64)
      simpa only [BitVec.add_zero] using cursor
    endRegs := fun impossible => by omega
    memory := rfl
    output := rfl
    frame := fun _ _ _ => rfl }
  obtain ⟨after, run, post⟩ := name_scan_loop c data c start
  refine ⟨after, run, ⟨⟨post.leaf.good, post.leaf.image, post.leaf.minstret,
    post.leaf.tick, ?_, post.valueReg, post.memory, post.output, post.frame⟩, ?_⟩⟩
  · change PCAt _ after
    simpa only [Nat.lt_irrefl, ite_false] using post.pc
  · obtain ⟨last14, last15, _⟩ := post.endRegs rfl
    exact ⟨last14, last15, post.cursorReg, post.valueReg, trivial⟩
end OCaml.Vm.Boot.Startup
