import OCaml.Vm.Primitives.StringScan
import OCaml.Vm.Primitives.ScanArithmetic
import Vsa.Sim.DeriveLoop

namespace OCaml.Vm.Primitives.StringScan
open Vsa.Machine Vsa.Sim LeanRV64DExecutable Vsa.Logic

def scanWrites : List Nat := [10, 11, 13, 14, 15]
def scanHead : BitVec 64 := BitVec.ofNat 64 (Layout.sym_caml_string_equal + 52)
def equalExit : BitVec 64 := BitVec.ofNat 64 (Layout.sym_caml_string_equal + 84)
def differentExit : BitVec 64 := BitVec.ofNat 64 (Layout.sym_caml_string_equal + 72)
def loopRegs (ra : BitVec 64) (a b n i : Nat) : GRegs :=
  [(1, ra), (10, scanPtr a i), (11, BitVec.ofNat 64 b - BitVec.ofNat 64 a), (15, scanPtr a n)]
def equalWord (before : Config) (a b i : Nat) : Prop :=
  word before (a + 8 * i) = word before (b + 8 * i)

/-- The scan either has a verified equal prefix, or has reached one of its
fixed exit labels with the corresponding word-comparison result. -/
inductive ScanInvariant (before : Config) (ra : BitVec 64) (a b n : Nat) : Config → Prop
  | scanning {c i} (bound : i < n)
      (boundary : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n i) c)
      (prefixEqual : ∀ j, j < i → equalWord before a b j) : ScanInvariant before ra a b n c
  | equal {c} (boundary : BoundaryPost scanWrites before ra equalExit [(1, ra)] c)
      (allEqual : ∀ j, j < n → equalWord before a b j) : ScanInvariant before ra a b n c
  | different {c} (boundary : BoundaryPost scanWrites before ra differentExit [(1, ra)] c)
      (witness : ∃ j, j < n ∧ ¬ equalWord before a b j) : ScanInvariant before ra a b n c

def scanMeasure (a n : Nat) (c : Config) : Nat :=
  if pcOf c = some scanHead then n - (((gpr c 10).getD 0).toNat - a) / 8 else 0

theorem measure_scanning {before ra a b n c i}
    (range : WordRange a n) (hi : i ≤ n)
    (h : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n i) c) :
    scanMeasure a n c = n - i := by
  have hr : gpr c 10 = some (scanPtr a i) := gholds_lookup _ h.regs rfl
  simp only [scanMeasure, h.pc, ite_true, hr, Option.getD_some, range.ptr_nat hi]
  omega

theorem measure_equal {before ra a n c}
    (h : BoundaryPost scanWrites before ra equalExit [(1, ra)] c) : scanMeasure a n c = 0 := by
  simp only [scanMeasure, h.pc, show some equalExit ≠ some scanHead from by decide, ite_false]

theorem measure_different {before ra a n c}
    (h : BoundaryPost scanWrites before ra differentExit [(1, ra)] c) : scanMeasure a n c = 0 := by
  simp only [scanMeasure, h.pc, show some differentExit ≠ some scanHead from by decide, ite_false]

/-- One generated word-comparison iteration, including its loop-end test. -/
theorem scan_iteration {before ra a b n c i}
    (wa : WordRange a n) (wb : WordRange b n) (hi : i < n)
    (h : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n i) c)
    (equalPrefix : ∀ j, j < i → equalWord before a b j) :
    FnSummary scanHead (fun d => d = c)
      (fun d => ScanInvariant before ra a b n d ∧ scanMeasure a n d < n - i) := by
  let x := scanPtr a i
  let delta := BitVec.ofNat 64 b - BitVec.ofNat 64 a
  let limit := scanPtr a n
  let bs0 := read8 c.σ.mem (a + 8 * i)
  let bs1 := read8 c.σ.mem (b + 8 * i)
  have v0 : bytesVal .ld bs0 = word before (a + 8 * i) := by
    rw [read8_value]; simp only [word, h.memory]
  have v1 : bytesVal .ld bs1 = word before (b + 8 * i) := by
    rw [read8_value]; simp only [word, h.memory]
  have window0 : ReadWindow (x + 0#64) 8 := by simpa [x, Sail.BitVec.addInt] using wa.window hi
  have window1 : ReadWindow ((x + delta) + 0#64) 8 := by
    simpa [x, delta, Sail.BitVec.addInt, scanPtr_delta] using wb.window hi
  have pins0 : LPins8 c.σ.mem (x + 0#64).toNat bs0 := by
    simpa [x, bs0, Sail.BitVec.addInt, wa.ptr_nat (Nat.le_of_lt hi)] using read8_pins c.σ.mem (a + 8 * i)
  have pins1 : LPins8 c.σ.mem ((x + delta) + 0#64).toNat bs1 := by
    simpa [x, delta, bs1, scanPtr_delta, Sail.BitVec.addInt, wb.ptr_nat (Nat.le_of_lt hi)] using read8_pins c.σ.mem (b + 8 * i)
  by_cases same : equalWord before a b i
  · have branch : guardB bop.BEQ (bytesVal .ld bs0) (bytesVal .ld bs1) = true := by
      simpa only [guardB, v0, v1, beq_iff_eq, equalWord] using same
    have S := b34_summary c ra x delta limit bs0 bs1 true h.toLeafInput h.regs window0 pins0 window1 pins1 branch
    apply boundary_bind S
    intro d post
    have hd := h.then post
    have regs : GHolds d.σ (loopRegs ra a b n (i + 1)) := by
      apply holds_select post.regs
      intro r v hv
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hv | hv | hv | hv <;> cases hv <;>
        simp [b34_regs, lookupG, x, delta, limit, scanPtr_succ]
    have pref : ∀ j, j < i + 1 → equalWord before a b j := by
      intro j hj
      by_cases hj' : j < i
      · exact equalPrefix j hj'
      · have he : j = i := by omega
        simpa only [he] using same
    by_cases last : i + 1 = n
    · have branchEnd : guardB bop.BEQ (scanPtr a (i + 1)) limit = true := by simp [guardB, limit, last]
      have T := b30_summary d ra (scanPtr a (i + 1)) delta limit true post.toLeafInput regs branchEnd
      apply T.weaken (fun _ he => he)
      intro e ep
      have done := (hd.then ep).select (target := [(1, ra)]) (by simp [b30_regs, lookupG])
      exact ⟨.equal done (by simpa only [last] using pref), by rw [measure_equal done]; omega⟩
    · have branchMore : guardB bop.BEQ (scanPtr a (i + 1)) limit = false := by
        have ne : scanPtr a (i + 1) ≠ scanPtr a n := fun he => last ((wa.ptr_eq_limit (by omega)).mp he)
        simp [guardB, limit, ne]
      have T := b30_summary d ra (scanPtr a (i + 1)) delta limit false post.toLeafInput regs branchMore
      apply T.weaken (fun _ he => he)
      intro e ep
      have more : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n (i + 1)) e := hd.then ep
      exact ⟨.scanning (by omega) more pref, by rw [measure_scanning wa (by omega) more]; omega⟩
  · have branch : guardB bop.BEQ (bytesVal .ld bs0) (bytesVal .ld bs1) = false := by
      simpa only [guardB, v0, v1, beq_eq_false_iff_ne, equalWord] using same
    have S := b34_summary c ra x delta limit bs0 bs1 false h.toLeafInput h.regs window0 pins0 window1 pins1 branch
    apply S.weaken (fun _ he => he)
    intro d post
    have done := (h.then post).select (target := [(1, ra)]) (by simp [b34_regs, lookupG])
    exact ⟨.different done ⟨i, hi, same⟩, by rw [measure_different done]; omega⟩

/-- Fold the generated back edge using the existing total-correctness loop rule. -/
theorem scan_loop {before ra a b n c i}
    (wa : WordRange a n) (wb : WordRange b n) (hi : i < n)
    (h : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n i) c)
    (equalPrefix : ∀ j, j < i → equalWord before a b j) :
    FnSummary scanHead (fun d => d = c)
      (fun d => ScanInvariant before ra a b n d ∧ pcOf d ≠ some scanHead) := by
  have body : ∀ fuel, Triple
      (fun d => ScanInvariant before ra a b n d ∧ pcOf d = some scanHead ∧ scanMeasure a n d = fuel)
      (fun d => ScanInvariant before ra a b n d ∧ scanMeasure a n d < fuel) := by
    intro fuel d pre
    obtain ⟨inv, head, measure⟩ := pre
    cases inv with
    | scanning bound boundary pref =>
      have S := scan_iteration wa wb bound boundary pref
      rw [measure_scanning wa (Nat.le_of_lt bound) boundary] at measure
      subst fuel
      exact S.run d ⟨boundary.pc, rfl⟩
    | equal boundary _ =>
      have bad : some equalExit = some scanHead := boundary.pc.symm.trans head
      exact False.elim ((by decide : some equalExit ≠ some scanHead) bad)
    | different boundary _ =>
      have bad : some differentExit = some scanHead := boundary.pc.symm.trans head
      exact False.elim ((by decide : some differentExit ≠ some scanHead) bad)
  constructor
  rintro d ⟨_, rfl⟩
  exact loopFromBody (scanMeasure a n) body d (.scanning hi h equalPrefix)

noncomputable def scanValue (before : Config) (a b n : Nat) : BitVec 64 :=
  by classical exact if ∀ j, j < n → equalWord before a b j then 3#64 else 1#64

/-- Fold the fixed success/failure epilogues after the scan has stopped. -/
theorem scan_finish {before ra a b n} : Triple
    (fun c => ScanInvariant before ra a b n c ∧ pcOf c ≠ some scanHead)
    (RegisterPost scanWrites before ra (scanValue before a b n)) := by
  intro c pre
  obtain ⟨inv, stopped⟩ := pre
  cases inv with
  | scanning _ boundary _ => exact False.elim (stopped boundary.pc)
  | equal boundary allEqual =>
    have S := b54_summary c ra boundary.toLeafInput boundary.regs
    have T : FnSummary equalExit (fun d => d = c)
        (RegisterPost scanWrites before ra (scanValue before a b n)) :=
      S.weaken (fun _ he => he) (fun d post => by
      have result := (boundary.then post).finish (value := 3#64) rfl
      simpa only [scanValue, if_pos allEqual] using result)
    exact T.run c ⟨boundary.pc, rfl⟩
  | different boundary witness =>
    have notAll : ¬ ∀ j, j < n → equalWord before a b j := by
      obtain ⟨j, hj, bad⟩ := witness
      exact fun all => bad (all j hj)
    have S := b48_summary c ra boundary.toLeafInput boundary.regs
    have T : FnSummary differentExit (fun d => d = c)
        (RegisterPost scanWrites before ra (scanValue before a b n)) := by
      apply boundary_bind S
      intro d post
      have regs : GHolds d.σ [(1, ra), (13, 1#64)] :=
        ⟨post.raReg, gholds_lookup _ post.regs rfl, True.intro⟩
      have U := b4c_summary d ra 1#64 post.toLeafInput regs
      apply U.weaken (fun _ he => he)
      intro e ep
      have result := ((boundary.then post).then ep).finish (value := 1#64) rfl
      simpa only [scanValue, if_neg notAll] using result
    exact T.run c ⟨boundary.pc, rfl⟩

/-- The whole word loop, with a complete caller frame and its exact result. -/
theorem scan_words {before ra a b n c i}
    (wa : WordRange a n) (wb : WordRange b n) (hi : i < n)
    (h : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n i) c)
    (equalPrefix : ∀ j, j < i → equalWord before a b j) :
    FnSummary scanHead (fun d => d = c)
      (RegisterPost scanWrites before ra (scanValue before a b n)) :=
  ⟨Triple.seq (scan_loop wa wb hi h equalPrefix).run scan_finish⟩

end OCaml.Vm.Primitives.StringScan
