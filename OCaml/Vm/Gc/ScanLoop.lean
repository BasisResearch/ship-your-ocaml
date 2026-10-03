import OCaml.Vm.Gc.ScanGeometry
import Vsa.Sim.DeriveLoop

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- Loop-head or exhausted-scan state. Only the destination suffix can change;
all copied words equal their source observations at the initial scan boundary. -/
structure ScanAt (a b count start : Nat) (initial : Config) (i : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  lower : start ≤ i
  upper : i ≤ count
  pc : PCAt (if i < count then FieldCopy.pc else exitPc) c
  registers : GHolds c.σ (regs (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
    (BitVec.ofNat 64 b) (BitVec.ofNat 64 i))
  memory : FrameOn (scanWindow b start count) initial.σ.mem c.σ.mem
  copied : ∀ j, start ≤ j → j < i → word c (b + 8 * j) = word initial (a + 8 * j)
  output : c.σ.sailOutput = initial.σ.sailOutput
  native : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [8, 9, 10, 11, 15], (gprReg n == r) = false) →
      c.σ.regs.get? r = initial.σ.regs.get? r

def scanIndex (c : Config) : Nat := ((gprGet c.σ 9).getD 0).toNat

theorem ScanAt.index_eq {a b count start initial i c} (h : ScanAt a b count start initial i c)
    (geometry : Geometry a b count) : scanIndex c = i := by
  have reg : gprGet c.σ 9 = some (BitVec.ofNat 64 i) := gholds_lookup _ h.registers rfl
  have upper := geometry.targetRange.upper
  have bound := h.upper
  simp only [scanIndex, reg, Option.getD_some, BitVec.toNat_ofNat]
  omega

/-- One concrete immediate-field iteration preserves the scan invariant. -/
theorem scan_iteration {a b count start initial i c}
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (immediates : ∀ j, start ≤ j → j < count →
      guardB .BNE (word initial (a + 8 * j) &&& 1#64) 0 = true)
    (h : ScanAt a b count start initial i c) (bound : i < count) :
    ∃ d, Steps c d ∧ ScanAt a b count start initial (i + 1) d := by
  let slot := scanPtr a i
  let delta := BitVec.ofNat 64 b - BitVec.ofNat 64 a
  let target := BitVec.ofNat 64 b
  let index := BitVec.ofNat 64 i
  have source : word c (a + 8 * i) = word initial (a + 8 * i) := by
    apply word_frame h.memory
    have separate := geometry.separate
    omega
  have sameHeader : word c (b - 8) = word initial (b - 8) := by
    apply word_frame h.memory
    exact Or.inl (by have lower := geometry.targetRange.lower; omega)
  have input : Input slot delta target index c :=
    ⟨h.good, h.minstret, h.registers, h.tick, h.code, geometry.windows bound, by
      change guardB .BNE (word c (scanPtr a i).toNat &&& 1#64) 0 = true
      rw [geometry.sourceRange.ptr_nat (Nat.le_of_lt bound), source]
      exact immediates i h.lower bound⟩
  obtain ⟨d, run, post⟩ := (copy_machine input).run c ⟨by simpa [bound] using h.pc, rfl⟩
  have log : copyLog slot delta c = [(b + 8 * i, 8, word c (a + 8 * i))] := by
    simp only [copyLog, slot, delta, BitVec.add_comm _ (scanPtr a i), scanPtr_delta,
      geometry.targetRange.ptr_nat (Nat.le_of_lt bound), geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)]
  have memory : d.σ.mem = writeLog c.σ.mem [(b + 8 * i, 8, word c (a + 8 * i))] := by
    rw [post.memory, log]
  have frame : FrameOn (scanWindow b start count) c.σ.mem d.σ.mem := by
    rw [memory]
    apply frameOn_writeLog
    change ((b + 8 * start ≤ b + 8 * i ∧ b + 8 * i + 8 ≤ b + 8 * count) ∨ False) ∧ True
    exact ⟨Or.inl ⟨by have := h.lower; omega, by omega⟩, True.intro⟩
  refine ⟨d, run, ⟨post.machine.good, post.machine.minstret, post.machine.tick,
    post.code input, by have := h.lower; omega, by omega, ?_, ?_,
    (fun a ha => (frame a ha).trans (h.memory a ha)), ?_,
    post.machine.output.trans h.output, ?_⟩⟩
  · have next := post.pc
    rw [again_eq geometry bound (sameHeader ▸ header)] at next
    simpa only [decide_eq_true_eq] using next
  · simpa only [slot, delta, target, index, scanPtr_succ, BitVec.ofNat_add] using post.scan_regs
  · intro j lower lt
    by_cases current : j = i
    · subst j
      have copied := post.destination
      simpa only [slot, delta, BitVec.add_comm _ (scanPtr a i), scanPtr_delta,
        geometry.targetRange.ptr_nat (Nat.le_of_lt bound),
        geometry.sourceRange.ptr_nat (Nat.le_of_lt bound), source] using copied
    · have old : j < i := by omega
      have unchanged : word d (b + 8 * j) = word c (b + 8 * j) := by
        change bytesT d.σ.mem _ 8 = bytesT c.σ.mem _ 8
        rw [memory]
        apply bytesT_writeLog_out
        exact ⟨Or.inl (by omega), True.intro⟩
      exact unchanged.trans (h.copied j lower old)
  · intro r noise notWritten
    exact (post.machine.frame r noise (fun n hn => notWritten n (written _ n hn))).trans
      (h.native r noise notWritten)

/-- Fold the actual immediate-valued field scan with the standard decreasing
counter rule. Pointer fields still require the oldify call path. -/
theorem scan_loop {a b count start initial}
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (immediates : ∀ j, start ≤ j → j < count →
      guardB .BNE (word initial (a + 8 * j) &&& 1#64) 0 = true) :
    Triple (ScanAt a b count start initial start) (ScanAt a b count start initial count) := by
  let I := fun c => ScanAt a b count start initial (scanIndex c) c
  let B := fun c => scanIndex c < count
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ count - scanIndex c = n)
      (fun c => I c ∧ count - scanIndex c < n) := by
    intro n c ⟨h, lt, rank⟩
    obtain ⟨d, run, post⟩ := scan_iteration geometry header immediates h lt
    have index := post.index_eq geometry
    refine ⟨d, run, ?_, ?_⟩
    · change ScanAt a b count start initial (scanIndex d) d
      rw [index]; exact post
    · rw [index]; dsimp [B] at lt; omega
  apply (loopFromBody (fun c => count - scanIndex c) body).conseq
  · intro c h
    change ScanAt a b count start initial (scanIndex c) c
    rw [h.index_eq geometry]; exact h
  · intro c ⟨h, stop⟩
    have bound := h.upper
    have eq : scanIndex c = count := by dsimp [B] at stop; omega
    simpa only [I, eq] using h

end OCaml.Vm.Gc.FieldCopy
