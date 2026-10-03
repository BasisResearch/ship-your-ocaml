import OCaml.Vm.Boot.Startup.LookupHead
import OCaml.Vm.Boot.Startup.LookupIndex
import Vsa.Sim.DeriveLoop

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives

/-- Read-only name-table facts, to be supplied by the runtime image and loaded PRIM
section. No execution or per-comparison trace is assumed. -/
structure NameTable (required base : BitVec 64) (name : String)
    (pointers : Nat → BitVec 64) (names : Nat → String) (target : Nat) (m : Mem) : Prop where
  bound : target < 2^31
  strings : ∀ k, k ≤ target → NameMemory required (pointers k) name (names k) m
  nonnull : ∀ k, k ≤ target → pointers k ≠ 0#64
  matchAt : name = names target
  before : ∀ k, k < target → name ≠ names k
  window : ∀ k, k < target → ReadWindow (nextLookupAddress (BitVec.ofNat 64 k) base) 8
  next : ∀ k, k < target → bytesVal .ld
    (read8 m (nextLookupAddress (BitVec.ofNat 64 k) base).toNat) = pointers (k + 1)

structure LookupAt (required base : BitVec 64) (pointers : Nat → BitVec 64)
    (target k : Nat) (initial c : Config) : Prop where
  ready : LookupReady c
  bound : k ≤ target
  pc : PCAt 0x80024e30#64 c
  index : gprGet c.σ 8 = some (BitVec.ofNat 64 k)
  requiredReg : gprGet c.σ 9 = some required
  baseReg : gprGet c.σ 18 = some base
  candidate : gprGet c.σ 11 = some (pointers k)
  memory : c.σ.mem = initial.σ.mem
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r, NotWrittenStrcmp r → r ≠ .x1 → r ≠ .x8 →
    c.σ.regs.get? r = initial.σ.regs.get? r

def lookupIndex (c : Config) : Nat := ((gprGet c.σ 8).getD 0).toNat

theorem LookupAt.index_eq {required base pointers target k initial c}
    (h : LookupAt required base pointers target k initial c) (bound : target < 2^31) :
    lookupIndex c = k := by
  simp only [lookupIndex, h.index, Option.getD_some]
  exact lookupIndex_nat k (by have := h.bound; omega)

/-- A failed comparison followed by the actual index/load back edge. -/
theorem lookup_iteration {required base name pointers names target k initial c}
    (table : NameTable required base name pointers names target initial.σ.mem)
    (h : LookupAt required base pointers target k initial c) (lt : k < target) :
    ∃ d, Steps c d ∧ LookupAt required base pointers target (k + 1) initial d := by
  have strings : NameMemory required (pointers k) name (names k) c.σ.mem := by
    rw [h.memory]; exact table.strings k h.bound
  obtain ⟨mid, front, cmp⟩ := (lookup_head c required (pointers k) name (names k)
    h.ready strings h.requiredReg h.candidate).run c ⟨h.pc, rfl⟩
  have mi : gprGet mid.σ 8 = some (BitVec.ofNat 64 k) :=
    (cmp.frame .x8 (by decide) (by decide)).trans h.index
  have mb : gprGet mid.σ 18 = some base :=
    (cmp.frame .x18 (by decide) (by decide)).trans h.baseReg
  have mm : mid.σ.mem = initial.σ.mem := cmp.memory.trans h.memory
  let bytes := read8 mid.σ.mem (nextLookupAddress (BitVec.ofNat 64 k) base).toNat
  have value : bytesVal .ld bytes = pointers (k + 1) := by
    dsimp [bytes]; rw [mm]; exact table.next k lt
  have nonnull : bytesVal .ld bytes ≠ 0#64 := by
    rw [value]; exact table.nonnull (k + 1) (by omega)
  obtain ⟨d, back, post⟩ := (lookup_advance mid (BitVec.ofNat 64 k) base bytes
    cmp.ready mi mb (table.window k lt) (read8_pins _ _) nonnull).run mid
      ⟨by simpa [table.before k lt] using cmp.pc, rfl⟩
  refine ⟨d, front.trans back, ⟨post.ready, by omega, post.pc, ?_, ?_, ?_, ?_,
    post.memory.trans mm, post.output.trans (cmp.output.trans h.output), ?_⟩⟩
  · simpa only [nextLookupIndex_nat k (by have := table.bound; omega)] using post.index
  · exact (post.frame .x9 (by decide) (by decide) (by decide) (by decide)).trans
      ((cmp.frame .x9 (by decide) (by decide)).trans h.requiredReg)
  · exact (post.frame .x18 (by decide) (by decide) (by decide) (by decide)).trans mb
  · simpa only [value] using post.candidate
  · intro r hr h1 h8
    have h11 : r ≠ .x11 := by simp_all [NotWrittenStrcmp, beq_eq_false_iff_ne, ne_comm]
    have h15 : r ≠ .x15 := by simp_all [NotWrittenStrcmp, beq_eq_false_iff_ne, ne_comm]
    exact (post.frame r (strcmp_frame_noise hr) h8 h11 h15).trans
      ((cmp.frame r hr h1).trans (h.frame r hr h1 h8))

/-- Fold the scan with a decreasing distance to the first matching name. -/
theorem lookup_loop {required base name pointers names target initial}
    (table : NameTable required base name pointers names target initial.σ.mem) :
    Triple (LookupAt required base pointers target 0 initial)
      (LookupAt required base pointers target target initial) := by
  let I := fun c => LookupAt required base pointers target (lookupIndex c) initial c
  let B := fun c => lookupIndex c < target
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ target - lookupIndex c = n)
      (fun c => I c ∧ target - lookupIndex c < n) := by
    intro n c ⟨h, lt, hn⟩
    obtain ⟨d, run, post⟩ := lookup_iteration table h lt
    have index := post.index_eq table.bound
    refine ⟨d, run, ?_, ?_⟩
    · change LookupAt required base pointers target (lookupIndex d) initial d
      rw [index]; exact post
    · rw [index]; dsimp [B] at lt; omega
  apply (loopFromBody (fun c => target - lookupIndex c) body).conseq
  · intro c h
    change LookupAt required base pointers target (lookupIndex c) initial c
    rw [h.index_eq table.bound]; exact h
  · intro c ⟨h, stop⟩
    have bound := h.bound
    have eq : lookupIndex c = target := by dsimp [B] at stop; omega
    simpa only [I, eq] using h

end OCaml.Vm.Boot.Startup
