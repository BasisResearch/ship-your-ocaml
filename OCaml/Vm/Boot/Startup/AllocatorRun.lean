import OCaml.Vm.Boot.Startup.LibraryLive
import OCaml.Vm.Boot.Startup.MallocRun
import VsaIris.Vsa.MallocRunAll
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
variable {live : Nat → Prop}
open VsaIris.MallocFast OCaml.Vm.Primitives

/-- The RISC-V callee-saved integer registers s0–s11. -/
def abiSaved : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem abiSaved_of_vsaSaved {k : Nat} (member : k ∈ vsaSaved) : k ∈ abiSaved := by
  simp [vsaSaved, abiSaved] at member ⊢; omega

/-- Recover any allocator-preserved ABI register from the shared return frame. -/
theorem allocator_saved_register {before after : Config} {r s : BitVec 64}
    (pre : VsaOk live before) (post : VsaOk live after)
    (frame : RetFrame ((vsaModel live).reg after) r s (firstMallocSaved (vsaReg before)))
    (n : Nat) (member : n ∈ vsaSaved) : gprGet after.σ n = gprGet before.σ n := by
  have range : 1 ≤ n ∧ n ≤ 31 := by simp [vsaSaved] at member; omega
  have saved := frame.saved (n, vsaReg before n) (by
    change (n, vsaReg before n) ∈ vsaSaved.map (fun k => (k, vsaReg before k))
    exact List.mem_map.mpr ⟨n, member, rfl⟩)
  exact library_register_frame pre post range.1 range.2 saved

/-- Remaining-capacity certificates include the ordinary allocator shape. -/
theorem room_shape {mv H k} (h : vsaRoomB mv H k) : vsaLayoutP.Shape mv H := by
  obtain ⟨starts, m, top, brkv, chunks, bins, image, heap, _⟩ := h
  exact ⟨starts, m, top, brkv, chunks, bins, image, heap⟩

/-- Startup stacks above the heap keep all allocator read-only pins separate. -/
theorem allocator_separate (H : List (Nat × Nat)) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) :
    LocalSeparation roR allocText aRegs (mS H s) where
  registers := by decide
  bytes := by
    intro p hp owned
    have bounds := (allocator_sources p hp).geometry
    change stackWin s allocHeadroom p.1 ∨ vsaFoot H p.1 at owned
    rcases owned with stack | global | heap
    · have upper := bounds.high
      unfold stackWin InExt at stack
      have order : heapStart < heapEnd := by decide
      omega
    · exact bounds.outsideGlobals global
    · exact Nat.not_le_of_lt bounds.high heap.1

theorem allocator_stack_disjoint (H : List (Nat × Nat)) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) :
    ∀ a, stackWin s allocHeadroom a → ¬ vsaFoot H a := by
  intro a stack heap
  unfold stackWin InExt at stack
  unfold vsaFoot allocGlobal InRange heapStart heapEnd allocHeadroom at *
  omega

/-- Concrete startup observations and capacity instantiate the landed allocator
contract. No initialized-heap execution or success is assumed. -/
structure AllocatorInputL (live : Nat → Prop) (H : List (Nat × Nat)) (n r s : BitVec 64) (capacity : Nat)
    (c : Config) : Prop where
  good : VsaOk live c
  readOnly : ROHolds (vsaModel live) c roR allocText
  room : vsaRoomB ((vsaModel live).mem c) H capacity
  request : gprGet c.σ 10 = some n
  stack : gprGet c.σ 2 = some s
  link : gprGet c.σ 1 = some r
  stackOk : SpOKA s
  high : heapEnd + allocHeadroom ≤ s.toNat
  aligned : r.toNat % 4 = 0

abbrev AllocatorInput (H : List (Nat × Nat)) (n r s : BitVec 64) (capacity : Nat) (c : Config) : Prop :=
  AllocatorInputL startupLive H n r s capacity c

/-- Reusable successful malloc summary for every later startup allocation.
The library charges its request, and the run kernel folds its certificate. -/
theorem allocator_summary [LibraryLive live] (c : Config) (H : List (Nat × Nat)) (n r s : BitVec 64)
    (k charge : Nat) (input : AllocatorInputL live H n r s (k + charge) c)
    (charged : vsaChg n.toNat charge) :
    FnSummary mallocEntryBV (fun d => d = c)
      (LocalPost live roR allocText aRegs (mS H s)
        (MallocRoomEnd vsaLayoutP vsaRoomB H n r s (firstMallocSaved (vsaReg c)) k) c) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have entry : EntryRegs (vsaReg c) mallocEntryBV r n s (firstMallocSaved (vsaReg c)) := by
    constructor
    · change (c.σ.regs.get? .PC).getD 0 = _
      rw [pc]; rfl
    · change (gprGet c.σ 1).getD 0 = _
      rw [input.link]; rfl
    · change (gprGet c.σ 10).getD 0 = _
      rw [input.request]; rfl
    · change (gprGet c.σ 2).getD 0 = _
      rw [input.stack]; rfl
    · exact firstMallocSaved_values _
  obtain ⟨fuel, certificate⟩ := mallocChgRun_proved live LibraryLive.alloc
    H n s r (firstMallocSaved (vsaReg c)) (vsaReg c) ((vsaModel live).mem c) k charge
    (firstMallocSaved_keys _) charged input.stackOk input.aligned entry
    (room_shape input.room) input.room (allocator_stack_disjoint H s input.high)
  exact localRun_triple c (allocator_separate H s input.high) input.good input.readOnly certificate c rfl
/-- The allocator keeps every callee-saved register: s0–s3 through its return
frame, s4–s11 because it never writes them. -/
theorem allocator_abi_register {before after : Config} {r s : BitVec 64}
    (pre : VsaOk live before) (post : VsaOk live after)
    (frame : RetFrame ((vsaModel live).reg after) r s (firstMallocSaved (vsaReg before)))
    (registers : ∀ k, k ∉ aRegs → (vsaModel live).reg after k = (vsaModel live).reg before k)
    (n : Nat) (member : n ∈ abiSaved) : gprGet after.σ n = gprGet before.σ n := by
  by_cases saved : n ∈ vsaSaved
  · exact allocator_saved_register pre post frame n saved
  · have range : 1 ≤ n ∧ n ≤ 31 := by simp [abiSaved] at member; omega
    exact library_register_frame pre post range.1 range.2 (registers n (by
      simp [vsaSaved] at saved; simp [abiSaved] at member; simp [aRegs]; omega))
end OCaml.Vm.Boot.Startup
