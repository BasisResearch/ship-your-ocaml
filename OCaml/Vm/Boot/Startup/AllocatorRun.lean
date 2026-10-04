import OCaml.Vm.Boot.Startup.MallocRun
import VsaIris.Vsa.MallocRunAll
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open VsaIris.MallocFast OCaml.Vm.Primitives

/-- Recover any allocator-preserved ABI register from the shared return frame. -/
theorem allocator_saved_register {before after : Config} {r s : BitVec 64}
    (pre : VsaOk startupLive before) (post : VsaOk startupLive after)
    (frame : RetFrame ((vsaModel startupLive).reg after) r s (firstMallocSaved (vsaReg before)))
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
structure AllocatorInput (H : List (Nat × Nat)) (n r s : BitVec 64) (capacity : Nat)
    (c : Config) : Prop where
  good : VsaOk startupLive c
  readOnly : ROHolds (vsaModel startupLive) c roR allocText
  room : vsaRoomB ((vsaModel startupLive).mem c) H capacity
  request : gprGet c.σ 10 = some n
  stack : gprGet c.σ 2 = some s
  link : gprGet c.σ 1 = some r
  stackOk : SpOKA s
  high : heapEnd + allocHeadroom ≤ s.toNat
  aligned : r.toNat % 4 = 0

/-- Reusable successful malloc summary for every later startup allocation.
The library charges its request, and the run kernel folds its certificate. -/
theorem allocator_summary (c : Config) (H : List (Nat × Nat)) (n r s : BitVec 64)
    (k charge : Nat) (input : AllocatorInput H n r s (k + charge) c)
    (charged : vsaChg n.toNat charge) :
    FnSummary mallocEntryBV (fun d => d = c)
      (LocalPost startupLive roR allocText aRegs (mS H s)
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
  obtain ⟨fuel, certificate⟩ := mallocChgRun_proved startupLive startup_alloc_live
    H n s r (firstMallocSaved (vsaReg c)) (vsaReg c) ((vsaModel startupLive).mem c) k charge
    (firstMallocSaved_keys _) charged input.stackOk input.aligned entry
    (room_shape input.room) input.room (allocator_stack_disjoint H s input.high)
  exact localRun_triple c (allocator_separate H s input.high) input.good input.readOnly certificate c rfl
end OCaml.Vm.Boot.Startup
