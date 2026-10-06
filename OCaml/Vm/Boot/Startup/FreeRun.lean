import OCaml.Vm.Boot.Startup.AllocatorRun
import OCaml.Vm.Boot.Startup.RuntimeMalloc
import OCaml.Vm.Boot.Startup.MallocReturn
import OCaml.Vm.Boot.Startup.TableReturn
import VsaIris.Vsa.FreeRunAll
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
open VsaIris.MallocFast OCaml.Vm.Primitives

/-- What the allocator owns while freeing block `(q, n)`: its scratch stack
window, the heap foot including the block, and the block itself. -/
abbrev fS (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) : Nat → Prop :=
  freeBytes vsaLayoutP H q n s allocHeadroom

theorem free_separate (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) (blockLow : heapStart ≤ q.toNat) :
    LocalSeparation roR allocText aRegs (fS H q n s) where
  registers := by decide
  bytes := by
    intro p hp owned
    have bounds := (allocator_sources p hp).geometry
    change stackWin s allocHeadroom p.1 ∨ (heapFoot vsaLayoutP ((q.toNat, n) :: H) p.1 ∨
      InExt (q.toNat, n) p.1) at owned
    rcases owned with stack | (global | heap) | block
    · have upper := bounds.high
      unfold stackWin InExt at stack
      have order : heapStart < heapEnd := by decide
      omega
    · exact bounds.outsideGlobals global
    · exact Nat.not_le_of_lt bounds.high heap.1
    · unfold InExt at block
      have := bounds.high
      omega

theorem free_stack_disjoint (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64)
    (high : heapEnd + allocHeadroom ≤ s.toNat) (blockHigh : q.toNat + n ≤ heapEnd) :
    ∀ a, stackWin s allocHeadroom a →
      ¬ (heapFoot vsaLayoutP ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a) := by
  intro a stack owned
  unfold stackWin InExt at stack
  rcases owned with (global | heap) | block
  · change allocGlobal a at global
    unfold allocGlobal InRange at global
    unfold heapEnd allocHeadroom at *
    omega
  · have := heap.2.1
    change a < heapEnd at this
    omega
  · unfold InExt at block
    omega

/-- Concrete startup observations for freeing a live block. -/
structure FreeInput (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (r s : BitVec 64) (capacity : Nat)
    (c : Config) : Prop where
  good : VsaOk startupLive c
  readOnly : ROHolds (vsaModel startupLive) c roR allocText
  room : vsaRoomB ((vsaModel startupLive).mem c) ((q.toNat, n) :: H) capacity
  pointer : gprGet c.σ 10 = some q
  stack : gprGet c.σ 2 = some s
  link : gprGet c.σ 1 = some r
  stackOk : SpOKA s
  high : heapEnd + allocHeadroom ≤ s.toNat
  aligned : r.toNat % 4 = 0
  blockLow : heapStart ≤ q.toNat
  blockHigh : q.toNat + n ≤ heapEnd

/-- Reusable successful free summary: the landed `_free_r` capacity run,
entered through the `free` wrapper, folded by the run kernel. -/
theorem free_summary (c : Config) (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (r s : BitVec 64)
    (k : Nat) (input : FreeInput H q n r s k c) :
    FnSummary freeEntryBV (fun d => d = c)
      (LocalPost startupLive roR allocText aRegs (fS H q n s)
        (FreeRoomEnd vsaLayoutP vsaRoomB H r s (firstMallocSaved (vsaReg c)) k) c) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have entry : EntryRegs (vsaReg c) freeEntryBV r q s (firstMallocSaved (vsaReg c)) := by
    constructor
    · change (c.σ.regs.get? .PC).getD 0 = _
      rw [pc]; rfl
    · change (gprGet c.σ 1).getD 0 = _
      rw [input.link]; rfl
    · change (gprGet c.σ 10).getD 0 = _
      rw [input.pointer]; rfl
    · change (gprGet c.σ 2).getD 0 = _
      rw [input.stack]; rfl
    · exact firstMallocSaved_values _
  obtain ⟨fuel, certificate⟩ := freeChgRun_proved startupLive startup_alloc_live
    H q n s r (firstMallocSaved (vsaReg c)) (vsaReg c) ((vsaModel startupLive).mem c) k
    (firstMallocSaved_keys _) input.stackOk input.aligned entry (room_shape input.room) input.room
    (free_stack_disjoint H q n s input.high input.blockHigh)
  exact localRun_triple c (free_separate H q n s input.high input.blockLow) input.good input.readOnly
    certificate c rfl

/-- Everything a free may touch lies in the scratch window, allocator globals
or the arena. -/
theorem fS_coarse {H q n s a} (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd)
    (owned : fS H q n s a) :
    stackWin s allocHeadroom a ∨ allocGlobal a ∨ (heapStart ≤ a ∧ a < heapEnd) := by
  change stackWin s allocHeadroom a ∨ (heapFoot vsaLayoutP ((q.toNat, n) :: H) a ∨
    InExt (q.toNat, n) a) at owned
  rcases owned with stack | (global | heap) | block
  · exact Or.inl stack
  · exact Or.inr (Or.inl global)
  · exact Or.inr (Or.inr ⟨heap.1, heap.2.1⟩)
  · unfold InExt at block
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- A landed successful free contract returns the same runtime interface with
the block removed from the live list and the remaining capacity kept. -/
theorem RuntimeReady.free_result {H q n capacity sp ra before after}
    (ready : RuntimeReady ((q.toNat, n) :: H) capacity sp ra before)
    (high : heapEnd + allocHeadroom ≤ sp.toNat) (blockLow : heapStart ≤ q.toNat)
    (blockHigh : q.toNat + n ≤ heapEnd)
    (post : LocalPost startupLive roR allocText aRegs (fS H q n sp)
      (FreeRoomEnd vsaLayoutP vsaRoomB H ra sp (firstMallocSaved (vsaReg before)) capacity) before after) :
    RuntimeReady H capacity sp ra after where
  good := post.good.good
  image := by
    apply image_local ready.image post.good startup_image_live _ post.memory
    constructor <;> intro i hi owned <;>
      rcases fS_coarse blockLow blockHigh owned with stack | global | heap <;>
      simp only [stackWin, InExt, allocHeadroom, allocGlobal, InRange,
        Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize,
        heapStart, heapEnd] at * <;> omega
  minstret := post.good.good.minstret
  raReg := library_gpr post.good (by decide) (by decide) post.result.frame.ra
  aligned := ready.aligned
  tick := post.good.tick
  platform := post.good
  readOnly := post.readOnly
  room := post.result.room
  stack := library_gpr post.good (by decide) (by decide) post.result.frame.sp
  domainWord := by
    rw [word_observed (m := before.σ.mem) Layout.sym_Caml_state
      (fun i hi => post.memory _ (fun owned => by
        rcases fS_coarse blockLow blockHigh owned with stack | global | heap <;>
          simp only [stackWin, InExt, allocHeadroom, allocGlobal, InRange, Layout.sym_Caml_state,
            heapStart, heapEnd] at * <;> omega))]
    exact ready.domainWord
  poolZero := lpins8_observed ready.poolZero fun i hi => post.memory _ (fun owned => by
    rcases fS_coarse blockLow blockHigh owned with stack | global | heap <;>
      simp only [stackWin, InExt, allocHeadroom, allocGlobal, InRange, Layout.sym_pool,
        heapStart, heapEnd] at * <;> omega)
end OCaml.Vm.Boot.Startup
