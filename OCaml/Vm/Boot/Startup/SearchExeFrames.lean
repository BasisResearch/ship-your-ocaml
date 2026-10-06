import OCaml.Vm.Boot.Startup.SearchInPath
import OCaml.Vm.Boot.Startup.ExtTableFree
import OCaml.Vm.Boot.Startup.EmbedFrame
import OCaml.Vm.Boot.Startup.CallerFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- A free touches nothing at or above its caller's stack pointer, and no kept byte. -/
theorem fS_outside {H q n} {sp : BitVec 64} {x : Nat} (frame : NativeFrame sp allocHeadroom)
    (deep : embedLimit + allocHeadroom ≤ sp.toNat)
    (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd)
    (where_ : sp.toNat ≤ x ∨ KeptByte x) : ¬ fS H q n sp x := by
  intro owned
  have lower := frame.lower
  rcases fS_coarse blockLow blockHigh owned with stack | global | heap
  · unfold stackWin InExt at stack
    rcases where_ with h | h
    · omega
    · have := h.lt
      omega
  · rcases where_ with h | h
    · have := allocator_foot_below (H := H) (Or.inl global); omega
    · exact h.not_foot (H := H) (Or.inl global)
  · rcases where_ with h | h
    · omega
    · have := (h.low heap.2).1
      omega

theorem StatFreed.byte {H q n capacity sp ra before after} (w : StatFreed H q n capacity sp ra before after)
    (frame : NativeFrame sp allocHeadroom) (deep : embedLimit + allocHeadroom ≤ sp.toNat)
    (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd)
    {x : Nat} (where_ : sp.toNat ≤ x ∨ KeptByte x) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have same := w.free.memory x (fS_outside frame deep blockLow blockHigh where_)
  change (after.σ.mem[x]?).getD 0 = (w.atFree.σ.mem[x]?).getD 0 at same
  rw [same, w.dispatch.memory]

theorem StatFreed.embed_frame {H q n capacity sp ra before after} (w : StatFreed H q n capacity sp ra before after)
    (frame : NativeFrame sp allocHeadroom) (deep : embedLimit + allocHeadroom ≤ sp.toNat)
    (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd) :
    EmbedFrame before after :=
  ⟨fun x hx => w.byte frame deep blockLow blockHigh (Or.inr hx)⟩

/-- Freeing the empty table keeps everything above its header and every kept byte. -/
theorem ExtTableFreed.byte {H q n capacity sp ra s1 t before after}
    (w : ExtTableFreed H q n capacity sp ra s1 t before after) (frame : NativeFrame sp (32 + allocHeadroom))
    (deep : embedLimit + 32 + allocHeadroom ≤ sp.toNat)
    (tableHigh : sp.toNat ≤ t.toNat) (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd)
    {x : Nat} (where_ : t.toNat + 4 ≤ x ∨ KeptByte x) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have frame32 := frame.resize (small := 32) (by decide) (by decide)
  have frameA := frame.resize (small := allocHeadroom) (by decide) (by decide)
  have lower := frame32.lower
  have freed := w.freed.byte frameA (by omega) blockLow blockHigh (x := x) (by
    rcases where_ with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h)
  have saves : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 [(8, s1), (24, ra)]) := by
    apply frame32.word_log_inside
    intro off value member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega
  have below : x < nativeFrameBase sp 32 ∨ sp.toNat ≤ x := by
    rcases where_ with h | h
    · exact Or.inr (by omega)
    · have := h.lt
      left
      unfold nativeFrameBase
      omega
  have outT : x < t.toNat ∨ t.toNat + 4 ≤ x := by
    rcases where_ with h | h
    · exact Or.inr h
    · have := h.lt
      left
      omega
  rw [freed, show w.called.σ.mem = w.zeroed.σ.mem from w.tail.memory, w.zero.memory, extTableFreeLog,
    writeLog_append, writeLog_out _ _ _ (show OutL [(t.toNat, 4, 0#64)] x from ⟨outT, trivial⟩),
    frameOn_writeLog _ _ _ saves x ⟨by rcases below with h | h; exact Or.inl h; exact Or.inr h, trivial⟩]

theorem ExtTableFreed.embed_frame {H q n capacity sp ra s1 t before after}
    (w : ExtTableFreed H q n capacity sp ra s1 t before after) (frame : NativeFrame sp (32 + allocHeadroom))
    (deep : embedLimit + 32 + allocHeadroom ≤ sp.toNat)
    (tableHigh : sp.toNat ≤ t.toNat) (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd) :
    EmbedFrame before after :=
  ⟨fun x hx => w.byte frame deep tableHigh blockLow blockHigh (Or.inr hx)⟩

/-- A run whose memory effect is a write log below `sp` keeps its caller's frame. -/
theorem CallerFrame.of_log {sp : BitVec 64} {size : Nat} {log : List WEntry} {before after : Config}
    (same : after.σ.mem = writeLog before.σ.mem log)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log) : CallerFrame sp before after :=
  ⟨fun a caller => by rw [same, frameOn_writeLog _ _ _ inside a ⟨Or.inr caller, trivial⟩]⟩

theorem CallerFrame.mono {sp sp' : BitVec 64} {before after : Config} (h : CallerFrame sp before after)
    (le : sp.toNat ≤ sp'.toNat) : CallerFrame sp' before after :=
  ⟨fun a bound => h.byte a (Nat.le_trans le bound)⟩

/-- Table initialization keeps every byte of the caller's frame above the header. -/
theorem ExtTableReturned.above {H capacity sp ra s0 t n before after}
    (w : ExtTableReturned H capacity sp ra s0 t n before after) (frame : NativeFrame sp 560)
    {a : Nat} (caller : sp.toNat ≤ a) (above : t.toNat + Layout.ext_table_bytes ≤ a) :
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0 := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  have alloc := (w.allocation.allocation.caller_frame nested).byte a (by
    rw [short.stack_nat]; unfold nativeFrameBase; omega)
  rw [show after.σ.mem = w.published.σ.mem from w.post.memory, w.publication.memory,
    writeLog_out _ _ _ (show OutL (extTablePublishLog t _) a from ⟨Or.inr (by
      unfold Layout.off_ext_table_contents Layout.ext_table_bytes at *; omega), trivial⟩), alloc,
    w.allocation.call.memory, w.allocation.setup.memory,
    frameOn_writeLog _ _ _ (extTableLog_inside short) a ⟨Or.inr caller, Or.inr above, trivial⟩]

/-- Freeing the table keeps the caller's s0, s2 and s3. -/
theorem ExtTableFreed.saved_gpr {H q n capacity sp ra s1 t before after k}
    (w : ExtTableFreed H q n capacity sp ra s1 t before after) (member : k ∈ [8, 18, 19]) :
    gprGet after.σ k = gprGet before.σ k := by
  have range : 1 ≤ k ∧ k ≤ 31 ∧ k ≠ 2 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 1 := by simp at member; omega
  have freed := w.freed.saved_gpr (k := k) (by simp [vsaSaved] at member ⊢; omega)
  have tail := w.tail.toEffectPost.gpr_frame (by decide) k range.1 range.2.1 (by simp; omega)
  have zero := w.zero.toEffectPost.gpr_frame (by decide) k range.1 range.2.1 (by simp; omega)
  exact freed.trans (tail.trans zero)

/-- A free keeps every byte of another live block disjoint from the freed one. -/
theorem fS_live_outside {H q n} {sp : BitVec 64} {x : Nat} (frame : NativeFrame sp allocHeadroom)
    {e : Nat × Nat} (member : e ∈ H) (inside : InExt e x) (apart : ¬ InExt (q.toNat, n) x)
    (arena : heapStart ≤ x ∧ x < heapEnd) : ¬ fS H q n sp x := by
  intro owned
  have lower := frame.lower
  change stackWin sp allocHeadroom x ∨ (heapFoot vsaLayoutP ((q.toNat, n) :: H) x ∨
    InExt (q.toNat, n) x) at owned
  rcases owned with stack | (global | heap) | block
  · unfold stackWin InExt at stack
    omega
  · change allocGlobal x at global
    unfold allocGlobal InRange heapStart at *
    omega
  · exact heap.2.2 e (List.mem_cons_of_mem _ member) inside
  · exact apart block

theorem StatFreed.live_byte {H q n capacity sp ra before after} (w : StatFreed H q n capacity sp ra before after)
    (frame : NativeFrame sp allocHeadroom) {e : Nat × Nat} (member : e ∈ H) {x : Nat} (inside : InExt e x)
    (apart : ¬ InExt (q.toNat, n) x) (arena : heapStart ≤ x ∧ x < heapEnd) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have same := w.free.memory x (fS_live_outside frame member inside apart arena)
  change (after.σ.mem[x]?).getD 0 = (w.atFree.σ.mem[x]?).getD 0 at same
  rw [same, w.dispatch.memory]

theorem ExtTableFreed.live_byte {H q n capacity sp ra s1 t before after}
    (w : ExtTableFreed H q n capacity sp ra s1 t before after) (frame : NativeFrame sp (32 + allocHeadroom))
    (tableHigh : sp.toNat ≤ t.toNat) {e : Nat × Nat} (member : e ∈ H) {x : Nat} (inside : InExt e x)
    (apart : ¬ InExt (q.toNat, n) x) (arena : heapStart ≤ x ∧ x < heapEnd) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have frame32 := frame.resize (small := 32) (by decide) (by decide)
  have frameA := frame.resize (small := allocHeadroom) (by decide) (by decide)
  have lower := frame.lower
  have saves : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 [(8, s1), (24, ra)]) := by
    apply frame32.word_log_inside
    intro off value member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega
  have below : x < nativeFrameBase sp 32 := by unfold nativeFrameBase allocHeadroom at *; omega
  rw [w.freed.live_byte frameA member inside apart arena, show w.called.σ.mem = w.zeroed.σ.mem from w.tail.memory,
    w.zero.memory, extTableFreeLog, writeLog_append,
    writeLog_out _ _ _ (show OutL [(t.toNat, 4, 0#64)] x from ⟨Or.inl (by omega), trivial⟩),
    frameOn_writeLog _ _ _ saves x ⟨Or.inl below, trivial⟩]

/-- Kept bytes are outside everything strdup may write below a deep enough caller. -/
theorem KeptByte.strdup_kept {a : Nat} {H : List (Nat × Nat)} {sp : BitVec 64} (ha : KeptByte a)
    (deep : embedLimit + 48 + allocHeadroom < sp.toNat) : StrdupKept H sp a := by
  by_cases below : a < heapEnd
  · exact Or.inr (Or.inr (Or.inl (ha.low below)))
  · exact Or.inr (Or.inl ⟨by omega, by have := ha.lt; omega⟩)
end OCaml.Vm.Boot.Startup
