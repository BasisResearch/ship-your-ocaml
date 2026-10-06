import OCaml.Vm.Boot.Startup.ExtTableFreeNormalized
import OCaml.Vm.Boot.Startup.ExtTableFreeImage
import OCaml.Vm.Boot.Startup.ExtTableFreeZeroNormalized
import OCaml.Vm.Boot.Startup.ExtTableFreeZeroImage
import OCaml.Vm.Boot.Startup.ExtTableFreeTailNormalized
import OCaml.Vm.Boot.Startup.ExtTableFreeTailImage
import OCaml.Vm.Boot.Startup.ExtTableSite
import OCaml.Vm.Boot.Startup.StatFree
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.FrameWindows
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap LeanRV64DExecutable
  OCaml.Vm.Primitives

theorem outW_below {ws : List W} (above : ∀ w ∈ ws, heapEnd ≤ w.lo) {a : Nat} (below : a < heapEnd) :
    OutW ws a := by
  induction ws with
  | nil => trivial
  | cons w rest ih =>
    exact ⟨Or.inl (Nat.lt_of_lt_of_le below (above w (by simp))),
      ih (fun w' hw => above w' (by simp [hw]))⟩

theorem outWRange_below {ws : List W} (above : ∀ w ∈ ws, heapEnd ≤ w.lo) {a n : Nat}
    (below : a + n ≤ heapEnd) : OutWRange ws a n := by
  induction ws with
  | nil => trivial
  | cons w rest ih =>
    exact ⟨Or.inl (Nat.le_trans below (above w (by simp))),
      ih (fun w' hw => above w' (by simp [hw]))⟩

/-- Stores confined to windows above the arena (native frames, stack-local
tables) keep startup readiness. -/
theorem RuntimeReady.above_log {H capacity oldsp oldra before after writes log pc value regs sp ra ws}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (inside : LogInW ws log) (above : ∀ w ∈ ws, heapEnd ≤ w.lo) : RuntimeReady H capacity sp ra after := by
  apply ready.window_log post keys cover gpFrame stack link aligned inside
  · intro pin hp
    have low := (allocator_sources pin hp).before_startup_count
    have bound : Layout.sym_startup_count ≤ heapEnd := by decide
    exact outW_below above (by omega)
  · exact outWRange_below above (by decide)
  · exact outWRange_below above (by decide)
  · intro a owned
    exact outW_below above (allocator_foot_below owned)

def extTableFreeLog (sp ra s1 t : BitVec 64) : List WEntry :=
  nativeWordLog sp 32 [(8, s1), (24, ra)] ++ [(t.toNat, 4, 0#64)]
def extTableFreeInput (sp ra s1 t : BitVec 64) : GRegs := [(2, sp), (9, s1), (1, ra), (10, t), (11, 0#64)]
def extTableFreeRegs (sp ra t : BitVec 64) : GRegs :=
  [(9, t), (2, nativeStack sp 32), (1, ra), (10, t), (11, 0#64)]

theorem logInW_left {w : W} {ws : List W} {log : List WEntry} (h : LogInW [w] log) :
    LogInW (w :: ws) log := by
  induction log with
  | nil => trivial
  | cons e rest ih =>
    obtain ⟨first, tail⟩ := h
    rcases first with inside | impossible
    · exact ⟨Or.inl inside, ih tail⟩
    · exact impossible.elim

theorem logInW_right {w : W} {ws : List W} {log : List WEntry} (h : LogInW ws log) :
    LogInW (w :: ws) log := by
  induction log with
  | nil => trivial
  | cons e rest ih => exact ⟨Or.inr h.1, ih h.2⟩

theorem extTableFreeLog_inside {sp ra s1 t} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩, ⟨t.toNat, t.toNat + Layout.ext_table_bytes⟩]
      (extTableFreeLog sp ra s1 t) := by
  apply log_in_append
  · apply logInW_left
    apply frame.word_log_inside
    intro off value member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega
  · exact ⟨Or.inr (Or.inl ⟨Nat.le_refl _, by show t.toNat + 4 ≤ t.toNat + Layout.ext_table_bytes; unfold Layout.ext_table_bytes; omega⟩), trivial⟩

/-- Save, take the no-entry-freeing branch and zero the size field. -/
theorem ext_table_free_zero (c : Config) (sp ra s1 t : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32) (site : ExtTableSite sp t)
    (regs : GHolds c.σ (extTableFreeInput sp ra s1 t)) :
    FnSummary 0x80003f98#64 (fun d => d = c)
      (WriteRegistersPost [2, 9] (extTableFreeLog sp ra s1 t) c 0x80003fe8#64 t (extTableFreeRegs sp ra t)) := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  apply registers_of_blocks leaf.image ?_
    (block_summary _ _ _ _ _ (show BlockInput (caml_ext_table_freeX3f98TSeg ++ caml_ext_table_freeX3fe4Seg)
        0x80003f98#64 (extTableFreeInput sp ra s1 t) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 9, 1, 10, 11]; decide
      shape := by change ChainOK _ [2, 9, 1, 10, 11] _; decide
      tick := leaf.tick
      facts := by
        have code := extTableFree_code leaf.image
        have zero := extTableFreeZero_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_ext_table_free_at_"
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · rfl
        · have w : WriteWindow (t + 0#64 + 0#64) 4 := by
            rw [BitVec.add_zero]
            exact site.window 0 4 (by decide) (by decide) (by decide)
          exact w.sw rfl rfl }))
  · change [((nativeStack sp 32 + 8#64).toNat, 8, s1), ((nativeStack sp 32 + 24#64).toNat, 8, ra),
      ((t + 0#64 + 0#64).toNat, 4, 0#64)] = _
    rw [BitVec.add_zero, BitVec.add_zero]
    rfl
  · rfl
  · change [(9, t + 0#64), (2, nativeStack sp 32), (1, ra), (10, t), (11, 0#64)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · decide
  · have image := site.image short
    have lower := frame.lower
    have bounds : Image.textBase + Image.textSize ≤ heapEnd ∧
        Image.rodataBase + Image.rodataSize ≤ heapEnd := by decide
    constructor
    all_goals apply OCaml.Vm.Sim.outLRange_of_windows (extTableFreeLog_inside frame (t := t) (ra := ra) (s1 := s1))
    all_goals exact ⟨Or.inl (by change _ ≤ nativeFrameBase sp 32; unfold nativeFrameBase; omega),
      Or.inl (by dsimp only; omega), trivial⟩

def extTableFreeTailLoads (sp t : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (t + 8#64).toNat, read8 c.σ.mem (nativeFrameBase sp 32 + 24),
   read8 c.σ.mem (nativeFrameBase sp 32 + 8)]

/-- Restore the caller and tail-call `caml_stat_free(tbl->contents)`. -/
theorem ext_table_free_tail (c : Config) (sp ra s1 t contents oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(9, t), (2, nativeStack sp 32)])
    (window : ReadWindow (t + 8#64) 8) (word : bytesT c.σ.mem (t + 8#64).toNat 8 = contents)
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra)
    (savedS1 : bytesT c.σ.mem (nativeFrameBase sp 32 + 8) 8 = s1) :
    FnSummary 0x80003fe8#64 (fun d => d = c)
      (WriteRegistersPost [10, 1, 9, 2] [] c 0x8000bb98#64 contents
        [(2, sp), (9, s1), (1, ra), (10, contents)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_ext_table_freeX3fe8Seg 0x80003fe8#64
        [(9, t), (2, nativeStack sp 32)] (extTableFreeTailLoads sp t c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 2]; decide
      shape := by change ChainOK _ [9, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := extTableFreeTail_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_ext_table_free_at_"
        · exact window.ld rfl rfl (read8_pins _ _)
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide)) }))
  · rfl
  · rfl
  · change [(2, nativeStack sp 32 + 32#64), (9, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 8))),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24))),
      (10, bytesVal .ld (read8 c.σ.mem (t + 8#64).toNat))] = _
    rw [read8_value, read8_value, read8_value, savedRa, savedS1, word, nativeStack_restore]
  · rfl
  · decide

/-- `caml_ext_table_free(tbl, 0)` on a stack-local table: zero the size, then
free the contents buffer `(q, n)`. -/
structure ExtTableFreed (H : List (Nat × Nat)) (q : BitVec 64) (n capacity : Nat)
    (sp ra s1 t : BitVec 64) (before after : Config) where
  zeroed : Config
  zero : WriteRegistersPost [2, 9] (extTableFreeLog sp ra s1 t) before 0x80003fe8#64 t (extTableFreeRegs sp ra t) zeroed
  called : Config
  tail : WriteRegistersPost [10, 1, 9, 2] [] zeroed 0x8000bb98#64 q [(2, sp), (9, s1), (1, ra), (10, q)] called
  freed : StatFreed H q n capacity sp ra called after

theorem ExtTableFreed.ready {H q n capacity sp ra s1 t before after}
    (w : ExtTableFreed H q n capacity sp ra s1 t before after) : RuntimeReady H capacity sp ra after :=
  w.freed.ready

theorem ext_table_free_empty (c : Config) (H : List (Nat × Nat)) (q : BitVec 64) (n capacity : Nat)
    (sp ra s1 t : BitVec 64) (ready : RuntimeReady ((q.toNat, n) :: H) capacity sp ra c)
    (frame : NativeFrame sp (32 + allocHeadroom)) (site : ExtTableSite sp t) (tableHigh : sp.toNat ≤ t.toNat)
    (regs : GHolds c.σ (extTableFreeInput sp ra s1 t)) (window : ReadWindow (t + 8#64) 8)
    (contents : bytesT c.σ.mem (t + 8#64).toNat 8 = q)
    (blockLow : heapStart ≤ q.toNat) (blockHigh : q.toNat + n ≤ heapEnd) :
    FnSummary 0x80003f98#64 (fun d => d = c)
      (fun after => Nonempty (ExtTableFreed H q n capacity sp ra s1 t c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame32 := frame.resize (small := 32) (by decide) (by decide)
  have frameA := frame.resize (small := allocHeadroom) (by decide) (by decide)
  obtain ⟨zeroed, run1, zero⟩ := (ext_table_free_zero c sp ra s1 t ready.toLeafInput frame32 site regs).run
    c ⟨pc, rfl⟩
  have lower := frame32.lower
  have readyZ := ready.above_log zero (by decide) (by simp only [extTableFreeRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ zero.regs (by rfl)) (gholds_lookup (n := 1) _ zero.regs (by rfl)) ready.aligned
    (extTableFreeLog_inside frame32) (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · change heapEnd ≤ nativeFrameBase sp 32; unfold nativeFrameBase; omega
      · change heapEnd ≤ t.toNat; omega)
  have memZ : zeroed.σ.mem = writeLog (writeLog c.σ.mem (nativeWordLog sp 32 [(8, s1), (24, ra)]))
      [(t.toNat, 4, 0#64)] := by rw [zero.memory, extTableFreeLog, writeLog_append]
  have savesInside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (nativeWordLog sp 32 [(8, s1), (24, ra)]) := by
    apply frame32.word_log_inside
    intro off value member
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega
  have tbound := site.bound
  have word : bytesT zeroed.σ.mem (t + 8#64).toNat 8 = q := by
    rw [memZ, site.addr (k := 8) (by decide),
      bytesT_writeLog_out _ (show OutLRange [(t.toNat, 4, 0#64)] (t.toNat + 8) 8 from ⟨Or.inr (by
        show t.toNat + 4 ≤ t.toNat + 8; omega), trivial⟩),
      bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows savesInside ⟨Or.inr (by dsimp only; omega), trivial⟩)]
    rw [← site.addr (k := 8) (by decide)]
    exact contents
  have saved (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(8, s1), (24, ra)]) :
      bytesT zeroed.σ.mem (nativeFrameBase sp 32 + off) 8 = value := by
    have small : off ≤ 24 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
    rw [memZ, bytesT_writeLog_out _ (show OutLRange [(t.toNat, 4, 0#64)] (nativeFrameBase sp 32 + off) 8 from
      ⟨Or.inl (by unfold nativeFrameBase; omega), trivial⟩)]
    apply frame32.word_log_read (slots := [(8, s1), (24, ra)])
    · intro k v hk
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp
    · exact member
  obtain ⟨called, run2, tail⟩ := (ext_table_free_tail zeroed sp ra s1 t q ra
    (zero.leaf (by rfl) ready.aligned) frame32
    ⟨gholds_lookup (n := 9) _ zero.regs (by rfl), gholds_lookup (n := 2) _ zero.regs (by rfl), trivial⟩
    window word (saved 24 ra (by simp)) (saved 8 s1 (by simp))).run zeroed ⟨zero.pc, rfl⟩
  have readyT := readyZ.effect tail (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ tail.regs (by rfl)) (gholds_lookup (n := 1) _ tail.regs (by rfl)) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  obtain ⟨after, run3, ⟨freed⟩⟩ := (stat_free_block called H q n capacity sp ra readyT tail.result frameA
    blockLow blockHigh).run called ⟨tail.pc, rfl⟩
  exact ⟨after, run1.trans (run2.trans run3), ⟨zeroed, zero, called, tail, freed⟩⟩
end OCaml.Vm.Boot.Startup
