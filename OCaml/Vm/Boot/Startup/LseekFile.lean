import OCaml.Vm.Boot.Startup.LseekFileSteps
import OCaml.Vm.Boot.Startup.LseekREntryCallInterface
import OCaml.Vm.Boot.Startup.OpenRun
import OCaml.Vm.Boot.Startup.OpenProg
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `lseek(3, -16, SEEK_END)` on "/prog": newlib's `lseek` → `_lseek_r` →
htif.c's `_lseek`. The position becomes the file's size less 16. -/

/-- The registers `lseek` may change besides `a0` and the ones it restores. -/
def lseekWrites : List Nat := [14, 10, 13, 12, 11, 15, 8, 2, 1, 16, 17, 6]

/-- The position store. -/
abbrev lseekLog : List WEntry := [(Layout.sym_fds + 80, 8, 0x249c#64)]

/-- `lseek(3, -16, SEEK_END)` returned 0x249c. -/
structure LseekFile (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 : BitVec 64) (before after : Config) :
    Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, sp), (8, s0), (1, ra), (10, 0x249c#64)]
  kept : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ lseekWrites → gprGet after.σ n = gprGet before.σ n
  ready : RuntimeReady H capacity sp ra after
  /-- Outside its 64 bytes of stack and the `errno` words, memory is the
  position store over the caller's. -/
  mem : ∀ x, x < sp.toNat - 64 ∨ sp.toNat ≤ x → OutW errnoWindows x →
    (after.σ.mem[x]?).getD 0 = ((writeLog before.σ.mem lseekLog)[x]?).getD 0

theorem lseek_file (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 : BitVec 64)
    (ready : RuntimeReady H capacity sp ra c) (frame : NativeFrame sp (16 + 48))
    (regs : GHolds c.σ [(2, sp), (1, ra), (8, s0), (10, 3#64), (11, -16#64), (12, 2#64)])
    (fs : FsWords c.σ.mem) (node : BitVec 64) (slot : FsSlotOne c.σ.mem node)
    (kind : read4 c.σ.mem (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8])
    (nodeWord : read4 c.σ.mem (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x80042574#64 (fun d => d = c) (LseekFile H capacity sp ra s0 c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have f1 : NativeFrame sp 16 := frame.resize (by decide) (by decide)
  have f2 : NativeFrame (nativeStack sp 16) 48 := frame.nested (front := 16) (by decide)
  have lower : heapEnd + 64 ≤ sp.toNat := frame.lower
  have h1 : (nativeStack sp 16).toNat = sp.toNat - 16 := by rw [f1.stack_nat]; rfl
  -- lseek: load _impure_ptr, tail-jump to _lseek_r
  obtain ⟨d1, run1, p1⟩ := (lib_lseek c 3#64 (-16#64) 2#64 ra ready.toLeafInput
    ⟨gholds_lookup (n := 10) _ regs rfl, gholds_lookup (n := 11) _ regs rfl, gholds_lookup (n := 12) _ regs rfl,
      trivial⟩).run c ⟨pc, rfl⟩
  have keep1 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [14, 10, 13, 12, 11])
      (hv : gprGet c.σ n = some v) : gprGet d1.σ n = some v :=
    (p1.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have ready1 := ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (keep1 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ regs rfl))
    (keep1 1 _ (by decide) (by decide) (by decide) ready.raReg) ready.aligned f1 (by simp only [LogInW])
  -- _lseek_r: save, clear errno, call _lseek
  obtain ⟨d2, run2, p2⟩ := (lseek_r_entry d1 sp ra s0 (getenvReent c) 3#64 (-16#64) 2#64 ready1.toLeafInput f1
    ⟨keep1 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ regs rfl), ready1.raReg,
      keep1 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ regs rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 11) _ p1.regs rfl,
      gholds_lookup (n := 12) _ p1.regs rfl, gholds_lookup (n := 13) _ p1.regs rfl, trivial⟩).run d1 ⟨p1.pc, rfl⟩
  have ready2 := ready1.errno_log p2 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2.regs rfl) (gholds_lookup (n := 1) _ p2.regs rfl) ready.aligned f1
    (openRLog_inside f1)
  obtain ⟨d3, run3, p3⟩ := (call_registers_summary jal_80042350_call_shape jal_80042350_call_decode d2
    (jal_80042350_call_pins ready2.image) p2.good ready2.image p2.tick p2.minstret
    [(2, nativeStack sp 16), (10, 3#64), (11, -16#64), (12, 2#64), (8, getenvReent c)]
    ⟨gholds_lookup (n := 2) _ p2.regs rfl, gholds_lookup (n := 10) _ p2.regs rfl,
      gholds_lookup (n := 11) _ p2.regs rfl, gholds_lookup (n := 12) _ p2.regs rfl,
      gholds_lookup (n := 8) _ p2.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d2 ⟨p2.pc, rfl⟩
  have p3' : WriteRegistersPost [1] [] d2 jal_80042350_call.target 3#64
      ((1, jal_80042350_call.link) :: [(2, nativeStack sp 16), (10, 3#64), (11, -16#64), (12, 2#64),
        (8, getenvReent c)]) d3 := p3
  have ready3 := ready2.stack_log p3' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p3'.regs rfl) (gholds_lookup (n := 1) _ p3'.regs rfl) (by decide) f2
    (by simp only [LogInW])
  -- memory up to _lseek's entry
  have mem3 (x : Nat) (stack : x < sp.toNat - 16 ∨ sp.toNat ≤ x) (errno : OutW errnoWindows x) :
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p3'.memory, show writeLog d2.σ.mem [] = d2.σ.mem from rfl, p2.memory,
      frameOn_writeLog _ _ _ (openRLog_inside f1) x ⟨by simp only [nativeFrameBase] at *; omega, errno⟩, p1.memory]
    rfl
  have glob3 (x : Nat) (hi : x < heapEnd) (errno : OutW errnoWindows x) :
      (d3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := mem3 x (Or.inl (by omega)) errno
  -- _lseek: fs_ready set, save ra
  obtain ⟨d4, run4, p4⟩ := (htif_lseek_entry d3 (nativeStack sp 16) jal_80042350_call.link 3#64 (-16#64) 2#64
    ready3.toLeafInput f2
    ⟨gholds_lookup (n := 2) _ p3'.regs rfl, gholds_lookup (n := 1) _ p3'.regs rfl,
      gholds_lookup (n := 10) _ p3'.regs rfl, gholds_lookup (n := 11) _ p3'.regs rfl,
      gholds_lookup (n := 12) _ p3'.regs rfl, trivial⟩
    (by
      rw [read4_observed (m := c.σ.mem) _ fun k hk => glob3 _ (by unfold Layout.sym_fs_ready heapEnd; omega)
        (by simp only [OutW, errnoWindows, and_true, Layout.sym_fs_ready]; omega)]
      exact fs.ready)).run d3 ⟨p3'.pc, rfl⟩
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p4.regs rfl) (gholds_lookup (n := 1) _ p4.regs rfl) (by decide) f2
    (htifLseekLog_inside f2)
  have glob4 (x : Nat) (hi : x < heapEnd) (errno : OutW errnoWindows x) :
      (d4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p4.memory, frameOn_writeLog _ _ _ (htifLseekLog_inside f2) x ⟨by
      simp only [nativeFrameBase, h1] at *; omega, trivial⟩]
    exact glob3 x hi errno
  have slotG (x : Nat) (lo : slotOne ≤ x) (hi : x < slotOne + 56) :
      (d4.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    glob4 x (by unfold slotOne Layout.sym_files heapEnd at *; omega) (HtifByte.out_errno (slotOne_htif lo hi))
  -- _lseek: SEEK_END on the file
  obtain ⟨d5, run5, p5⟩ := (htif_lseek_end d4 (nativeStack sp 16) jal_80042350_call.link ready4.toLeafInput f2
    ⟨gholds_lookup (n := 2) _ p4.regs rfl, gholds_lookup (n := 1) _ p4.regs rfl,
      gholds_lookup (n := 10) _ p4.regs rfl, gholds_lookup (n := 11) _ p4.regs rfl,
      gholds_lookup (n := 12) _ p4.regs rfl, trivial⟩
    (by
      rw [read4_observed (m := c.σ.mem) _ fun k hk => glob4 _ (by unfold Layout.sym_fds heapEnd; omega)
        (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega)]
      exact kind)
    (by
      rw [read4_observed (m := c.σ.mem) _ fun k hk => glob4 _ (by unfold Layout.sym_fds heapEnd; omega)
        (by simp only [OutW, errnoWindows, and_true, Layout.sym_fds]; omega)]
      exact nodeWord)
    (by rw [slotG _ (by unfold slotOne; omega) (by unfold slotOne; omega)]; exact slot.dirByte)
    (by
      rw [word_observed (m := c.σ.mem) _ fun i hi => slotG _ (by unfold slotOne; omega)
        (by unfold slotOne; omega)]
      exact slot.size)
    (by
      rw [p4.memory, htifLseekLog]
      exact f2.word_log_read (by intro k v hk; simp at hk; omega) (by simp) _ (by simp))).run d4 ⟨p4.pc, rfl⟩
  have ready5 := ready4.window_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p5.regs rfl) (gholds_lookup (n := 1) _ p5.regs rfl) (by decide)
    (show LogInW takeWindows lseekLog by simp only [lseekLog, LogInW, InsideW, takeWindows]; refine ⟨?_, trivial⟩; omega)
    takeWindows_out_pins ⟨Or.inl (by decide), Or.inl (by decide), trivial⟩
    ⟨Or.inl (by decide), Or.inl (by decide), trivial⟩ (fun a foot => takeWindows_out_foot foot)
  -- _lseek_r: restore and return
  have frame5 (x : Nat) (lo : sp.toNat - 16 ≤ x) (hi : x < sp.toNat) :
      (d5.σ.mem[x]?).getD 0 = (d2.σ.mem[x]?).getD 0 := by
    rw [p5.memory, frameOn_writeLog _ _ _ (show LogInW takeWindows lseekLog by
        simp only [lseekLog, LogInW, InsideW, takeWindows]; refine ⟨?_, trivial⟩; omega) x
        (by simp only [OutW, takeWindows, and_true, Layout.sym_files, Layout.sym_fds, heapEnd] at *; omega),
      p4.memory, frameOn_writeLog _ _ _ (htifLseekLog_inside f2) x ⟨Or.inr (by rw [h1]; omega), trivial⟩,
      p3'.memory]
    rfl
  obtain ⟨d6, run6, p6⟩ := (lseek_r_succeed d5 sp ra s0 0x249c#64 jal_80042350_call.link ready5.toLeafInput f1
    ⟨gholds_lookup (n := 10) _ p5.regs rfl, gholds_lookup (n := 2) _ p5.regs rfl, trivial⟩ (by decide)
    (fun off value member => by
      have range : off + 8 ≤ 16 := by
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      rw [word_observed (m := d2.σ.mem) _ fun i hi => frame5 _ (by simp only [nativeFrameBase]; omega)
        (by simp only [nativeFrameBase]; omega), p2.memory, openRLog, writeLog_append,
        bytesT_writeLog_out _ (by
          have l := lower; unfold heapEnd at l; simp only [OutLRange, and_true, nativeFrameBase]; omega)]
      exact f1.word_log_read (by
        intro k v hk; simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
        (by simp) _ (by
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member ⊢
          rcases member with h | h <;> simp [h]))
    ready.aligned).run d5 ⟨p5.pc, rfl⟩
  have keepAll (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ lseekWrites) : gprGet d6.σ n = gprGet c.σ n := by
    simp only [lseekWrites, List.mem_cons, List.not_mem_nil, or_false] at out
    exact (p6.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((p5.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
        ((p4.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          ((p3'.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
            ((p2.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
              (p1.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega))))))
  refine ⟨d6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), {
    pc := p6.pc
    regs := ⟨gholds_lookup (n := 2) _ p6.regs rfl, gholds_lookup (n := 8) _ p6.regs rfl,
      gholds_lookup (n := 1) _ p6.regs rfl, gholds_lookup (n := 10) _ p6.regs rfl, trivial⟩
    kept := keepAll
    ready := ready5.errno_log p6 (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ p6.regs rfl) (gholds_lookup (n := 1) _ p6.regs rfl) ready.aligned f1
      (by simp only [LogInW])
    mem := fun x stack errno => ?_ }⟩
  rw [show d6.σ.mem = d5.σ.mem from p6.memory, p5.memory]
  apply writeLog_getD_congr
  rw [p4.memory, frameOn_writeLog _ _ _ (htifLseekLog_inside f2) x ⟨by
    simp only [nativeFrameBase, h1] at *; omega, trivial⟩]
  exact mem3 x (by omega) errno
end OCaml.Vm.Boot.Startup
