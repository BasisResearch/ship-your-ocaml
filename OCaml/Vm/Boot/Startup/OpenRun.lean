import OCaml.Vm.Boot.Startup.OpenSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `open("ocamlrun", O_RDONLY)` on the bare-metal file system: newlib's
`open` → `_open_r` → htif.c's `_open`, whose `resolve` initializes the file
system and finds no such file: ENOENT, -1. -/

/-- The callee-saved registers `open` keeps for its caller. -/
def openCarried (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64) : GRegs :=
  [(8, s0), (9, s1), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (23, s7), (24, s8), (25, s9), (26, s10)]

/-- The stack `open` uses below its caller's: its own frame, `_open_r`'s,
`_open`'s, `resolve`'s, `fs_init`'s, `new_node`'s and malloc's headroom. -/
abbrev openDepth : Nat := 80 + (16 + (80 + (96 + (96 + (64 + allocHeadroom)))))

theorem libOpenLog_inside {sp ra a2 a3 a4 a5 a6 a7 : BitVec 64} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (libOpenLog sp ra a2 a3 a4 a5 a6 a7) :=
  frame.word_log_inside fun off value member => by
    simp only [libOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega

theorem openRLog_inside {sp ra s0 : BitVec 64} (frame : NativeFrame sp 16) :
    LogInW (⟨nativeFrameBase sp 16, sp.toNat⟩ :: errnoWindows) (openRLog sp ra s0) :=
  OCaml.Vm.Sim.logInW_append'
    (OCaml.Vm.Sim.logInW_mono (frame.word_log_inside fun off value member => by simp at member; omega)
      (fun w hw => by simp at hw; simp [hw]))
    (by simp only [LogInW, InsideW, errnoWindows]; exact ⟨Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)), trivial⟩)

theorem htifOpenLog_inside {sp ra s0 s1 s2 : BitVec 64} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (htifOpenLog sp ra s0 s1 s2) :=
  OCaml.Vm.Sim.logInW_append'
    (OCaml.Vm.Sim.logInW_append' (frame.word_log_inside fun off value member => by simp at member; omega)
      (frame.word_log_inside fun off value member => by simp at member; omega)) (by
    have lower := frame.lower
    simp only [LogInW, InsideW, resAt_nat frame (by decide : 4 ≤ 80), resAt_nat frame (by decide : 36 ≤ 80),
      or_false, and_true]
    unfold nativeFrameBase at *
    refine ⟨?_, ?_⟩ <;> omega)

/-- `open("ocamlrun", O_RDONLY)` returned -1 (ENOENT); the file system is up. -/
structure OpenOcamlrun (H : List (Nat × Nat)) (capacity : Nat) (sp ra path : BitVec 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64) (before after : Config) where
  node : BitVec 64
  pc : PCAt ra after
  regs : GHolds after.σ ([(2, sp), (1, ra), (10, -1#64)] ++ openCarried s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
  ready : RuntimeReady ((node.toNat, 5) :: H) capacity sp ra after
  embed : EmbedImage after
  slot : FsSlotOne after.σ.mem node
  name : OcamlrunName after.σ.mem path

theorem open_ocamlrun (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra path a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp openDepth)
    (deep : embedLimit + openDepth ≤ sp.toNat) (image : EmbedImage c)
    (regs : GHolds c.σ (libOpenInput sp ra path 0#64 a2 a3 a4 a5 a6 a7 ++ openCarried s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10))
    (notReady : read4 c.σ.mem Layout.sym_fs_ready = [0#8, 0#8, 0#8, 0#8])
    (clear : ∀ j, 1 ≤ j → j < 64 → slotUsed c.σ.mem (Layout.sym_files + 56 * j) = 0#8)
    (impure : getenvReent c = 0x80064668#64)
    (name : OcamlrunName c.σ.mem path) (home : ∃ e ∈ H, e.1 ≤ path.toNat ∧ path.toNat + 9 ≤ e.1 + e.2)
    (pathLow : path.toNat + 16 ≤ heapEnd)
    (charged : vsaChg 5 charge) :
    FnSummary 0x80042590#64 (fun d => d = c)
      (fun after => Nonempty (OpenOcamlrun H capacity sp ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have entry := (gholds_append _ _).1 regs
  -- frames
  have f0 : NativeFrame sp 80 := frame.resize (by decide) (by decide)
  have n1 : NativeFrame (nativeStack sp 80) (16 + (80 + (96 + (96 + (64 + allocHeadroom))))) :=
    (show NativeFrame sp (80 + (16 + (80 + (96 + (96 + (64 + allocHeadroom)))))) from frame).nested (front := 80) (by decide)
  have f1 : NativeFrame (nativeStack sp 80) 16 := n1.resize (by unfold allocHeadroom; omega) (by decide)
  have n2 : NativeFrame (nativeStack (nativeStack sp 80) 16) (80 + (96 + (96 + (64 + allocHeadroom)))) :=
    n1.nested (front := 16) (by decide)
  have f2 : NativeFrame (nativeStack (nativeStack sp 80) 16) 80 := n2.resize (by unfold allocHeadroom; omega) (by decide)
  have lower := frame.lower
  have nat0 := f0.stack_nat
  have nat1 := f1.stack_nat
  have nat2 := f2.stack_nat
  have h1 : (nativeStack sp 80).toNat = sp.toNat - 80 := by rw [nat0]; rfl
  have h2 : (nativeStack (nativeStack sp 80) 16).toNat = sp.toNat - 96 := by
    rw [nat1]; unfold nativeFrameBase; rw [h1]; omega
  have h3 : (nativeStack (nativeStack (nativeStack sp 80) 16) 80).toNat = sp.toNat - 176 := by
    rw [nat2]; unfold nativeFrameBase; rw [h2]; omega
  -- open: spill the arguments, call _open_r
  obtain ⟨d1, run1, p1⟩ := (lib_open_entry c sp ra path 0#64 a2 a3 a4 a5 a6 a7 ready.toLeafInput f0 entry.1).run c
    ⟨pc, rfl⟩
  have ready1 := ready.stack_log p1 (by decide) (by simp only [libOpened, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) ready.aligned f0
    (libOpenLog_inside f0)
  have keep1 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [12, 11, 13, 6, 28, 2, 10, 29])
      (hv : gprGet c.σ n = some v) : gprGet d1.σ n = some v :=
    (p1.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  obtain ⟨d2, run2, p2⟩ := (call_registers_summary jal_800425d4_call_shape jal_800425d4_call_decode d1
    (jal_800425d4_call_pins ready1.image) p1.good ready1.image p1.tick p1.minstret
    [(2, nativeStack sp 80), (8, s0), (10, getenvReent c), (11, path), (12, 0#64),
      (13, Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb a2 31 0))]
    ⟨gholds_lookup (n := 2) _ p1.regs rfl,
      keep1 8 s0 (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ entry.2 rfl),
      gholds_lookup (n := 10) _ p1.regs rfl, gholds_lookup (n := 11) _ p1.regs rfl,
      gholds_lookup (n := 12) _ p1.regs rfl, gholds_lookup (n := 13) _ p1.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d1 ⟨p1.pc, rfl⟩
  have p2' : WriteRegistersPost [1] [] d1 jal_800425d4_call.target (getenvReent c)
      ((1, jal_800425d4_call.link) :: [(2, nativeStack sp 80), (8, s0), (10, getenvReent c), (11, path), (12, 0#64),
        (13, Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb a2 31 0))]) d2 := p2
  have ready2 := ready1.stack_log p2' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2'.regs rfl) (gholds_lookup (n := 1) _ p2'.regs rfl) (by decide) f1
    (by simp only [LogInW])
  have keep2 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out1 : n ∉ [12, 11, 13, 6, 28, 2, 10, 29])
      (out2 : n ∉ [1]) (hv : gprGet c.σ n = some v) : gprGet d2.σ n = some v :=
    (p2'.toEffectPost.gpr_frame (by decide) n lo hi out2).trans (keep1 n v lo hi out1 hv)
  -- _open_r: clear the global errno, call _open
  obtain ⟨d3, run3, p3⟩ := (open_r_entry d2 (nativeStack sp 80) _ s0 (getenvReent c) path 0#64 _ ready2.toLeafInput f1
    (gholds_select p2'.regs _ fun n v member => by
      simp only [openRInput, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl)).run d2 ⟨p2'.pc, rfl⟩
  have ready3 := ready2.errno_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p3.regs rfl) (gholds_lookup (n := 1) _ p3.regs rfl) (by decide) f1 (openRLog_inside f1)
  have keep3 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out1 : n ∉ [12, 11, 13, 6, 28, 2, 10, 29])
      (out3 : n ∉ [15, 10, 12, 8, 11, 2] ∧ n ∉ [1]) (hv : gprGet c.σ n = some v) : gprGet d3.σ n = some v :=
    (p3.toEffectPost.gpr_frame (by decide) n lo hi out3.1).trans (keep2 n v lo hi out1 out3.2 hv)
  obtain ⟨d4, run4, p4⟩ := (call_registers_summary jal_8004d7cc_call_shape jal_8004d7cc_call_decode d3
    (jal_8004d7cc_call_pins ready3.image) p3.good ready3.image p3.tick p3.minstret
    [(2, nativeStack (nativeStack sp 80) 16), (8, getenvReent c), (9, s1), (18, s2), (10, path), (11, 0#64)]
    ⟨gholds_lookup (n := 2) _ p3.regs rfl, gholds_lookup (n := 8) _ p3.regs rfl,
      keep3 9 s1 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ entry.2 rfl),
      keep3 18 s2 (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ entry.2 rfl),
      gholds_lookup (n := 10) _ p3.regs rfl, gholds_lookup (n := 11) _ p3.regs rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d3 ⟨p3.pc, rfl⟩
  have p4' : WriteRegistersPost [1] [] d3 jal_8004d7cc_call.target path
      ((1, jal_8004d7cc_call.link) :: [(2, nativeStack (nativeStack sp 80) 16), (8, getenvReent c), (9, s1), (18, s2),
        (10, path), (11, 0#64)]) d4 := p4
  have ready4 := ready3.stack_log p4' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p4'.regs rfl) (gholds_lookup (n := 1) _ p4'.regs rfl) (by decide) f2
    (by simp only [LogInW])
  -- _open: check the flags, call resolve
  obtain ⟨d5, run5, p5⟩ := (htif_open_entry d4 (nativeStack (nativeStack sp 80) 16) _ (getenvReent c) s1 s2 path
    ready4.toLeafInput f2 (gholds_select p4'.regs _ fun n v member => by
      simp only [htifOpenInput, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl)).run d4 ⟨p4'.pc, rfl⟩
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p5.regs rfl) (gholds_lookup (n := 1) _ p5.regs rfl) (by decide) f2
    (htifOpenLog_inside f2)
  have keep5 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out1 : n ∉ [12, 11, 13, 6, 28, 2, 10, 29])
      (out3 : n ∉ [15, 10, 12, 8, 11, 2] ∧ n ∉ [1]) (out5 : n ∉ [11, 8, 14, 15, 9, 18, 2] ∧ n ∉ [1])
      (hv : gprGet c.σ n = some v) : gprGet d5.σ n = some v :=
    (p5.toEffectPost.gpr_frame (by decide) n lo hi out5.1).trans
      ((p4'.toEffectPost.gpr_frame (by decide) n lo hi out5.2).trans (keep3 n v lo hi out1 out3 hv))
  have c5 (n : Nat) (v : BitVec 64) (hn : n ∈ [19, 20, 21, 22, 23, 24, 25, 26])
      (hv : lookupG n (openCarried s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) = some v) : gprGet d5.σ n = some v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    exact keep5 n v (by omega) (by omega) (by simp; omega) ⟨by simp; omega, by simp; omega⟩
      ⟨by simp; omega, by simp; omega⟩ (gholds_lookup _ entry.2 hv)
  obtain ⟨d6, run6, p6⟩ := (call_registers_summary jal_800008f8_call_shape jal_800008f8_call_decode d5
    (jal_800008f8_call_pins ready5.image) p5.good ready5.image p5.tick p5.minstret
    [(2, nativeStack (nativeStack (nativeStack sp 80) 16) 80), (10, path),
      (11, nativeStack (nativeStack (nativeStack sp 80) 16) 80), (8, 0#64), (9, 2#64), (18, 0#64), (19, s3), (20, s4),
      (21, s5), (22, s6), (23, s7), (24, s8), (25, s9), (26, s10)]
    ⟨gholds_lookup (n := 2) _ p5.regs rfl, gholds_lookup (n := 10) _ p5.regs rfl,
      gholds_lookup (n := 11) _ p5.regs rfl, gholds_lookup (n := 8) _ p5.regs rfl,
      gholds_lookup (n := 9) _ p5.regs rfl, gholds_lookup (n := 18) _ p5.regs rfl,
      c5 19 _ (by decide) rfl, c5 20 _ (by decide) rfl, c5 21 _ (by decide) rfl, c5 22 _ (by decide) rfl,
      c5 23 _ (by decide) rfl, c5 24 _ (by decide) rfl, c5 25 _ (by decide) rfl, c5 26 _ (by decide) rfl, trivial⟩
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d5 ⟨p5.pc, rfl⟩
  have p6' : WriteRegistersPost [1] [] d5 jal_800008f8_call.target path
      ((1, jal_800008f8_call.link) :: [(2, nativeStack (nativeStack (nativeStack sp 80) 16) 80), (10, path),
        (11, nativeStack (nativeStack (nativeStack sp 80) 16) 80), (8, 0#64), (9, 2#64), (18, 0#64), (19, s3), (20, s4),
        (21, s5), (22, s6), (23, s7), (24, s8), (25, s9), (26, s10)]) d6 := p6
  have ready6 := ready5.stack_log p6' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p6'.regs rfl) (gholds_lookup (n := 1) _ p6'.regs rfl) (by decide) f2
    (by simp only [LogInW])
  -- memory from open's entry to resolve's
  have mem6 (x : Nat) (stack : x < sp.toNat - 176 ∨ sp.toNat ≤ x) (errno : x < 0x80064d48 ∨ 0x80064d4c ≤ x)
      (errno2 : x < 0x80064668 ∨ 0x8006466c ≤ x) :
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p6'.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl, p5.memory,
      frameOn_writeLog _ _ _ (htifOpenLog_inside f2) x ⟨by simp only [nativeFrameBase, h2] at *; omega, trivial⟩,
      p4'.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, p3.memory,
      frameOn_writeLog _ _ _ (openRLog_inside f1) x ⟨by simp only [nativeFrameBase, h1] at *; omega,
        by simp only [errnoWindows, OutW, and_true]; omega⟩,
      p2'.memory, show writeLog d1.σ.mem [] = d1.σ.mem from rfl, p1.memory,
      frameOn_writeLog _ _ _ (libOpenLog_inside f0) x ⟨by simp only [nativeFrameBase] at *; omega, trivial⟩]
  have low6 (x : Nat) (lo : 0x8006466c ≤ x) (below : x < 0x80064d48) : (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    mem6 x (Or.inl (by unfold openDepth embedLimit Layout.sym_stack_top Layout.sym_stack_size allocHeadroom at *; omega))
      (Or.inl below) (Or.inr lo)
  have high6 (x : Nat) (lo : 0x80064d4c ≤ x) (hi : x < sp.toNat - 176) :
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := mem6 x (Or.inl hi) (Or.inr lo) (Or.inr (by omega))
  have image6 : EmbedImage d6 := image.frame ⟨fun a ka => by
    have := ka.lt
    rcases ka with ⟨lo, _⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact high6 a (by unfold heapEnd at lo; omega)
        (by unfold openDepth embedLimit Layout.sym_stack_top Layout.sym_stack_size allocHeadroom at *; omega)
    · exact low6 a (by unfold Layout.sym_environ at lo; omega) (by unfold Layout.sym_environ at hi; omega)
    · exact low6 a (by unfold Layout.sym_caml_verb_gc at lo; omega) (by unfold Layout.sym_caml_verb_gc at hi; omega)⟩
  have heapBelow : heapEnd ≤ sp.toNat - 176 := by
    unfold openDepth embedLimit Layout.sym_stack_top Layout.sym_stack_size allocHeadroom heapEnd at *; omega
  obtain ⟨blk, blkH, blkLo, blkHi⟩ := home
  have blkB := ready.heap.block_bounds (q := blk.1) (n := blk.2) blkH
  obtain ⟨d7, run7, ⟨R⟩⟩ := (resolve_ocamlrun d6 H capacity charge (nativeStack (nativeStack sp 80) 16)
    jal_800008f8_call.link path 0#64 2#64 0#64 s3 s4 s5 s6 s7 s8 s9 s10 ready6 n2
    (by rw [h2]; unfold openDepth at deep; omega) image6
    (gholds_select p6'.regs _ fun n v member => by
      simp only [resolveEntry, List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
    (by unfold read4; rw [low6 _ (by unfold Layout.sym_fs_ready; omega) (by unfold Layout.sym_fs_ready; omega),
          low6 _ (by unfold Layout.sym_fs_ready; omega) (by unfold Layout.sym_fs_ready; omega),
          low6 _ (by unfold Layout.sym_fs_ready; omega) (by unfold Layout.sym_fs_ready; omega),
          low6 _ (by unfold Layout.sym_fs_ready; omega) (by unfold Layout.sym_fs_ready; omega)]
        exact notReady)
    (fun j lo hi => by
      unfold slotUsed
      rw [high6 _ (by unfold Layout.sym_files; omega) (by unfold Layout.sym_files heapEnd at *; omega)]
      exact clear j lo hi)
    (name.transport fun k hk => high6 _ (by unfold heapStart at blkB; omega) (by omega))
    ⟨blk, blkH, blkLo, blkHi⟩
    (by
      have n3 : NativeFrame (nativeStack (nativeStack (nativeStack sp 80) 16) 80) (96 + (96 + (64 + allocHeadroom))) :=
        n2.nested (front := 80) (by decide)
      have h4 := (n3.resize (small := 96) (by unfold allocHeadroom; omega) (by decide)).stack_nat
      unfold resolveStack nativeFrameBase
      rw [h4]; unfold nativeFrameBase; rw [nat2]; unfold nativeFrameBase; rw [h2]
      unfold openDepth embedLimit Layout.sym_stack_top Layout.sym_stack_size allocHeadroom heapEnd at *; omega)
    charged).run d6 ⟨p6'.pc, rfl⟩
  sorry
end OCaml.Vm.Boot.Startup