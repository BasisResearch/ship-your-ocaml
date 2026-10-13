import OCaml.Vm.Boot.Startup.OpenRun
import OCaml.Vm.Boot.Startup.OpenProgSteps
import OCaml.Vm.Boot.Startup.ResolveProg
import OCaml.Vm.Boot.Startup.FsUp
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `open("/prog", O_RDONLY)` once the file system is up: newlib's `open` →
`_open_r` → htif.c's `_open`, whose `resolve` finds slot 1, a file; the
first free descriptor is 3. -/

/-- The stack the second `open` uses below its caller's: its own frame,
`_open_r`'s, `_open`'s, `resolve`'s and `child`'s. -/
abbrev openProgDepth : Nat := 80 + (16 + (80 + (96 + 64)))

/-- The globals `_open` writes when it takes descriptor 3: `files[1].opens`
and `fds[3]`. -/
def takeWindows : List W :=
  [⟨Layout.sym_files + 56 + 48, Layout.sym_files + 56 + 52⟩, ⟨Layout.sym_fds + 72, Layout.sym_fds + 96⟩]

theorem htifOpenTakeLog_inside (opens : BitVec 64) : LogInW takeWindows (htifOpenTakeLog opens) := by
  simp only [htifOpenTakeLog, LogInW, InsideW, takeWindows]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

theorem takeWindows_out_pins (pin : Nat × BitVec 8) (member : pin ∈ VsaIris.Sym.allocText) :
    OutW takeWindows pin.1 := by
  have source := allocator_sources pin member
  unfold AllocatorByteSource at source
  simp only [OutW, takeWindows, and_true]
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, Layout.sym_files,
    Layout.sym_fds] at * <;> omega

theorem takeWindows_out_foot {H : List (Nat × Nat)} {a : Nat} (foot : vsaFoot H a) : OutW takeWindows a := by
  simp only [OutW, takeWindows, and_true]
  rcases foot with global | ⟨lo, _⟩
  · unfold allocGlobal InRange at global; unfold Layout.sym_files Layout.sym_fds; omega
  · unfold heapStart at lo; unfold Layout.sym_files Layout.sym_fds; omega

theorem HtifByte.out_errno {a} (h : HtifByte a) : OutW errnoWindows a := by
  simp only [OutW, errnoWindows, and_true]
  rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_print_config,
      Layout.sym_fds] at * <;> omega

/-- The log `_open` leaves in the globals for "/prog", given the open count
it read. -/
def openProgLog (m : Std.ExtHashMap Nat (BitVec 8)) : List WEntry :=
  htifOpenTakeLog (opensNext (read4 m (Layout.sym_files + 56 + 48)))

/-- `open("/prog", O_RDONLY)` returned descriptor 3. -/
structure OpenProg (H : List (Nat × Nat)) (capacity : Nat) (sp ra : BitVec 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ ([(2, sp), (1, ra), (10, 3#64)] ++ openCarried s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
  ready : RuntimeReady H capacity sp ra after
  /-- Outside the stack it used and the `errno` words, memory is the
  descriptor log over the caller's. -/
  mem : ∀ x, x < sp.toNat - openProgDepth ∨ sp.toNat ≤ x → OutW errnoWindows x →
    (after.σ.mem[x]?).getD 0 = ((writeLog before.σ.mem (openProgLog before.σ.mem))[x]?).getD 0
theorem open_prog (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra path node a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64)
    (ready : RuntimeReady H capacity sp ra c) (frame : NativeFrame sp openProgDepth)
    (regs : GHolds c.σ (libOpenInput sp ra path 0#64 a2 a3 a4 a5 a6 a7 ++ openCarried s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10))
    (reent : getenvReent c = 0x80064668#64)
    (fs : FsUp c.σ.mem node) (nodeWin : ReadWindow node 5) (nodeHigh : heapStart ≤ node.toNat)
    (nodeLow : node.toNat + 5 ≤ heapEnd) (prog : ProgPath c.σ.mem path) (pathHigh : heapStart ≤ path.toNat)
    (pathLow : path.toNat + 6 ≤ heapEnd) (pathBelow : path.toNat + 16 ≤ sp.toNat - openProgDepth) :
    FnSummary 0x80042590#64 (fun d => d = c) (OpenProg H capacity sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have entry := (gholds_append _ _).1 regs
  -- frames
  have f0 : NativeFrame sp 80 := frame.resize (by decide) (by decide)
  have n1 : NativeFrame (nativeStack sp 80) (16 + (80 + (96 + 64))) := frame.nested (front := 80) (by decide)
  have f1 : NativeFrame (nativeStack sp 80) 16 := n1.resize (by decide) (by decide)
  have n2 : NativeFrame (nativeStack (nativeStack sp 80) 16) (80 + (96 + 64)) := n1.nested (front := 16) (by decide)
  have f2 : NativeFrame (nativeStack (nativeStack sp 80) 16) 80 := n2.resize (by decide) (by decide)
  have lower : heapEnd + 336 ≤ sp.toNat := frame.lower
  have lowerN : 0x86800000 + 336 ≤ sp.toNat := frame.lower
  have pathBelow' : path.toNat + 16 ≤ sp.toNat - 336 := pathBelow
  have nat0 := f0.stack_nat
  have nat1 := f1.stack_nat
  have nat2 := f2.stack_nat
  have h1 : (nativeStack sp 80).toNat = sp.toNat - 80 := by rw [nat0]; rfl
  have h2 : (nativeStack (nativeStack sp 80) 16).toNat = sp.toNat - 96 := by
    rw [nat1]; unfold nativeFrameBase; rw [h1]; omega
  have sp2Nat : nativeFrameBase (nativeStack (nativeStack sp 80) 16) 80 = sp.toNat - 176 := by
    unfold nativeFrameBase; rw [h2]; omega
  have hRS : nativeFrameBase (resolveStack (nativeStack (nativeStack sp 80) 16)) 64 = sp.toNat - 336 := by
    have n3 : NativeFrame (nativeStack (nativeStack (nativeStack sp 80) 16) 80) (96 + 64) :=
      n2.nested (front := 80) (by decide)
    have h4 := (n3.resize (small := 96) (by decide) (by decide)).stack_nat
    unfold resolveStack
    have h3 := (n3.nested (front := 96) (by decide) : NativeFrame _ 64).lower
    unfold nativeFrameBase
    rw [h4]; unfold nativeFrameBase; rw [nat2]; unfold nativeFrameBase; rw [h2]; omega
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
  have mem6 (x : Nat) (stack : x < sp.toNat - 176 ∨ sp.toNat ≤ x) (errno : OutW errnoWindows x) :
      (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p6'.memory, show writeLog d5.σ.mem [] = d5.σ.mem from rfl, p5.memory,
      frameOn_writeLog _ _ _ (htifOpenLog_inside f2) x ⟨by simp only [nativeFrameBase, h2] at *; omega, trivial⟩,
      p4'.memory, show writeLog d3.σ.mem [] = d3.σ.mem from rfl, p3.memory,
      frameOn_writeLog _ _ _ (openRLog_inside f1) x ⟨by simp only [nativeFrameBase, h1] at *; omega, errno⟩,
      p2'.memory, show writeLog d1.σ.mem [] = d1.σ.mem from rfl, p1.memory,
      frameOn_writeLog _ _ _ (libOpenLog_inside f0) x ⟨by simp only [nativeFrameBase] at *; omega, trivial⟩]
  have low6 (x : Nat) (hi : x < heapEnd) (errno : OutW errnoWindows x) : (d6.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    mem6 x (Or.inl (by omega)) errno
  -- resolve("/prog")
  obtain ⟨d7, run7, R⟩ := (resolve_prog d6 H capacity (nativeStack (nativeStack sp 80) 16) jal_800008f8_call.link path
    node 0#64 2#64 0#64 s3 s4 s5 s6 s7 s8 s9 s10 ready6 n2
    (gholds_select p6'.regs _ fun n v member => by
      simp only [resolveEntry, List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
    (by
      rw [read4_observed (m := c.σ.mem) _ fun k hk => low6 _ (by unfold Layout.sym_fs_ready heapEnd; omega)
        (by simp only [OutW, errnoWindows, and_true, Layout.sym_fs_ready]; omega)]
      exact fs.words.ready)
    (prog.transport fun k hk => low6 _ (by omega) (by
      simp only [OutW, errnoWindows, and_true]; unfold heapStart at pathHigh; omega))
    (by rw [hRS]; omega)
    (fs.slot.transport (fun x lo hi => low6 x (by unfold slotOne Layout.sym_files heapEnd at *; omega)
        (HtifByte.out_errno (slotOne_htif lo hi)))
      (fun j hj => low6 _ (by omega) (by
        simp only [OutW, errnoWindows, and_true]; unfold heapStart at nodeHigh; omega)))
    nodeWin (by rw [hRS]; omega)).run d6 ⟨p6'.pc, rfl⟩
  have mem7 (x : Nat) (h : x < sp.toNat - 336 ∨ sp.toNat - 176 + 48 ≤ x) :
      (d7.σ.mem[x]?).getD 0 = (d6.σ.mem[x]?).getD 0 := R.kept x (by rw [hRS, sp2Nat]; exact h)
  have glob (x : Nat) (hi : x < heapEnd) (errno : OutW errnoWindows x) :
      (d7.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    (mem7 x (Or.inl (by omega))).trans (low6 x hi errno)
  have fs7 : FsUp d7.σ.mem node := fs.transport
    (fun x hx => glob x (by have := hx.bounds; unfold Layout.sym_files heapEnd at *; omega) hx.out_errno)
    (fun j hj => glob _ (by omega) (by simp only [OutW, errnoWindows, and_true]; unfold heapStart at nodeHigh; omega))
  -- _open: R_FILE, scan the descriptors
  obtain ⟨d8, run8, p8⟩ := (htif_open_file_front d7 (nativeStack (nativeStack sp 80) 16) 1#64 _ R.ready.toLeafInput f2
    ⟨gholds_lookup (n := 2) _ R.regs rfl, gholds_lookup (n := 8) _ R.regs rfl, gholds_lookup (n := 9) _ R.regs rfl,
      gholds_lookup (n := 18) _ R.regs rfl, gholds_lookup (n := 10) _ R.regs rfl, trivial⟩ R.kind R.flag).run d7
    ⟨R.pc, rfl⟩
  have ready8 := R.ready.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p8.regs rfl)
    ((p8.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans R.ready.raReg) (by decide) f2
    (by simp only [LogInW])
  have mem8 : d8.σ.mem = d7.σ.mem := p8.memory
  obtain ⟨b0, runB0, q0⟩ := (htif_open_slot_busy d8 jal_800008f8_call.link 1#64 0 [1#8, 0#8, 0#8, 0#8] ready8.toLeafInput (by decide)
    ⟨by rw [gholds_lookup (n := 14) _ p8.regs rfl]; rfl, gholds_lookup (n := 9) _ p8.regs rfl,
      gholds_lookup (n := 12) _ p8.regs rfl, gholds_lookup (n := 10) _ p8.regs rfl, trivial⟩
    (by rw [mem8]; exact fs7.words.stdin) (by decide)).run d8 ⟨p8.pc, rfl⟩
  have readyB0 := ready8.stack_log q0 (by decide) (by simp only [keysG]; decide) (by decide)
    ((q0.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready8.stack)
    ((q0.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready8.raReg) (by decide) f2
    (by simp only [LogInW])
  obtain ⟨b1, runB1, q1⟩ := (htif_open_slot_busy b0 jal_800008f8_call.link 1#64 1 [2#8, 0#8, 0#8, 0#8] readyB0.toLeafInput (by decide)
    ⟨gholds_lookup (n := 14) _ q0.regs rfl, gholds_lookup (n := 9) _ q0.regs rfl,
      gholds_lookup (n := 12) _ q0.regs rfl, gholds_lookup (n := 10) _ q0.regs rfl, trivial⟩
    (by rw [show b0.σ.mem = d7.σ.mem from q0.memory.trans mem8]; exact fs7.words.stdout) (by decide)).run b0
    ⟨q0.pc, rfl⟩
  have readyB1 := readyB0.stack_log q1 (by decide) (by simp only [keysG]; decide) (by decide)
    ((q1.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans readyB0.stack)
    ((q1.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans readyB0.raReg) (by decide) f2
    (by simp only [LogInW])
  obtain ⟨b2, runB2, q2⟩ := (htif_open_slot_busy b1 jal_800008f8_call.link 1#64 2 [3#8, 0#8, 0#8, 0#8] readyB1.toLeafInput (by decide)
    ⟨gholds_lookup (n := 14) _ q1.regs rfl, gholds_lookup (n := 9) _ q1.regs rfl,
      gholds_lookup (n := 12) _ q1.regs rfl, gholds_lookup (n := 10) _ q1.regs rfl, trivial⟩
    (by rw [show b1.σ.mem = d7.σ.mem from q1.memory.trans (q0.memory.trans mem8)]; exact fs7.words.stderr)
    (by decide)).run b1 ⟨q1.pc, rfl⟩
  have readyB2 := readyB1.stack_log q2 (by decide) (by simp only [keysG]; decide) (by decide)
    ((q2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans readyB1.stack)
    ((q2.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans readyB1.raReg) (by decide) f2
    (by simp only [LogInW])
  have memB2 : b2.σ.mem = d7.σ.mem := q2.memory.trans (q1.memory.trans (q0.memory.trans mem8))
  have keepB (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [13, 14, 9])
      (hv : gprGet d8.σ n = some v) : gprGet b2.σ n = some v :=
    (q2.toEffectPost.gpr_frame (by decide) n lo hi out).trans
      ((q1.toEffectPost.gpr_frame (by decide) n lo hi out).trans
        ((q0.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv))
  -- descriptor 3 is free: take it
  obtain ⟨e1, runT, T⟩ := (htif_open_take b2 (nativeStack (nativeStack sp 80) 16) jal_800008f8_call.link 1#64
    (read4 b2.σ.mem (Layout.sym_files + 56 + 48)) readyB2.toLeafInput f2
    ⟨gholds_lookup (n := 14) _ q2.regs rfl, gholds_lookup (n := 9) _ q2.regs rfl,
      gholds_lookup (n := 12) _ q2.regs rfl, gholds_lookup (n := 10) _ q2.regs rfl,
      keepB 11 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ p8.regs rfl),
      keepB 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ p8.regs rfl),
      keepB 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p8.regs rfl),
      keepB 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p8.regs rfl), trivial⟩
    (by rw [memB2]; exact fs7.fd3) _ rfl (by rw [memB2]; exact R.node) rfl).run b2 ⟨q2.pc, rfl⟩
  have readyT := readyB2.stack_log T (by decide) (by simp only [keysG]; decide) (by decide)
    ((T.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans readyB2.stack)
    ((T.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans readyB2.raReg) (by decide) f2
    (by simp only [LogInW])
  obtain ⟨e2, runS, S⟩ := (htif_open_stores e1 jal_800008f8_call.link _ readyT.toLeafInput
    ⟨gholds_lookup (n := 13) _ T.regs rfl, gholds_lookup (n := 12) _ T.regs rfl, gholds_lookup (n := 14) _ T.regs rfl,
      gholds_lookup (n := 10) _ T.regs rfl, gholds_lookup (n := 8) _ T.regs rfl, gholds_lookup (n := 11) _ T.regs rfl,
      trivial⟩).run e1 ⟨T.pc, rfl⟩
  have readyS := readyT.window_log S (by decide) (by simp only [keysG]; decide) (by decide)
    ((S.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans readyT.stack)
    ((S.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans readyT.raReg) (by decide)
    (htifOpenTakeLog_inside _) takeWindows_out_pins
    ⟨Or.inl (by decide), Or.inl (by decide), trivial⟩ ⟨Or.inl (by decide), Or.inl (by decide), trivial⟩
    (fun a foot => takeWindows_out_foot foot)
  have memS : e2.σ.mem = writeLog b2.σ.mem (htifOpenTakeLog (opensNext (read4 b2.σ.mem (Layout.sym_files + 56 + 48)))) :=
    S.memory.trans (by rw [show e1.σ.mem = b2.σ.mem from T.memory])
  -- the stack below the globals, unchanged since resolve returned
  have stackS (x : Nat) (hx : heapEnd ≤ x) : (e2.σ.mem[x]?).getD 0 = (d7.σ.mem[x]?).getD 0 := by
    rw [memS, frameOn_writeLog _ _ _ (htifOpenTakeLog_inside _) x (by
      simp only [OutW, takeWindows, and_true, Layout.sym_files, Layout.sym_fds, heapEnd] at *; omega), memB2]
  -- the frames above resolve's, unchanged since they were saved
  have back5 (x : Nat) (lo : sp.toNat - 128 ≤ x) : (e2.σ.mem[x]?).getD 0 = (d5.σ.mem[x]?).getD 0 := by
    have hx : heapEnd ≤ x := by unfold heapEnd; omega
    have hy : sp.toNat - 336 < x := by omega
    rw [stackS x hx, mem7 x (Or.inr (by omega)), p6'.memory]
    rfl
  have back3 (x : Nat) (lo : sp.toNat - 96 ≤ x) : (e2.σ.mem[x]?).getD 0 = (d3.σ.mem[x]?).getD 0 := by
    have out : OutW [⟨nativeFrameBase (nativeStack (nativeStack sp 80) 16) 80,
        (nativeStack (nativeStack sp 80) 16).toNat⟩] x := ⟨Or.inr (by rw [h2]; omega), trivial⟩
    rw [back5 x (by omega), p5.memory, frameOn_writeLog _ _ _ (htifOpenLog_inside f2) x out, p4'.memory]
    rfl
  have back1 (x : Nat) (lo : sp.toNat - 80 ≤ x) : (e2.σ.mem[x]?).getD 0 = (d1.σ.mem[x]?).getD 0 := by
    have out : OutW (⟨nativeFrameBase (nativeStack sp 80) 16, (nativeStack sp 80).toNat⟩ :: errnoWindows) x :=
      ⟨Or.inr (by rw [h1]; omega), by
        simp only [OutW, errnoWindows, and_true]; unfold heapEnd at lower; omega⟩
    rw [back3 x (by omega), p3.memory, frameOn_writeLog _ _ _ (openRLog_inside f1) x out, p2'.memory]
    rfl
  -- _open's saved words, from its prologue through resolve
  have saved9 (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ [(64, getenvReent c), (72, jal_8004d7cc_call.link), (48, s2), (56, s1)]) :
      bytesT e2.σ.mem (nativeFrameBase (nativeStack (nativeStack sp 80) 16) 80 + off) 8 = value := by
    have range : 48 ≤ off ∧ off + 8 ≤ 80 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
    rw [word_observed (m' := e2.σ.mem) (m := d5.σ.mem) (nativeFrameBase (nativeStack (nativeStack sp 80) 16) 80 + off)
        (fun i hi => back5 _ (by rw [sp2Nat]; omega)), p5.memory, htifOpenLog, writeLog_append,
      bytesT_writeLog_out _ (by
        have lower := f2.lower
        simp only [OutLRange, resAt_nat f2 (by decide : 4 ≤ 80), resAt_nat f2 (by decide : 36 ≤ 80), and_true]
        simp only [nativeFrameBase] at *
        omega),
      show ∀ (sp' : BitVec 64) (a b : List (Nat × BitVec 64)), nativeWordLog sp' 80 a ++ nativeWordLog sp' 80 b =
        nativeWordLog sp' 80 (a ++ b) from fun _ _ _ => (List.map_append ..).symm]
    apply f2.word_log_read
    · intro k v hk
      simp only [List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      simp only [List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  obtain ⟨e3, runU, U⟩ := (htif_open_succeed e2 (nativeStack (nativeStack sp 80) 16) jal_8004d7cc_call.link
    (getenvReent c) s1 s2 3#64 _ readyS.toLeafInput f2
    ⟨(S.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 9) _ T.regs rfl), readyS.stack, trivial⟩ saved9 (by decide)).run e2 ⟨S.pc, rfl⟩
  have readyU := readyS.stack_log U (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ U.regs rfl) (gholds_lookup (n := 1) _ U.regs rfl) (by decide) f1
    (by simp only [LogInW])
  have memU : e3.σ.mem = e2.σ.mem := U.memory
  -- _open_r's saved words
  have saved10 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(8, jal_800425d4_call.link), (0, s0)]) :
      bytesT e3.σ.mem (nativeFrameBase (nativeStack sp 80) 16 + off) 8 = value := by
    have range : off + 8 ≤ 16 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
    have base1 : nativeFrameBase (nativeStack sp 80) 16 = sp.toNat - 96 := by unfold nativeFrameBase; rw [h1]; omega
    rw [word_observed (m' := e3.σ.mem) (m := d3.σ.mem) (nativeFrameBase (nativeStack sp 80) 16 + off) (fun i hi => by
      rw [memU]; exact back3 _ (by rw [base1]; omega)), p3.memory, openRLog, writeLog_append, bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; rw [base1]; omega)]
    exact f1.word_log_read (by
      intro k v hk; simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
      (by simp) _ (by
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member ⊢
        rcases member with h | h <;> simp [h])
  obtain ⟨e4, runV, V⟩ := (open_r_succeed e3 (nativeStack sp 80) jal_800425d4_call.link s0 3#64 _ readyU.toLeafInput f1
    ⟨gholds_lookup (n := 10) _ U.regs rfl, gholds_lookup (n := 2) _ U.regs rfl, trivial⟩ (by decide) saved10
    (by decide)).run e3 ⟨U.pc, rfl⟩
  have readyV := readyU.stack_log V (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ V.regs rfl) (gholds_lookup (n := 1) _ V.regs rfl) (by decide) f0
    (by simp only [LogInW])
  have memV : e4.σ.mem = e2.σ.mem := V.memory.trans memU
  -- open: return 3
  have saved11 : bytesT e4.σ.mem (nativeFrameBase sp 80 + 24) 8 = ra := by
    rw [word_observed (m' := e4.σ.mem) (m := d1.σ.mem) (nativeFrameBase sp 80 + 24) (fun i hi => by
      rw [memV]; exact back1 _ (by simp only [nativeFrameBase]; omega)), p1.memory]
    exact f0.word_log_read (by
      intro k v hk; simp only [libOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
      (by simp [libOpenSlots]) _ (by simp [libOpenSlots])
  obtain ⟨e5, runW, W⟩ := (lib_open_return e4 sp ra 3#64 _ readyV.toLeafInput f0
    ⟨gholds_lookup (n := 2) _ V.regs rfl, gholds_lookup (n := 10) _ V.regs rfl, trivial⟩ saved11
    ready.aligned).run e4 ⟨V.pc, rfl⟩
  have kAfter (n : Nat) (v : BitVec 64) (hn : n ∈ [19, 20, 21, 22, 23, 24, 25, 26]) (hv : gprGet d7.σ n = some v) :
      gprGet e5.σ n = some v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    have lo : 1 ≤ n := by omega
    have hi : n ≤ 31 := by omega
    exact (W.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
      ((V.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
        ((U.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          ((S.toEffectPost.gpr_frame (by decide) n lo hi (by simp)).trans
            ((T.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans
              (keepB n v lo hi (by simp; omega)
                ((p8.toEffectPost.gpr_frame (by decide) n lo hi (by simp; omega)).trans hv))))))
  have opens : read4 b2.σ.mem (Layout.sym_files + 56 + 48) = read4 c.σ.mem (Layout.sym_files + 56 + 48) := by
    rw [memB2]
    exact read4_observed _ fun k hk => glob _ (by unfold Layout.sym_files heapEnd; omega)
      (by simp only [OutW, errnoWindows, and_true, Layout.sym_files]; omega)
  refine ⟨e5, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (runB0.trans (runB1.trans (runB2.trans (runT.trans (runS.trans (runU.trans (runV.trans runW)))))))))))))), {
    pc := W.pc
    regs := (gholds_append _ _).2 ⟨W.regs,
      (W.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 8) _ V.regs rfl),
      (W.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
        ((V.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 9) _ U.regs rfl)),
      (W.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
        ((V.toEffectPost.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 18) _ U.regs rfl)),
      kAfter 19 _ (by decide) (gholds_lookup (n := 19) _ R.regs rfl),
      kAfter 20 _ (by decide) (gholds_lookup (n := 20) _ R.regs rfl),
      kAfter 21 _ (by decide) (gholds_lookup (n := 21) _ R.regs rfl),
      kAfter 22 _ (by decide) (gholds_lookup (n := 22) _ R.regs rfl),
      kAfter 23 _ (by decide) (gholds_lookup (n := 23) _ R.regs rfl),
      kAfter 24 _ (by decide) (gholds_lookup (n := 24) _ R.regs rfl),
      kAfter 25 _ (by decide) (gholds_lookup (n := 25) _ R.regs rfl),
      kAfter 26 _ (by decide) (gholds_lookup (n := 26) _ R.regs rfl), trivial⟩
    ready := readyV.stack_log W (by decide) (by simp only [keysG]; decide) (by decide)
      (gholds_lookup (n := 2) _ W.regs rfl) (gholds_lookup (n := 1) _ W.regs rfl) ready.aligned f0
      (by simp only [LogInW])
    mem := fun x stack errno => by
      rw [show e5.σ.mem = e4.σ.mem from W.memory, memV, memS, opens, openProgLog]
      apply writeLog_getD_congr
      unfold openProgDepth at stack
      rw [memB2, mem7 x (by omega), mem6 x (by omega) errno] }⟩
end OCaml.Vm.Boot.Startup
