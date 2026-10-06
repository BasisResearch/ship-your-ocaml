import OCaml.Vm.Boot.Startup.ResolveSteps
import OCaml.Vm.Boot.Startup.ResolveName
import OCaml.Vm.Boot.Startup.HeapFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! htif.c's first `resolve("ocamlrun", r)`: `fs_init`, then the path names no
file, so `R_NONE`. -/

/-- `resolve`'s entry registers: `r` is `_open`'s frame, then the path and the
callee-saved registers. -/
def resolveEntry (spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) : GRegs :=
  [(2, nativeStack spo 80), (1, ra), (10, path), (11, nativeStack spo 80), (8, s0), (9, s1), (18, s2), (19, s3),
    (20, s4), (21, s5), (22, s6), (23, s7), (24, s8), (25, s9)]

/-- `resolve`'s own stack pointer. -/
def resolveStack (spo : BitVec 64) : BitVec 64 := nativeStack (nativeStack spo 80) 96

/-- `resolve` after `fs_init` returns to it. -/
structure ResolveInit (H : List (Nat × Nat)) (capacity : Nat)
    (spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) (before after : Config) where
  node : BitVec 64
  pc : PCAt jal_80000594_call.link after
  regs : GHolds after.σ [(2, resolveStack spo), (19, nativeStack spo 80), (25, path), (20, s4), (8, s0), (9, s1),
    (18, s2), (21, s5), (22, s6), (23, s7), (24, s8)]
  high : ∀ n, 26 ≤ n → n ≤ 27 → gprGet after.σ n = gprGet before.σ n
  ready : RuntimeReady ((node.toNat, 5) :: H) capacity (resolveStack spo) jal_80000594_call.link after
  embed : EmbedImage after
  slot : FsSlotOne after.σ.mem node
  rest : ∀ j, 2 ≤ j → j < 64 → slotUsed after.σ.mem (Layout.sym_files + 56 * j) = 0#8
  saved : ∀ off value, (off, value) ∈ resolveSlots ra s3 s4 s9 →
    bytesT after.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value
  live : ∀ e ∈ H, ∀ x, InExt e x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  above : ∀ x, (nativeStack spo 80).toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

/-- `resolve`'s entry through `fs_init`. -/
theorem resolve_init (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) (nativeStack spo 80) ra c)
    (frame : NativeFrame spo (80 + (96 + (96 + (64 + allocHeadroom)))))
    (deep : embedLimit + (80 + (96 + (96 + (64 + allocHeadroom)))) ≤ spo.toNat)
    (image : EmbedImage c) (regs : GHolds c.σ (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
    (notReady : read4 c.σ.mem Layout.sym_fs_ready = [0#8, 0#8, 0#8, 0#8])
    (clear : ∀ j, 1 ≤ j → j < 64 → slotUsed c.σ.mem (Layout.sym_files + 56 * j) = 0#8)
    (charged : vsaChg 5 charge) :
    FnSummary 0x8000056c#64 (fun d => d = c)
      (fun after => Nonempty (ResolveInit H capacity spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have outer : NativeFrame (nativeStack spo 80) (96 + (96 + (64 + allocHeadroom))) :=
    frame.nested (front := 80) (by decide)
  have frameR := outer.resize (small := 96) (by unfold allocHeadroom; omega) (by decide)
  have frameF : NativeFrame (resolveStack spo) (96 + (64 + allocHeadroom)) := outer.nested (front := 96) (by decide)
  have outerNat := (frame.resize (small := 80) (by unfold allocHeadroom; omega) (by decide)).stack_nat
  have rNat := frameR.stack_nat
  have lower := frame.lower
  have entry (n : Nat) (v : BitVec 64) (hv : lookupG n (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) = some v) :
      gprGet c.σ n = some v := gholds_lookup _ regs hv
  -- the prologue
  obtain ⟨d1, run1, p1⟩ := (resolve_entry c (nativeStack spo 80) ra s3 s4 s9 path (nativeStack spo 80)
    ready.toLeafInput frameR (gholds_select regs _ fun n v member => by
      simp only [resolveInput, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl) notReady).run c ⟨pc, rfl⟩
  have ready1 := ready.stack_log p1 (by decide) (by simp only [resolveEntered, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) ready.aligned frameR
    (resolveLog_inside frameR)
  -- the call to fs_init
  have callRegs : GHolds d1.σ [(19, nativeStack spo 80), (25, path), (2, resolveStack spo), (15, 0#64), (20, s4),
      (10, path), (11, nativeStack spo 80)] :=
    gholds_select p1.regs _ fun n v member => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rfl
  obtain ⟨d2, run2, p2⟩ := (call_registers_summary jal_80000594_call_shape jal_80000594_call_decode d1
    (jal_80000594_call_pins ready1.image) p1.good ready1.image p1.tick p1.minstret _ callRegs
    (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run d1 ⟨p1.pc, rfl⟩
  have p2' : WriteRegistersPost [1] [] d1 jal_80000594_call.target path
      ((1, jal_80000594_call.link) :: [(19, nativeStack spo 80), (25, path), (2, resolveStack spo), (15, 0#64),
        (20, s4), (10, path), (11, nativeStack spo 80)]) d2 := p2
  have ready2 := ready1.stack_log p2' (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p2'.regs rfl) (gholds_lookup (n := 1) _ p2'.regs rfl) (by decide) frameF
    (by simp only [LogInW])
  have mem2 : d2.σ.mem = writeLog c.σ.mem (resolveLog (nativeStack spo 80) ra s3 s4 s9) :=
    (p2'.memory.trans (show writeLog d1.σ.mem [] = d1.σ.mem from rfl)).trans p1.memory
  have keep2 (x : Nat) (out : x < nativeFrameBase (nativeStack spo 80) 96 ∨ (nativeStack spo 80).toNat ≤ x) :
      (d2.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [mem2, frameOn_writeLog _ _ _ (resolveLog_inside frameR) x ⟨out, trivial⟩]
  have keepG (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out1 : n ∉ [19, 25, 2, 15]) (out2 : n ∉ [1])
      (hv : lookupG n (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) = some v) : gprGet d2.σ n = some v :=
    (p2'.toEffectPost.gpr_frame (by decide) n lo hi out2).trans
      ((p1.toEffectPost.gpr_frame (by decide) n lo hi out1).trans (entry n v hv))
  have base : nativeFrameBase (nativeStack spo 80) 96 = spo.toNat - 80 - 96 := by
    unfold nativeFrameBase; rw [outerNat]; unfold nativeFrameBase; rfl
  obtain ⟨d3, run3, ⟨F⟩⟩ := (fs_init d2 H capacity charge (resolveStack spo) jal_80000594_call.link s0 s1 s2
    (nativeStack spo 80) s4 s5 s6 s7 s8 path path ready2 frameF
    (by unfold resolveStack; rw [rNat, base]; omega)
    (image.frame (EmbedFrame.stack mem2 (resolveLog_inside frameR) (by rw [outerNat]; unfold nativeFrameBase; omega)))
    ((gholds_append _ _).2 ⟨⟨gholds_lookup (n := 2) _ p2'.regs rfl, gholds_lookup (n := 19) _ p2'.regs rfl,
        keepG 22 s6 (by decide) (by decide) (by decide) (by decide) rfl,
        keepG 23 s7 (by decide) (by decide) (by decide) (by decide) rfl,
        gholds_lookup (n := 1) _ p2'.regs rfl, keepG 8 s0 (by decide) (by decide) (by decide) (by decide) rfl,
        gholds_lookup (n := 10) _ p2'.regs rfl, trivial⟩,
      ⟨keepG 9 s1 (by decide) (by decide) (by decide) (by decide) rfl,
        keepG 18 s2 (by decide) (by decide) (by decide) (by decide) rfl,
        gholds_lookup (n := 20) _ p2'.regs rfl, keepG 21 s5 (by decide) (by decide) (by decide) (by decide) rfl,
        keepG 24 s8 (by decide) (by decide) (by decide) (by decide) rfl, gholds_lookup (n := 25) _ p2'.regs rfl,
        trivial⟩⟩)
    (fun j lo hi => by
      unfold slotUsed
      rw [keep2 _ (Or.inl (by rw [base]; unfold Layout.sym_files heapEnd at *; omega))]
      exact clear j lo hi) charged).run d2 ⟨p2'.pc, rfl⟩
  refine ⟨d3, run1.trans (run2.trans run3), ⟨{
    node := F.node
    pc := F.pc
    regs := gholds_select F.regs _ fun n v member => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    high := fun n lo hi => (F.high n lo hi).trans
      ((p2'.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)).trans
      (p1.toEffectPost.gpr_frame (by decide) n (by omega) (by omega) (by simp; omega)))
    ready := F.ready
    embed := F.embed
    slot := F.slot
    rest := F.rest
    saved := fun off value member => by
      have range : 8 ≤ off ∧ off + 8 ≤ 96 := by
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        omega
      rw [word_observed (m := d2.σ.mem) _ (fun i hi => F.above _ (by
        unfold resolveStack; rw [rNat]; omega)), mem2]
      exact frameR.word_log_read (by
        intro k v hk
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
        omega) (by simp [resolveSlots]) _ member
    live := fun e he x inside => by
      have bounds := ready.heap.block_bounds (q := e.1) (n := e.2) he
      unfold InExt at inside
      rw [F.live e he x (by unfold InExt; omega), keep2 x (Or.inl (by rw [base]; unfold heapEnd at *; omega))]
    above := fun x high => by
      rw [F.above x (by
        unfold resolveStack; rw [rNat, base]; have h' := high; rw [outerNat] at h'; unfold nativeFrameBase at h'; omega),
        keep2 x (Or.inr high)] }⟩⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-- A register frame on a register set keeps every other GPR. -/
theorem gpr_of_regFrame {before after : Config} {ws : List Nat} (bounded : ∀ m ∈ ws, 1 ≤ m ∧ m ≤ 31)
    (frame : ∀ r : Register, (∀ n ∈ ws, gprReg n ≠ r) → (∀ q ∈ noiseRegs, (q == r) = false) →
      after.σ.regs.get? r = before.σ.regs.get? r)
    (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ ws) : gpr after n = gpr before n := by
  apply gprGet_of_frame n lower upper (VsaIris.Inst.gpr_avoids_noise n (by omega) lower)
  · intro m hm
    have b := bounded m hm
    exact gprReg_beq_false m (by omega) n (by omega) b.1 lower (fun e => unwritten (e ▸ hm))
  · intro r noise outside
    exact frame r (fun m hm => by
      have ne := outside m hm
      exact fun eq => by rw [eq, beq_self_eq_true] at ne; contradiction) noise

/-- The callee-saved registers `resolve` saves in its component loop. -/
def resolveCarried (s0 s1 s2 s5 s6 s7 s8 s10 : BitVec 64) : GRegs :=
  [(8, s0), (9, s1), (18, s2), (21, s5), (22, s6), (23, s7), (24, s8), (26, s10)]

theorem OcamlrunName.last {m path} (h : OcamlrunName m path) :
    (path + 8#64 - 1#64).toNat = path.toNat + 7 := by
  have upper := h.region.upper
  rw [BitVec.toNat_sub, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

/-- `resolve` at its component loop: `r` cleared, the last component is the
whole path. -/
structure ResolveScanned (H : List (Nat × Nat)) (capacity : Nat) (spo path s0 s1 s2 s5 s6 s7 s8 s10 : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReady H capacity (resolveStack spo) jal_800005bc_call.link after
  pc : PCAt 0x8000062c#64 after
  regs : GHolds after.σ ([(20, 0#64), (10, 8#64), (25, path), (19, nativeStack spo 80), (2, resolveStack spo)] ++
    resolveCarried s0 s1 s2 s5 s6 s7 s8 s10)
  name : OcamlrunName after.σ.mem path
  kept : ∀ x, x < nativeFrameBase spo 80 ∨ spo.toNat ≤ x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem resolve_scan (d : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (spo path s0 s1 s2 s5 s6 s7 s8 s10 ra : BitVec 64) (ready : RuntimeReady H capacity (resolveStack spo) ra d)
    (frameO : NativeFrame spo 80)
    (regs : GHolds d.σ ([(19, nativeStack spo 80), (25, path), (2, resolveStack spo)] ++
      resolveCarried s0 s1 s2 s5 s6 s7 s8 s10))
    (name : OcamlrunName d.σ.mem path) (below : path.toNat + 16 ≤ nativeFrameBase spo 80) :
    FnSummary 0x80000598#64 (fun e => e = d) (ResolveScanned H capacity spo path s0 s1 s2 s5 s6 s7 s8 s10 d) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have carried0 : GHolds d.σ (resolveCarried s0 s1 s2 s5 s6 s7 s8 s10) := ((gholds_append _ _).1 regs).2
  have nameOut (log : List WEntry) (inside : LogInW [⟨nativeFrameBase spo 80, spo.toNat⟩] log)
      (m : Std.ExtHashMap Nat (BitVec 8)) (h : OcamlrunName m path) : OcamlrunName (writeLog m log) path :=
    h.transport fun k hk => by
      rw [frameOn_writeLog _ _ _ inside (path.toNat + k)
        ⟨Or.inl (show path.toNat + k < nativeFrameBase spo 80 by omega), trivial⟩]
  -- zero *r, strlen(path)
  obtain ⟨e1, run1, p1⟩ := (resolve_strlen_call d spo path ra ready.toLeafInput frameO
    ⟨gholds_lookup (n := 19) _ regs rfl, gholds_lookup (n := 25) _ regs rfl, trivial⟩).run d ⟨pc, rfl⟩
  have carried1 := gholds_carry carried0 (p1.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have sp1 : gprGet e1.σ 2 = some (resolveStack spo) :=
    (p1.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 2) _ regs rfl)
  have ready1 := ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide) sp1
    (gholds_lookup (n := 1) _ p1.regs rfl) (by decide) frameO (resolveClearLog_inside frameO)
  have name1 : OcamlrunName e1.σ.mem path := by rw [p1.memory]; exact nameOut _ (resolveClearLog_inside frameO) _ name
  obtain ⟨e2, run2, R2⟩ := (strlen_ready e1 H capacity (resolveStack spo) _ path 8 ready1 name1.cbytes
    (gholds_lookup (n := 10) _ p1.regs rfl)).run e1 ⟨p1.pc, rfl⟩
  have carried2 := gholds_carry carried1 R2.post.registers (by simp only [resolveCarried, keysG]; decide)
  have keep2 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 12, 13, 14, 15])
      (hv : gprGet e1.σ n = some v) : gprGet e2.σ n = some v := (R2.post.registers n lo hi out).trans hv
  have mem2 (x : Nat) : (e2.σ.mem[x]?).getD 0 = (e1.σ.mem[x]?).getD 0 := by
    have := R2.post.memory x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    exact this
  have name2 : OcamlrunName e2.σ.mem path := name1.transport fun k _ => mem2 _
  have rWin (off w : Nat) (h : off + w ≤ 80) :
      LogInW [⟨nativeFrameBase spo 80, spo.toNat⟩] [(resAt spo off, w, (0#64 : BitVec 64))] := by
    have lower := frameO.lower
    simp only [LogInW, InsideW, resAt_nat frameO (by omega : off ≤ 80), or_false, and_true]
    unfold nativeFrameBase at *; omega
  have rWinV (off w : Nat) (v : BitVec 64) (h : off + w ≤ 80) :
      LogInW [⟨nativeFrameBase spo 80, spo.toNat⟩] [(resAt spo off, w, v)] := by
    have lower := frameO.lower
    simp only [LogInW, InsideW, resAt_nat frameO (by omega : off ≤ 80), or_false, and_true]
    unfold nativeFrameBase at *; omega
  have pathOut (k : Nat) (hk : k ≤ 8) : OutW [⟨nativeFrameBase spo 80, spo.toNat⟩] (path.toNat + k) :=
    ⟨Or.inl (show path.toNat + k < nativeFrameBase spo 80 by omega), trivial⟩
  -- the last byte is not '/'
  have bLast : (e2.σ.mem[(path + 8#64 - 1#64).toNat]?).getD 0 = BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars 7) := by
    rw [name2.last]; exact name2.bytes 7 (by decide)
  have win7 : ReadWindow (path + 8#64 - 1#64) 1 := by
    have r := name2.region
    constructor <;> rw [name2.last]
    · exact Nat.le_trans r.lower (by omega)
    · have := r.upper; omega
    · rcases r.htif with l | t; exact Or.inl (by omega); exact Or.inr (by omega)
  obtain ⟨e3, run3, p3⟩ := (resolve_flag_test e2 spo path 8#64 _ (BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars 7))
    R2.ready.toLeafInput
    ⟨R2.post.result, keep2 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ p1.regs rfl),
      keep2 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p1.regs rfl), trivial⟩
    (by decide) win7 bLast).run e2 ⟨R2.post.pc, rfl⟩
  have sp2 : gprGet e2.σ 2 = some (resolveStack spo) := keep2 2 _ (by decide) (by decide) (by decide) sp1
  have ready3 := R2.ready.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans sp2)
    ((p3.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans R2.ready.raReg) (by decide)
    frameO (by simp only [LogInW])
  have carried3 := gholds_carry carried2 (p3.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  -- r->slash = 0
  obtain ⟨e4, run4, p4⟩ := (resolve_flag_store e3 spo path 8#64 _ _ ready3.toLeafInput frameO p3.regs).run e3
    ⟨p3.pc, rfl⟩
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p4.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready3.stack)
    ((p4.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready3.raReg) (by decide)
    frameO (rWinV 36 4 _ (by decide))
  have carried4 := gholds_carry carried3 (p4.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have mem4 (x : Nat) (out : OutW [⟨nativeFrameBase spo 80, spo.toNat⟩] x) :
      (e4.σ.mem[x]?).getD 0 = (e2.σ.mem[x]?).getD 0 := by
    rw [p4.memory, frameOn_writeLog _ _ _ (rWinV 36 4 _ (by decide)) x out, p3.memory]; rfl
  have name4 : OcamlrunName e4.σ.mem path := name2.transport fun k hk => mem4 _ (pathOut k hk)
  -- the scan for the last component starts at the end
  obtain ⟨e5, run5, p5⟩ := (resolve_back_start e4 path 8#64 _ (BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars 7))
    ready4.toLeafInput
    (gholds_select p4.regs _ fun n v member => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
    (by decide) win7 (by rw [mem4 _ (by rw [name2.last]; exact pathOut 7 (by decide))]; exact bLast)
    (by decide)).run e4 ⟨p4.pc, rfl⟩
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready4.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready4.raReg) (by decide)
    frameO (by simp only [LogInW])
  have carried5 := gholds_carry carried4 (p5.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have name5 : OcamlrunName e5.σ.mem path := by rw [p5.memory]; exact name4
  -- the scan over the eight bytes
  have noSlash : NoSlash e5.σ.mem path 8 :=
    ⟨name5.slash.region, fun j hj => (name5.slash.free j hj).2⟩
  obtain ⟨e6, run6, B⟩ := back_loop (a0 := 8#64) (ra := jal_800005bc_call.link) e5 noSlash e5
    { leaf := ready5.toLeafInput
      bound := by decide
      pc := p5.pc
      regs := ⟨gholds_lookup (n := 14) _ p5.regs rfl, gholds_lookup (n := 11) _ p5.regs rfl,
        gholds_lookup (n := 10) _ p5.regs rfl, gholds_lookup (n := 25) _ p5.regs rfl, trivial⟩
      memory := rfl
      output := rfl
      frame := fun _ _ _ => rfl
      present := ⟨fun n lo hi => ready5.platform.gpr n lo (by omega)⟩ }
  have bounded : ∀ m ∈ [13, 12, 14], 1 ≤ m ∧ m ≤ 31 := by decide
  have loopGpr := gpr_of_regFrame bounded B.frame
  have good6 : VsaOk startupLive e6 :=
    ⟨B.leaf.good, B.leaf.tick, fun n lo hi => B.present.get n lo (by omega),
      fun a ha => by rw [B.memory]; exact ready5.platform.live a ha,
      (B.frame _ (by decide) (by decide)).trans ready5.platform.htifIdle⟩
  have ready6 := ready5.of_same_memory B.leaf good6 (by rw [B.memory]; exact Vsa.Densify.MemEqv.refl _)
    (loopGpr 3 (by decide) (by decide) (by decide))
    ((loopGpr 2 (by decide) (by decide) (by decide)).trans ready5.stack)
  have carried6 := gholds_carry carried5 loopGpr (by simp only [resolveCarried, keysG]; decide)
  -- no "." or "..": clear r->last_dotdot, start at the root
  obtain ⟨e7, run7, p7⟩ := (resolve_back_exit e6 spo path 8#64 _ B.leaf frameO
    ⟨(gholds_lookup (n := 14) _ B.regs rfl).trans rfl,
      (loopGpr 15 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 15) _ p5.regs rfl),
      gholds_lookup (n := 10) _ B.regs rfl, gholds_lookup (n := 25) _ B.regs rfl,
      (loopGpr 19 (by decide) (by decide) (by decide)).trans
        ((p5.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 19) _ p4.regs rfl)), trivial⟩
    (by decide) (by decide) (by decide)).run e6 ⟨B.pc, rfl⟩
  have ready7 := ready6.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack)
    ((p7.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready6.raReg) (by decide)
    frameO (rWin 44 4 (by decide))
  have carried7 := gholds_carry carried6 (p7.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have mem7 (x : Nat) (out : OutW [⟨nativeFrameBase spo 80, spo.toNat⟩] x) :
      (e7.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 := by
    rw [p7.memory, frameOn_writeLog _ _ _ (rWin 44 4 (by decide)) x out, B.memory, p5.memory,
      show writeLog e4.σ.mem [] = e4.σ.mem from rfl, mem4 x out, mem2,
      p1.memory, frameOn_writeLog _ _ _ (resolveClearLog_inside frameO) x out]
  refine ⟨e7, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), {
    ready := ready7
    pc := p7.pc
    regs := (gholds_append _ _).2 ⟨⟨gholds_lookup (n := 20) _ p7.regs rfl, gholds_lookup (n := 10) _ p7.regs rfl,
      gholds_lookup (n := 25) _ p7.regs rfl, gholds_lookup (n := 19) _ p7.regs rfl, ready7.stack, trivial⟩, carried7⟩
    name := name5.transport fun k hk => by
      rw [p7.memory, frameOn_writeLog _ _ _ (rWin 44 4 (by decide)) _ (pathOut k hk), B.memory]
    kept := fun x out => mem7 x ⟨out, trivial⟩ }⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-- Slot 1's facts survive any change that keeps slot 1 and the name block. -/
theorem FsSlotOne.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {node : BitVec 64} (h : FsSlotOne m node)
    (slot : ∀ x, slotOne ≤ x → x < slotOne + 56 → (m'[x]?).getD 0 = (m[x]?).getD 0)
    (name : ∀ j, j ≤ 4 → (m'[node.toNat + j]?).getD 0 = (m[node.toNat + j]?).getD 0) : FsSlotOne m' node := by
  have word (off : Nat) (fits : off + 8 ≤ 56) : bytesT m' (slotOne + off) 8 = bytesT m (slotOne + off) 8 :=
    word_observed _ fun i hi => slot _ (by omega) (by omega)
  refine ⟨(slot _ (by omega) (by omega)).trans h.used, (slot _ (by omega) (by omega)).trans h.dirByte,
    (slot _ (by omega) (by omega)).trans h.linked, ?_, (word 8 (by decide)).trans h.namePtr, ?_,
    (word 24 (by decide)).trans h.data, (word 32 (by decide)).trans h.size, (word 40 (by decide)).trans h.cap,
    (slot _ (by omega) (by omega)).trans h.ro, fun j hj => (name j (by omega)).trans (h.name j hj),
    (name 4 (by decide)).trans h.nul⟩
  · have p := h.parent
    unfold slotParent read4 at *
    rw [slot (slotOne + 4) (by omega) (by omega), slot (slotOne + 4 + 1) (by omega) (by omega),
      slot (slotOne + 4 + 2) (by omega) (by omega), slot (slotOne + 4 + 3) (by omega) (by omega)]
    exact p
  · have l := h.length
    unfold slotLength at *
    rw [show slotOne + 16 = slotOne + 16 from rfl, word 16 (by decide)]
    exact l

theorem resolveNoneLog_inside {spo d path len : BitVec 64} (frame : NativeFrame spo 80) :
    LogInW [⟨nativeFrameBase spo 80, spo.toNat⟩] (resolveNoneLog spo d path len) := by
  have lower := frame.lower
  simp only [resolveNoneLog, LogInW, InsideW, resAt_nat frame (by decide : 4 ≤ 80), resAt_nat frame (by decide : 16 ≤ 80),
    resAt_nat frame (by decide : 24 ≤ 80), resAt_nat frame (by decide : 0 ≤ 80), or_false, and_true]
  unfold nativeFrameBase at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-- `resolve` returned `R_NONE` for "ocamlrun". -/
structure ResolveDone (H : List (Nat × Nat)) (capacity : Nat)
    (spo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 node path : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, nativeStack spo 80), (25, s9), (20, s4), (19, s3), (26, s10), (24, s8), (23, s7),
    (22, s6), (21, s5), (18, s2), (9, s1), (1, ra), (8, s0), (10, -1#64)]
  ready : RuntimeReady H capacity (nativeStack spo 80) ra after
  slot : FsSlotOne after.σ.mem node
  name : OcamlrunName after.σ.mem path
  kept : ∀ x, x < nativeFrameBase (resolveStack spo) 64 ∨ spo.toNat ≤ x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  none : bytesT after.σ.mem (resAt spo 16) 8 = path

theorem resolve_finish (e : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (spo path node ra0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64)
    (ready : RuntimeReady H capacity (resolveStack spo) ra e) (frame : NativeFrame spo (80 + (96 + 64)))
    (regs : GHolds e.σ ([(20, 0#64), (10, 8#64), (25, path), (19, nativeStack spo 80), (2, resolveStack spo)] ++
      resolveCarried s0 s1 s2 s5 s6 s7 s8 s10))
    (name : OcamlrunName e.σ.mem path) (below : path.toNat + 16 ≤ nativeFrameBase (resolveStack spo) 64)
    (slot : FsSlotOne e.σ.mem node) (nodeBelow : node.toNat + 5 ≤ nativeFrameBase (resolveStack spo) 64)
    (rest : ∀ j, 2 ≤ j → j < 64 → slotUsed e.σ.mem (Layout.sym_files + 56 * j) = 0#8)
    (saved : ∀ off value, (off, value) ∈ resolveSlots ra0 s3 s4 s9 →
      bytesT e.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value) (aligned0 : ra0.toNat % 4 = 0) :
    FnSummary 0x8000062c#64 (fun d => d = e)
      (ResolveDone H capacity spo ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 node path e) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have outer : NativeFrame (nativeStack spo 80) (96 + 64) := frame.nested (front := 80) (by decide)
  have frameR := outer.resize (small := 96) (by decide) (by decide)
  have frame64 : NativeFrame (resolveStack spo) 64 := outer.nested (front := 96) (by decide)
  have frameO := frame.resize (small := 80) (by decide) (by decide)
  have rNat := frameR.stack_nat
  have oNat := frameO.stack_nat
  have cNat := frame64.stack_nat
  have lower := frame.lower
  have hO : (nativeStack spo 80).toNat = spo.toNat - 80 := by rw [oNat]; rfl
  have hR : (resolveStack spo).toNat = spo.toNat - 176 := by
    unfold resolveStack; rw [rNat]; unfold nativeFrameBase; rw [hO]; omega
  have carried0 : GHolds e.σ (resolveCarried s0 s1 s2 s5 s6 s7 s8 s10) := ((gholds_append _ _).1 regs).2
  -- save the loop's registers; strchr(path, '/') = NULL
  obtain ⟨f1, run1, p1⟩ := (resolve_strchr_call e (nativeStack spo 80) path s0 s1 s2 s5 s6 s7 s8 s10 ra
    ready.toLeafInput frameR (by
      have g := (gholds_append _ _).1 regs
      exact ⟨gholds_lookup (n := 2) _ regs rfl, gholds_lookup (n := 25) _ regs rfl,
        gholds_lookup (n := 18) _ g.2 rfl, gholds_lookup (n := 21) _ g.2 rfl, gholds_lookup (n := 22) _ g.2 rfl,
        gholds_lookup (n := 23) _ g.2 rfl, gholds_lookup (n := 24) _ g.2 rfl, gholds_lookup (n := 8) _ g.2 rfl,
        gholds_lookup (n := 9) _ g.2 rfl, gholds_lookup (n := 26) _ g.2 rfl, trivial⟩)).run e ⟨pc, rfl⟩
  have loopInside : LogInW [⟨nativeFrameBase (nativeStack spo 80) 96, (nativeStack spo 80).toNat⟩]
      (resolveLoopLog (nativeStack spo 80) s0 s1 s2 s5 s6 s7 s8 s10) :=
    frameR.word_log_inside fun off value member => by
      simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
  have ready1 := ready.stack_log p1 (by decide) (by simp only [resolveLooped, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) (by decide) frameR loopInside
  have out1 (x : Nat) (h : x < nativeFrameBase (resolveStack spo) 64 ∨ spo.toNat ≤ x) :
      (f1.σ.mem[x]?).getD 0 = (e.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ loopInside x ⟨by
      simp only [nativeFrameBase, hO, hR] at h ⊢; omega, trivial⟩]
  have pathLow (k : Nat) (hk : k ≤ 8) : path.toNat + k < nativeFrameBase (resolveStack spo) 64 ∨ spo.toNat ≤ path.toNat + k :=
    Or.inl (by omega)
  have name1 : OcamlrunName f1.σ.mem path := name.transport fun k hk => out1 _ (pathLow k hk)
  obtain ⟨f2, run2, ⟨done2, ready2⟩⟩ := (strchr_ready f1 H capacity (resolveStack spo) _ path 8 ready1
    ⟨gholds_lookup (n := 11) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩ name1.slash
    name1.plan).run f1 ⟨p1.pc, rfl⟩
  have keep2 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ strchrWrites)
      (hv : gprGet f1.σ n = some v) : gprGet f2.σ n = some v := (done2.frame.gpr n lo hi out).trans hv
  -- strlen(path) = 8
  obtain ⟨f3, run3, p3⟩ := (resolve_strlen2_call f2 path _ done2.toLeafInput
    ⟨gholds_lookup (n := 10) _ done2.regs rfl,
      keep2 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p1.regs rfl), trivial⟩).run f2
    ⟨done2.pc, rfl⟩
  have ready3 := ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready2.stack)
    (gholds_lookup (n := 1) _ p3.regs rfl) (by decide) frame64 (by simp only [LogInW])
  have keep3 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out1 : n ∉ [10] ++ [1]) (out2 : n ∉ strchrWrites)
      (hv : gprGet f1.σ n = some v) : gprGet f3.σ n = some v :=
    (p3.toEffectPost.gpr_frame (by decide) n lo hi out1).trans (keep2 n v lo hi out2 hv)
  have mem3 : f3.σ.mem = f1.σ.mem := (p3.memory.trans rfl).trans done2.memory
  have name3 : OcamlrunName f3.σ.mem path := by rw [mem3]; exact name1
  obtain ⟨f4, run4, R4⟩ := (strlen_ready f3 H capacity (resolveStack spo) _ path 8 ready3 name3.cbytes
    (gholds_lookup (n := 10) _ p3.regs rfl)).run f3 ⟨p3.pc, rfl⟩
  have keep4 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out0 : n ∉ [10, 11, 12, 13, 14, 15])
      (out1 : n ∉ [10] ++ [1]) (out2 : n ∉ strchrWrites) (hv : gprGet f1.σ n = some v) : gprGet f4.σ n = some v :=
    (R4.post.registers n lo hi out0).trans (keep3 n v lo hi out1 out2 hv)
  have mem4 (x : Nat) : (f4.σ.mem[x]?).getD 0 = (f1.σ.mem[x]?).getD 0 := by
    have := R4.post.memory x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    rw [this, mem3]
  -- child(0, path, 8) = -1
  obtain ⟨f5, run5, p5⟩ := (resolve_child_call f4 path 8#64 0#64 _ R4.ready.toLeafInput
    ⟨R4.post.result,
      keep4 21 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ p1.regs rfl),
      keep4 23 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 23) _ p1.regs rfl),
      keep4 25 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p1.regs rfl),
      keep4 20 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        ((p1.toEffectPost.gpr_frame (by decide) 20 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 20) _ regs rfl)), trivial⟩
    (by decide) (by decide) (by decide)).run f4 ⟨R4.post.pc, rfl⟩
  have ready5 := R4.ready.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans R4.ready.stack)
    (gholds_lookup (n := 1) _ p5.regs rfl) (by decide) frame64 (by simp only [LogInW])
  have keep5 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [8, 26, 9, 12, 11, 10] ++ [1])
      (hv : gprGet f4.σ n = some v) : gprGet f5.σ n = some v :=
    (p5.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have memF5 (x : Nat) (h : x < nativeFrameBase (resolveStack spo) 64 ∨ spo.toNat ≤ x) :
      (f5.σ.mem[x]?).getD 0 = (e.σ.mem[x]?).getD 0 := by
    rw [p5.memory, show writeLog f4.σ.mem [] = f4.σ.mem from rfl, mem4, out1 x h]
  have slotLow (x : Nat) (hx : x < slotOne + 56) : x < nativeFrameBase (resolveStack spo) 64 := by
    simp only [nativeFrameBase, hR, slotOne, Layout.sym_files, heapEnd] at *; omega
  have slot5 : FsSlotOne f5.σ.mem node :=
    slot.transport (fun x _ hi => memF5 x (Or.inl (slotLow x hi))) (fun j hj => memF5 _ (Or.inl (by omega)))
  obtain ⟨a5, ha5⟩ := Option.isSome_iff_exists.mp (ready5.platform.gpr 15 (by decide) (by decide))
  obtain ⟨f6, run6, p6⟩ := (child_miss f5 (resolveStack spo) _ 8#64 1#64 47#64 (nativeStack spo 80) 0#64 1#64
    0#64 path 8#64 a5 ready5.toLeafInput frame64
    ⟨ready5.stack, gholds_lookup (n := 8) _ p5.regs rfl, gholds_lookup (n := 9) _ p5.regs rfl,
      keep5 18 _ (by decide) (by decide) (by decide)
        (keep4 18 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p1.regs rfl)),
      keep5 19 _ (by decide) (by decide) (by decide)
        (keep4 19 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          ((p1.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by decide)).trans
            (gholds_lookup (n := 19) _ regs rfl))),
      gholds_lookup (n := 20) _ p5.regs rfl, gholds_lookup (n := 21) _ p5.regs rfl,
      gholds_lookup (n := 1) _ p5.regs rfl, gholds_lookup (n := 10) _ p5.regs rfl,
      gholds_lookup (n := 11) _ p5.regs rfl, gholds_lookup (n := 12) _ p5.regs rfl, ha5, trivial⟩
    (fun j lo hi => by
      rcases Nat.lt_or_ge j 2 with one | two
      · have j1 : j = 1 := by omega
        subst j1
        rw [show Layout.sym_files + 56 * 1 = slotOne from rfl]
        refine .length (by unfold slotUsed; rw [slot5.used]; decide) (by unfold slotLinked; rw [slot5.linked]; decide)
          slot5.parent (by rw [slot5.length]; decide)
      · refine .unused ?_
        unfold slotUsed
        rw [memF5 _ (Or.inl (by simp only [nativeFrameBase, hR, Layout.sym_files, heapEnd] at *; omega))]
        exact rest j two hi)).run f5 ⟨p5.pc, rfl⟩
  have ready6 := ready5.stack_log p6 (by decide) (by simp only [childResult, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p6.regs rfl) (gholds_lookup (n := 1) _ p6.regs rfl) (by decide) frame64
    (childLog_inside frame64)
  -- R_NONE
  obtain ⟨f7, run7, p7⟩ := (resolve_none f6 spo path 8#64 0#64 _ ready6.toLeafInput frameO
    ⟨gholds_lookup (n := 10) _ p6.regs rfl, gholds_lookup (n := 9) _ p6.regs rfl,
      gholds_lookup (n := 20) _ p6.regs rfl, gholds_lookup (n := 19) _ p6.regs rfl,
      (p6.toEffectPost.gpr_frame (by decide) 25 (by decide) (by decide) (by decide)).trans
        (gholds_lookup (n := 25) _ p5.regs rfl),
      gholds_lookup (n := 8) _ p6.regs rfl, trivial⟩).run f6 ⟨p6.pc, rfl⟩
  have ready7 := ready6.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack)
    ((p7.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready6.raReg) (by decide)
    frameO (resolveNoneLog_inside frameO)
  have childInside : LogInW [⟨nativeFrameBase (resolveStack spo) 64, (resolveStack spo).toNat⟩]
      (childLog (resolveStack spo) jal_800006b0_call.link 8#64 1#64 47#64 (nativeStack spo 80) 0#64 1#64) :=
    childLog_inside frame64
  have mem7 (x : Nat) (out7 : x < nativeFrameBase spo 80 ∨ spo.toNat ≤ x)
      (out6 : x < nativeFrameBase (resolveStack spo) 64 ∨ (resolveStack spo).toNat ≤ x) :
      (f7.σ.mem[x]?).getD 0 = (f4.σ.mem[x]?).getD 0 := by
    rw [p7.memory, frameOn_writeLog _ _ _ (resolveNoneLog_inside frameO) x ⟨out7, trivial⟩, p6.memory,
      frameOn_writeLog _ _ _ childInside x ⟨out6, trivial⟩, p5.memory]
    rfl
  -- the frame words, from both saves
  have loopSlots : resolveLoopLog (nativeStack spo 80) s0 s1 s2 s5 s6 s7 s8 s10 =
      (resolveLoopSlots s0 s1 s2 s5 s6 s7 s8 s10).map
        (fun (off, value) => (nativeFrameBase (nativeStack spo 80) 96 + off, 8, value)) :=
    frameR.word_log_slots fun off value member => by
      simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
  have frameWord (off : Nat) (h : off + 8 ≤ 96) :
      bytesT f7.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 =
        bytesT f1.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 :=
    word_observed _ fun i hi => (mem7 _ (Or.inl (by simp only [nativeFrameBase, hO] at *; omega))
      (Or.inr (by simp only [nativeFrameBase, hO, hR] at *; omega))).trans (mem4 _)
  have savedF7 (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ resolveRestored ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) :
      bytesT f7.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value := by
    have loopRead (off : Nat) (value : BitVec 64) (hm : (off, value) ∈ resolveLoopSlots s0 s1 s2 s5 s6 s7 s8 s10) :
        bytesT f7.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value := by
      have bound : off + 8 ≤ 96 := by
        simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; omega
      rw [frameWord off bound, p1.memory]
      exact frameR.word_log_read (fun k v hk => by
        simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
        (by simp [resolveLoopSlots]) _ hm
    have entryRead (off : Nat) (value : BitVec 64) (hm : (off, value) ∈ resolveSlots ra0 s3 s4 s9) :
        bytesT f7.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value := by
      have bound : off + 8 ≤ 96 ∧ (off = 56 ∨ off = 8 ∨ off = 88 ∨ off = 48) := by
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; omega
      rw [frameWord off bound.1, p1.memory, bytesT_writeLog_out _ (by
        rw [loopSlots]
        simp only [resolveLoopSlots, List.map, OutLRange, and_true]
        omega)]
      exact saved off value hm
    simp only [resolveRestored, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | (apply loopRead; simp [resolveLoopSlots]; done)
      | (apply entryRead; simp [resolveSlots])
  -- restore and return
  obtain ⟨f8, run8, p8⟩ := (resolve_return f7 (nativeStack spo 80) ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (-1#64) _
    ready7.toLeafInput frameR
    ⟨(p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack,
      gholds_lookup (n := 10) _ p7.regs rfl, trivial⟩ savedF7 aligned0).run f7 ⟨p7.pc, rfl⟩
  have ready8 := ready7.stack_log p8 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p8.regs rfl) (gholds_lookup (n := 1) _ p8.regs rfl) aligned0 frameR
    (by simp only [LogInW])
  have mem8 : f8.σ.mem = f7.σ.mem := p8.memory
  have back (x : Nat) (h : x < nativeFrameBase (resolveStack spo) 64 ∨ spo.toNat ≤ x) :
      (f8.σ.mem[x]?).getD 0 = (e.σ.mem[x]?).getD 0 := by
    rw [mem8, mem7 x (by simp only [nativeFrameBase, hO, hR] at h ⊢; omega)
      (by simp only [nativeFrameBase, hO, hR] at h ⊢; omega), mem4, out1 x h]
  refine ⟨f8, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))), {
    pc := p8.pc
    regs := p8.regs
    ready := ready8
    slot := slot.transport (fun x _ hi => back x (Or.inl (slotLow x hi))) (fun j hj => back _ (Or.inl (by omega)))
    name := name.transport fun k hk => back _ (pathLow k hk)
    kept := back
    none := ?_ }⟩
  rw [mem8, p7.memory]
  refine word_writeLog_at _ _ 1 _ _ rfl ?_
  have lowerO := frameO.lower
  simp only [resolveNoneLog, List.drop, OutLRange, resAt_nat frameO (by decide : 16 ≤ 80),
    resAt_nat frameO (by decide : 24 ≤ 80), resAt_nat frameO (by decide : 0 ≤ 80), and_true]
  omega
end OCaml.Vm.Boot.Startup
