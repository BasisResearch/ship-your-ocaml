import OCaml.Vm.Boot.Startup.ResolveHit
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! The second `resolve`: "/prog" from caml_attempt_open's 16-aligned copy. -/

/-- The 16-aligned copy of "/prog". -/
structure ProgPath (m : Std.ExtHashMap Nat (BitVec 8)) (path : BitVec 64) : Prop where
  aligned : path.toNat % 16 = 0
  region : ReadWindow path 16
  bytes : ∀ k, k ≤ 5 → (m[path.toNat + k]?).getD 0 = progByte k

theorem ProgPath.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {path : BitVec 64} (h : ProgPath m path)
    (same : ∀ k, k ≤ 5 → (m'[path.toNat + k]?).getD 0 = (m[path.toNat + k]?).getD 0) : ProgPath m' path :=
  ⟨h.aligned, h.region, fun k hk => (same k hk).trans (h.bytes k hk)⟩

theorem ProgPath.cbytes {m path} (h : ProgPath m path) : CBytes m path.toNat 5 where
  nz := fun i hi => by
    change (m[_]?).getD 0 ≠ 0
    rw [h.bytes i (by omega)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> decide
  nul := by change (m[_]?).getD 0 = 0; rw [h.bytes 5 (by decide)]; rfl
  lo := h.region.lower
  hi := by have := h.region.upper; omega
  htif := by
    rcases h.region.htif with l | r
    · exact Or.inl (by unfold Layout.sym_tohost at l; omega)
    · exact Or.inr (by unfold Layout.sym_tohost at r; omega)

theorem ProgPath.last {m path} (h : ProgPath m path) : (path + 5#64 - 1#64).toNat = path.toNat + 4 := by
  have upper := h.region.upper
  rw [BitVec.toNat_sub, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem ProgPath.window {m path} (h : ProgPath m path) {w : Nat} (hw : w ≤ 16) : ReadWindow path w := by
  refine ⟨h.region.lower, by have := h.region.upper; omega, ?_⟩
  rcases h.region.htif with l | r
  · exact Or.inl (by omega)
  · exact Or.inr r

theorem ProgPath.window0 {m path} (h : ProgPath m path) : ReadWindow path 1 := h.window (by decide)

/-- `resolve("/prog")` at its component loop: `r` cleared, the last component
starts after the leading '/'. -/
structure ResolveScannedProg (H : List (Nat × Nat)) (capacity : Nat) (spo path s0 s1 s2 s5 s6 s7 s8 s10 : BitVec 64)
    (before after : Config) : Prop where
  ready : RuntimeReady H capacity (resolveStack spo) jal_800005bc_call.link after
  pc : PCAt 0x8000062c#64 after
  regs : GHolds after.σ ([(20, 0#64), (10, 5#64), (25, path), (19, nativeStack spo 80), (2, resolveStack spo)] ++
    resolveCarried s0 s1 s2 s5 s6 s7 s8 s10)
  prog : ProgPath after.σ.mem path
  kept : ∀ x, x < nativeFrameBase spo 80 ∨ nativeFrameBase spo 80 + 48 ≤ x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

theorem resolve_scan_prog (d : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (spo path s0 s1 s2 s5 s6 s7 s8 s10 ra : BitVec 64) (ready : RuntimeReady H capacity (resolveStack spo) ra d)
    (frameO : NativeFrame spo 80)
    (regs : GHolds d.σ ([(19, nativeStack spo 80), (25, path), (2, resolveStack spo)] ++
      resolveCarried s0 s1 s2 s5 s6 s7 s8 s10))
    (prog : ProgPath d.σ.mem path) (below : path.toNat + 16 ≤ nativeFrameBase spo 80) :
    FnSummary 0x80000598#64 (fun e => e = d) (ResolveScannedProg H capacity spo path s0 s1 s2 s5 s6 s7 s8 s10 d) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have carried0 : GHolds d.σ (resolveCarried s0 s1 s2 s5 s6 s7 s8 s10) := ((gholds_append _ _).1 regs).2
  have nameOut (log : List WEntry) (inside : LogInW [⟨nativeFrameBase spo 80, spo.toNat⟩] log)
      (m : Std.ExtHashMap Nat (BitVec 8)) (h : ProgPath m path) : ProgPath (writeLog m log) path :=
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
  have name1 : ProgPath e1.σ.mem path := by
    rw [p1.memory]; exact nameOut _ (structWin_widen frameO (resolveClearLog_struct frameO)) _ prog
  obtain ⟨e2, run2, R2⟩ := (strlen_ready e1 H capacity (resolveStack spo) _ path 5 ready1 name1.cbytes
    (gholds_lookup (n := 10) _ p1.regs rfl)).run e1 ⟨p1.pc, rfl⟩
  have carried2 := gholds_carry carried1 R2.post.registers (by simp only [resolveCarried, keysG]; decide)
  have keep2 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 12, 13, 14, 15])
      (hv : gprGet e1.σ n = some v) : gprGet e2.σ n = some v := (R2.post.registers n lo hi out).trans hv
  have mem2 (x : Nat) : (e2.σ.mem[x]?).getD 0 = (e1.σ.mem[x]?).getD 0 := by
    have := R2.post.memory x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    exact this
  have name2 : ProgPath e2.σ.mem path := name1.transport fun k _ => mem2 _
  have rWin (off w : Nat) (h : off + w ≤ 48) :
      LogInW [structWin spo] [(resAt spo off, w, (0#64 : BitVec 64))] := by
    simp only [structWin, LogInW, InsideW, resAt_nat frameO (by omega : off ≤ 80), or_false, and_true]
    omega
  have rWinV (off w : Nat) (v : BitVec 64) (h : off + w ≤ 48) :
      LogInW [structWin spo] [(resAt spo off, w, v)] := by
    simp only [structWin, LogInW, InsideW, resAt_nat frameO (by omega : off ≤ 80), or_false, and_true]
    omega
  have pathOut (k : Nat) (hk : k ≤ 5) : OutW [structWin spo] (path.toNat + k) :=
    ⟨Or.inl (show path.toNat + k < nativeFrameBase spo 80 by omega), trivial⟩
  -- the last byte is not '/'
  have bLast : (e2.σ.mem[(path + 5#64 - 1#64).toNat]?).getD 0 = progByte 4 := by
    rw [name2.last]; exact name2.bytes 4 (by decide)
  have win7 : ReadWindow (path + 5#64 - 1#64) 1 := by
    have r := name2.region
    constructor <;> rw [name2.last]
    · exact Nat.le_trans r.lower (by omega)
    · have := r.upper; omega
    · rcases r.htif with l | t; exact Or.inl (by omega); exact Or.inr (by omega)
  obtain ⟨e3, run3, p3⟩ := (resolve_flag_test e2 spo path 5#64 _ (progByte 4)
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
  obtain ⟨e4, run4, p4⟩ := (resolve_flag_store e3 spo path 5#64 _ _ ready3.toLeafInput frameO p3.regs).run e3
    ⟨p3.pc, rfl⟩
  have ready4 := ready3.stack_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p4.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready3.stack)
    ((p4.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready3.raReg) (by decide)
    frameO (structWin_widen frameO (rWinV 36 4 _ (by decide)))
  have carried4 := gholds_carry carried3 (p4.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have mem4 (x : Nat) (out : OutW [structWin spo] x) :
      (e4.σ.mem[x]?).getD 0 = (e2.σ.mem[x]?).getD 0 := by
    rw [p4.memory, frameOn_writeLog _ _ _ (rWinV 36 4 _ (by decide)) x out, p3.memory]; rfl
  have name4 : ProgPath e4.σ.mem path := name2.transport fun k hk => mem4 _ (pathOut k hk)
  -- the scan for the last component starts at the end
  obtain ⟨e5, run5, p5⟩ := (resolve_back_start e4 path 5#64 _ (progByte 4)
    ready4.toLeafInput
    (gholds_select p4.regs _ fun n v member => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
    (by decide) win7 (by rw [mem4 _ (by rw [name2.last]; exact pathOut 4 (by decide))]; exact bLast)
    (by decide)).run e4 ⟨p4.pc, rfl⟩
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready4.stack)
    ((p5.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready4.raReg) (by decide)
    frameO (by simp only [LogInW])
  have carried5 := gholds_carry carried4 (p5.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have name5 : ProgPath e5.σ.mem path := by rw [p5.memory]; exact name4
  -- the scan over "prog", back to the leading '/'
  obtain ⟨e6, run6, B⟩ := back_loop_upto (L := 5) (a0 := 5#64) (ra := jal_800005bc_call.link) e5 4 (by decide)
    (name5.window (by decide)) (fun j hj => by
      unfold strByte
      rw [show path.toNat + (5 - (j + 1)) = path.toNat + (4 - j) by omega, name5.bytes (4 - j) (by omega)]
      have : 4 - j = 1 ∨ 4 - j = 2 ∨ 4 - j = 3 ∨ 4 - j = 4 := by omega
      rcases this with h | h | h | h <;> rw [h] <;> decide) e5
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
  obtain ⟨e7, run7, p7⟩ := (resolve_back_rooted e6 spo path 5#64 _ B.leaf frameO
    ⟨(gholds_lookup (n := 14) _ B.regs rfl).trans rfl, gholds_lookup (n := 11) _ B.regs rfl,
      (loopGpr 15 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 15) _ p5.regs rfl),
      gholds_lookup (n := 10) _ B.regs rfl, gholds_lookup (n := 25) _ B.regs rfl,
      (loopGpr 19 (by decide) (by decide) (by decide)).trans
        ((p5.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 19) _ p4.regs rfl)), trivial⟩
    (name5.window0) (by rw [B.memory]; exact name5.bytes 0 (by decide)) (by decide) (by decide) (by decide)).run e6
    ⟨B.pc, rfl⟩
  have ready7 := ready6.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready6.stack)
    ((p7.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready6.raReg) (by decide)
    frameO (structWin_widen frameO (rWin 44 4 (by decide)))
  have carried7 := gholds_carry carried6 (p7.toEffectPost.gpr_frame (by decide))
    (by simp only [resolveCarried, keysG]; decide)
  have mem7 (x : Nat) (out : OutW [structWin spo] x) :
      (e7.σ.mem[x]?).getD 0 = (d.σ.mem[x]?).getD 0 := by
    rw [p7.memory, frameOn_writeLog _ _ _ (rWin 44 4 (by decide)) x out, B.memory, p5.memory,
      show writeLog e4.σ.mem [] = e4.σ.mem from rfl, mem4 x out, mem2,
      p1.memory, frameOn_writeLog _ _ _ (resolveClearLog_struct frameO) x out]
  refine ⟨e7, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), {
    ready := ready7
    pc := p7.pc
    regs := (gholds_append _ _).2 ⟨⟨gholds_lookup (n := 20) _ p7.regs rfl, gholds_lookup (n := 10) _ p7.regs rfl,
      gholds_lookup (n := 25) _ p7.regs rfl, gholds_lookup (n := 19) _ p7.regs rfl, ready7.stack, trivial⟩, carried7⟩
    prog := name5.transport fun k hk => by
      rw [p7.memory, frameOn_writeLog _ _ _ (rWin 44 4 (by decide)) _ (pathOut k hk), B.memory]
    kept := fun x out => mem7 x ⟨out, trivial⟩ }⟩
end OCaml.Vm.Boot.Startup
