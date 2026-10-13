import OCaml.Vm.Boot.Startup.ResolveHit
import OCaml.Vm.Boot.Startup.StrchrHit
import OCaml.Vm.Boot.Startup.ChildHit
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
  /-- `r->slash`: "prog" has no trailing '/'. -/
  flag : read4 after.σ.mem (resAt spo 36) = [0#8, 0#8, 0#8, 0#8]

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
  have flag7 : read4 e7.σ.mem (resAt spo 36) = [0#8, 0#8, 0#8, 0#8] := by
    have h : e7.σ.mem = writeLog e3.σ.mem ((resAt spo 36, 4, slashFlag (progByte 4)) ::
        [(resAt spo 44, 4, 0#64)]) := by
      rw [p7.memory, B.memory, p5.memory, show writeLog e4.σ.mem [] = e4.σ.mem from rfl, p4.memory,
        ← writeLog_append, List.singleton_append]
    have pin := pin4_of_writeLog e3.σ.mem [] [(resAt spo 44, 4, 0#64)] (resAt spo 36)
      (slashFlag (progByte 4)) (by
        simp only [OutLRange, resAt_nat frameO (by decide : 44 ≤ 80), resAt_nat frameO (by decide : 36 ≤ 80),
          and_true]
        omega)
    rw [List.nil_append] at pin
    obtain ⟨b0, b1, b2, b3⟩ := pin
    unfold read4
    rw [h, b0, b1, b2, b3]
    decide
  refine ⟨e7, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), {
    flag := flag7
    ready := ready7
    pc := p7.pc
    regs := (gholds_append _ _).2 ⟨⟨gholds_lookup (n := 20) _ p7.regs rfl, gholds_lookup (n := 10) _ p7.regs rfl,
      gholds_lookup (n := 25) _ p7.regs rfl, gholds_lookup (n := 19) _ p7.regs rfl, ready7.stack, trivial⟩, carried7⟩
    prog := name5.transport fun k hk => by
      rw [p7.memory, frameOn_writeLog _ _ _ (rWin 44 4 (by decide)) _ (pathOut k hk), B.memory]
    kept := fun x out => mem7 x ⟨out, trivial⟩ }⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

structure StrchrHitReturned (H : List (Nat × Nat)) (capacity : Nat) (sp ra a : BitVec 64) (before after : Config) :
    Prop where
  done : StrchrHitDone a ra before after
  ready : RuntimeReady H capacity sp ra after

theorem strchr_slash_ready (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra a : BitVec 64)
    (ready : RuntimeReady H capacity sp ra c) (regs : GHolds c.σ [(11, 47#64), (10, a)])
    (aligned : a.toNat % 8 = 0) (window : ReadWindow a 8) (slash : (c.σ.mem[a.toNat]?).getD 0 = 47#8) :
    FnSummary 0x80040704#64 (fun d => d = c) (StrchrHitReturned H capacity sp ra a c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have present : GprPresent c.σ := ⟨fun n lo hi => ready.platform.gpr n lo (by omega)⟩
  obtain ⟨after, run, done⟩ := (strchr_slash_first c a ra ready.toLeafInput
    ⟨regs.1, regs.2.1, ready.raReg, trivial⟩ present aligned window slash).run c ⟨pc, rfl⟩
  have good : VsaOk startupLive after := by
    refine ⟨done.good, done.tick, fun n lo hi => done.present.get n lo (by omega), fun a ha => ?_, ?_⟩
    · rw [done.memory]; exact ready.platform.live a ha
    · rw [done.frame.regs _ (by decide) (by decide)]; exact ready.platform.htifIdle
  have gpFrame : gpr after 3 = gpr c 3 := done.frame.regs .x3 (by decide) (by decide)
  have spFrame : gprGet after.σ 2 = gprGet c.σ 2 := done.frame.regs .x2 (by decide) (by decide)
  exact ⟨after, run, done, ready.of_same_memory done.toLeafInput good
    (by rw [done.memory]; exact Vsa.Densify.MemEqv.refl _) gpFrame (spFrame.trans ready.stack)⟩

/-- "prog", one past the copy's '/', for `strchr` and `strlen`. -/
theorem ProgPath.rest_slash {m path} (h : ProgPath m path) : SlashString m (path + 1#64) 4 where
  region := by
    have r := h.region
    have nat : (path + 1#64).toNat = path.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := r.upper; omega
    refine ⟨by rw [nat]; exact Nat.le_trans r.lower (by omega), by rw [nat]; have := r.upper; omega, ?_⟩
    rw [nat]; rcases r.htif with l | t
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  free := fun j hj => by
    have nat : (path + 1#64).toNat = path.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := h.region.upper; omega
    unfold strByte
    rw [nat, show path.toNat + 1 + j = path.toNat + (j + 1) by omega, h.bytes (j + 1) (by omega)]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide
  nul := by
    have nat : (path + 1#64).toNat = path.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := h.region.upper; omega
    unfold strByte
    rw [nat, show path.toNat + 1 + 4 = path.toNat + 5 by omega, h.bytes 5 (by decide)]
    rfl

theorem ProgPath.rest_cbytes {m path} (h : ProgPath m path) : CBytes m (path.toNat + 1) 4 where
  nz := fun i hi => by
    change (m[_]?).getD 0 ≠ 0
    rw [show path.toNat + 1 + i = path.toNat + (i + 1) by omega, h.bytes (i + 1) (by omega)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide
  nul := by
    change (m[_]?).getD 0 = 0
    rw [show path.toNat + 1 + 4 = path.toNat + 5 by omega, h.bytes 5 (by decide)]; rfl
  lo := by have := h.region.lower; omega
  hi := by have := h.region.upper; omega
  htif := by
    rcases h.region.htif with l | t
    · exact Or.inl (by unfold Layout.sym_tohost at l; omega)
    · exact Or.inr (by unfold Layout.sym_tohost at t; omega)

theorem ProgPath.rest_plan {m path} (h : ProgPath m path) : StrchrPlan m (path + 1#64) 4 := by
  have nat : (path + 1#64).toNat = path.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := h.region.upper; omega
  have al := h.aligned
  exact .bytes fun j hj => by rw [nat]; omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-- `resolve("/prog")` returned `R_FILE` for slot 1. -/
structure ResolveDoneProg (H : List (Nat × Nat)) (capacity : Nat)
    (spo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 path : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, nativeStack spo 80), (25, s9), (20, s4), (19, s3), (26, s10), (24, s8), (23, s7),
    (22, s6), (21, s5), (18, s2), (9, s1), (1, ra), (8, s0), (10, 1#64)]
  ready : RuntimeReady H capacity (nativeStack spo 80) ra after
  kept : ∀ x, x < nativeFrameBase (resolveStack spo) 64 ∨ nativeFrameBase spo 80 + 48 ≤ x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  res : ∀ x, nativeFrameBase spo 80 ≤ x → (after.σ.mem[x]?).getD 0 =
    ((writeLog before.σ.mem (resolveFileLog spo 0#64 1#64 (path + 1#64) 4#64))[x]?).getD 0

theorem resolveFileLog_struct {spo d node path len : BitVec 64} (frame : NativeFrame spo 80) :
    LogInW [structWin spo] (resolveFileLog spo d node path len) := by
  simp only [resolveFileLog, structWin, LogInW, InsideW, resAt_nat frame (by decide : 4 ≤ 80),
    resAt_nat frame (by decide : 8 ≤ 80), resAt_nat frame (by decide : 16 ≤ 80), resAt_nat frame (by decide : 24 ≤ 80),
    resAt_nat frame (by decide : 0 ≤ 80), or_false, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem resolve_finish_prog (e : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (spo path node ra0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64)
    (ready : RuntimeReady H capacity (resolveStack spo) ra e) (frame : NativeFrame spo (80 + (96 + 64)))
    (regs : GHolds e.σ ([(20, 0#64), (10, 5#64), (25, path), (19, nativeStack spo 80), (2, resolveStack spo)] ++
      resolveCarried s0 s1 s2 s5 s6 s7 s8 s10))
    (prog : ProgPath e.σ.mem path) (below : path.toNat + 16 ≤ nativeFrameBase (resolveStack spo) 64)
    (slot : FsSlotOne e.σ.mem node) (nodeWin : ReadWindow node 5)
    (nodeBelow : node.toNat + 5 ≤ nativeFrameBase (resolveStack spo) 64)
    (saved : ∀ off value, (off, value) ∈ resolveSlots ra0 s3 s4 s9 →
      bytesT e.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value) (aligned0 : ra0.toNat % 4 = 0) :
    FnSummary 0x8000062c#64 (fun d => d = e)
      (ResolveDoneProg H capacity spo ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 path e) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have outer : NativeFrame (nativeStack spo 80) (96 + 64) := frame.nested (front := 80) (by decide)
  have frameR := outer.resize (small := 96) (by decide) (by decide)
  have frame64 : NativeFrame (resolveStack spo) 64 := outer.nested (front := 96) (by decide)
  have frameO := frame.resize (small := 80) (by decide) (by decide)
  have rNat := frameR.stack_nat
  have oNat := frameO.stack_nat
  have lower := frame.lower
  have hO : (nativeStack spo 80).toNat = spo.toNat - 80 := by rw [oNat]; rfl
  have hR : (resolveStack spo).toNat = spo.toNat - 176 := by
    unfold resolveStack; rw [rNat]; unfold nativeFrameBase; rw [hO]; omega
  have carried0 : GHolds e.σ (resolveCarried s0 s1 s2 s5 s6 s7 s8 s10) := ((gholds_append _ _).1 regs).2
  -- save the loop's registers; strchr(path, '/') = path
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
  have out1 (x : Nat) (h : x < nativeFrameBase (resolveStack spo) 64 ∨ nativeFrameBase spo 80 + 48 ≤ x) :
      (f1.σ.mem[x]?).getD 0 = (e.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ loopInside x ⟨by
      simp only [nativeFrameBase, hO, hR] at h ⊢; omega, trivial⟩]
  have prog1 : ProgPath f1.σ.mem path := prog.transport fun k hk => out1 _ (Or.inl (by omega))
  obtain ⟨f2, run2, ⟨hit2, ready2⟩⟩ := (strchr_slash_ready f1 H capacity (resolveStack spo) _ path ready1
    ⟨gholds_lookup (n := 11) _ p1.regs rfl, gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩
    (by have := prog1.aligned; omega) (prog1.window (by decide)) (by simpa [progByte] using prog1.bytes 0 (by decide))).run f1
    ⟨p1.pc, rfl⟩
  have keep2 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ strchrWrites)
      (hv : gprGet f1.σ n = some v) : gprGet f2.σ n = some v := (hit2.frame.gpr n lo hi out).trans hv
  have mem2 : f2.σ.mem = f1.σ.mem := hit2.memory
  have pathNat : (path + 1#64).toNat = path.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := prog.region.upper; omega
  -- an empty first component: strchr("prog", '/') = NULL
  obtain ⟨f3, run3, p3⟩ := (resolve_skip_empty f2 path _ (progByte 1) hit2.toLeafInput
    ⟨hit2.result, keep2 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p1.regs rfl),
      keep2 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p1.regs rfl), trivial⟩
    (fun h => by have := congrArg BitVec.toNat h; have := prog.region.lower; simp at *; omega)
    ((prog.rest_slash).region |> fun w => ⟨w.lower, by have := w.upper; omega,
      by rcases w.htif with l | t; exact Or.inl (by omega); exact Or.inr t⟩)
    (by rw [pathNat, mem2]; exact prog1.bytes 1 (by decide)) (by decide)).run f2 ⟨hit2.pc, rfl⟩
  have sp2 : gprGet f2.σ 2 = some (resolveStack spo) := ready2.stack
  have ready3 := ready2.stack_log p3 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p3.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans sp2)
    (gholds_lookup (n := 1) _ p3.regs rfl) (by decide) frame64 (by simp only [LogInW])
  have mem3 : f3.σ.mem = f1.σ.mem := (show f3.σ.mem = f2.σ.mem from p3.memory).trans mem2
  have prog3 : ProgPath f3.σ.mem path := by rw [mem3]; exact prog1
  obtain ⟨f4, run4, ⟨done4, ready4⟩⟩ := (strchr_ready f3 H capacity (resolveStack spo) _ (path + 1#64) 4 ready3
    ⟨gholds_lookup (n := 11) _ p3.regs rfl, gholds_lookup (n := 10) _ p3.regs rfl, trivial⟩ prog3.rest_slash
    prog3.rest_plan).run f3 ⟨p3.pc, rfl⟩
  have keep4 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ strchrWrites)
      (hv : gprGet f3.σ n = some v) : gprGet f4.σ n = some v := (done4.frame.gpr n lo hi out).trans hv
  have mem4 : f4.σ.mem = f1.σ.mem := done4.memory.trans mem3
  -- strlen("prog") = 4
  obtain ⟨f5, run5, p5⟩ := (resolve_again_strlen f4 (path + 1#64) _ done4.toLeafInput
    ⟨gholds_lookup (n := 10) _ done4.regs rfl,
      keep4 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p3.regs rfl), trivial⟩).run f4
    ⟨done4.pc, rfl⟩
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p5.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready4.stack)
    (gholds_lookup (n := 1) _ p5.regs rfl) (by decide) frame64 (by simp only [LogInW])
  have mem5 : f5.σ.mem = f1.σ.mem := (show f5.σ.mem = f4.σ.mem from p5.memory).trans mem4
  have prog5 : ProgPath f5.σ.mem path := by rw [mem5]; exact prog1
  obtain ⟨f6, run6, R6⟩ := (strlen_ready f5 H capacity (resolveStack spo) _ (path + 1#64) 4 ready5
    (by rw [pathNat]; exact prog5.rest_cbytes)
    (gholds_lookup (n := 10) _ p5.regs rfl)).run f5 ⟨p5.pc, rfl⟩
  have keep6 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out0 : n ∉ [10, 11, 12, 13, 14, 15])
      (hv : gprGet f5.σ n = some v) : gprGet f6.σ n = some v := (R6.post.registers n lo hi out0).trans hv
  have mem6 (x : Nat) : (f6.σ.mem[x]?).getD 0 = (f1.σ.mem[x]?).getD 0 := by
    have := R6.post.memory x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this
    rw [this, mem5]
  -- registers since the loop's save
  have fromLoop (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out0 : n ∉ [10, 11, 12, 13, 14, 15])
      (out1 : n ∉ [10] ++ [1]) (out2 : n ∉ strchrWrites) (out3 : n ∉ [14, 26, 15, 8, 25, 11, 10] ++ [1])
      (hv : gprGet f1.σ n = some v) : gprGet f6.σ n = some v :=
    keep6 n v lo hi out0 ((p5.toEffectPost.gpr_frame (by decide) n lo hi out1).trans
      (keep4 n v lo hi out2 ((p3.toEffectPost.gpr_frame (by decide) n lo hi out3).trans (keep2 n v lo hi out2 hv))))
  -- child(0, "prog", 4)
  obtain ⟨f7, run7, p7⟩ := (resolve_child_call f6 (path + 1#64) 4#64 0#64 _ R6.ready.toLeafInput
    ⟨R6.post.result,
      fromLoop 21 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ p1.regs rfl),
      fromLoop 23 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 23) _ p1.regs rfl),
      keep6 25 _ (by decide) (by decide) (by decide) ((p5.toEffectPost.gpr_frame (by decide) 25 (by decide) (by decide)
        (by decide)).trans (keep4 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p3.regs rfl))),
      fromLoop 20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        ((p1.toEffectPost.gpr_frame (by decide) 20 (by decide) (by decide) (by decide)).trans
          (gholds_lookup (n := 20) _ regs rfl)), trivial⟩
    (by decide) (by decide) (by decide)).run f6 ⟨R6.post.pc, rfl⟩
  have ready7 := R6.ready.stack_log p7 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p7.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans R6.ready.stack)
    (gholds_lookup (n := 1) _ p7.regs rfl) (by decide) frame64 (by simp only [LogInW])
  have toE (x : Nat) (low : x < nativeFrameBase (resolveStack spo) 64) :
      (f7.σ.mem[x]?).getD 0 = (e.σ.mem[x]?).getD 0 := by
    rw [show f7.σ.mem = f6.σ.mem from p7.memory, mem6, out1 x (Or.inl low)]
  have slotLow (x : Nat) (hx : x < slotOne + 56) : x < nativeFrameBase (resolveStack spo) 64 := by
    simp only [nativeFrameBase, hR, slotOne, Layout.sym_files, heapEnd] at *; omega
  have present7 : GprPresent f7.σ := ⟨fun n lo hi => ready7.platform.gpr n lo (by omega)⟩
  obtain ⟨a5, ha5⟩ := Option.isSome_iff_exists.mp (ready7.platform.gpr 15 (by decide) (by decide))
  have keep7 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [8, 26, 9, 12, 11, 10] ++ [1])
      (hv : gprGet f6.σ n = some v) : gprGet f7.σ n = some v :=
    (p7.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  obtain ⟨f8, run8, ⟨p8, present8⟩⟩ := (child_hit f7 (resolveStack spo) _ 4#64 1#64 47#64 (nativeStack spo 80) 0#64 1#64
    0#64 (path + 1#64) a5 node 4 ready7.toLeafInput present7 frame64
    ⟨ready7.stack, gholds_lookup (n := 8) _ p7.regs rfl, gholds_lookup (n := 9) _ p7.regs rfl,
      keep7 18 _ (by decide) (by decide) (by decide)
        (fromLoop 18 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (gholds_lookup (n := 18) _ p1.regs rfl)),
      keep7 19 _ (by decide) (by decide) (by decide)
        (fromLoop 19 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ((p1.toEffectPost.gpr_frame (by decide) 19 (by decide) (by decide) (by decide)).trans
            (gholds_lookup (n := 19) _ regs rfl))),
      gholds_lookup (n := 20) _ p7.regs rfl, gholds_lookup (n := 21) _ p7.regs rfl,
      gholds_lookup (n := 1) _ p7.regs rfl, gholds_lookup (n := 10) _ p7.regs rfl,
      gholds_lookup (n := 11) _ p7.regs rfl, gholds_lookup (n := 12) _ p7.regs rfl, ha5, trivial⟩
    (by unfold slotUsed; rw [toE _ (slotLow _ (by unfold slotOne; omega))]; rw [show Layout.sym_files + 56 = slotOne from rfl,
      slot.used]; decide)
    (by unfold slotLinked; rw [toE _ (slotLow _ (by unfold slotOne; omega))]; rw [show Layout.sym_files + 56 + 2 = slotOne + 2 from rfl,
      slot.linked]; decide)
    (by
      have same : SlotSame e.σ.mem f7.σ.mem (Layout.sym_files + 56) :=
        ⟨fun x lo hi => toE x (slotLow x (by unfold slotOne; omega))⟩
      rw [same.parent]; exact slot.parent)
    (by
      have same : SlotSame e.σ.mem f7.σ.mem (Layout.sym_files + 56) :=
        ⟨fun x lo hi => toE x (slotLow x (by unfold slotOne; omega))⟩
      rw [same.length, show Layout.sym_files + 56 = slotOne from rfl, slot.length])
    (by rw [word_observed (m := e.σ.mem) _ (fun i hi => toE _ (slotLow _ (by unfold slotOne; omega)))]
        exact slot.namePtr)
    (by decide) (by decide) nodeWin
    (by rw [show (4 : Nat) + 1 = 5 from rfl]
        exact ⟨by rw [pathNat]; have := prog.region.lower; omega, by rw [pathNat]; have := prog.region.upper; omega,
          by rw [pathNat]; rcases prog.region.htif with l | t; exact Or.inl (by omega); exact Or.inr (by omega)⟩)
    (by omega) (by rw [pathNat]; omega)
    (fun j hj => by
      rw [toE _ (by omega), toE _ (by rw [pathNat]; omega), slot.name j hj, pathNat,
        show path.toNat + 1 + j = path.toNat + (j + 1) by omega, prog.bytes (j + 1) (by omega)])).run f7
    ⟨p7.pc, rfl⟩
  have keep8 (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31)
      (out : n ∉ [2, 19, 21, 20, 8, 9, 18, 15, 10, 12, 11, 1, 13, 14]) (hv : gprGet f7.σ n = some v) :
      gprGet f8.σ n = some v := (p8.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have childInside : LogInW [⟨nativeFrameBase (resolveStack spo) 64, (resolveStack spo).toNat⟩]
      (childLog (resolveStack spo) jal_800006b0_call.link 4#64 1#64 47#64 (nativeStack spo 80) 0#64 1#64) :=
    childLog_inside frame64
  have mem8 (x : Nat) (out8 : x < nativeFrameBase (resolveStack spo) 64 ∨ (resolveStack spo).toNat ≤ x) :
      (f8.σ.mem[x]?).getD 0 = (f6.σ.mem[x]?).getD 0 := by
    rw [p8.memory, frameOn_writeLog _ _ _ childInside x ⟨out8, trivial⟩, show f7.σ.mem = f6.σ.mem from p7.memory]
  have ready8 := ready7.stack_log_written p8 (by decide) (fun n _ lo hi => present8.get n lo (by omega)) (by decide)
    (gholds_lookup (n := 2) _ p8.regs rfl) (gholds_lookup (n := 1) _ p8.regs rfl) (by decide) frame64 childInside
  -- R_FILE
  obtain ⟨f9, run9, p9⟩ := (resolve_file f8 spo (path + 1#64) 4#64 0#64 1#64 _ ready8.toLeafInput frameO
    ⟨gholds_lookup (n := 10) _ p8.regs rfl,
      keep8 22 _ (by decide) (by decide) (by decide)
        (keep7 22 _ (by decide) (by decide) (by decide)
          (fromLoop 22 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (gholds_lookup (n := 22) _ p1.regs rfl))),
      keep8 26 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 26) _ p7.regs rfl),
      gholds_lookup (n := 20) _ p8.regs rfl, gholds_lookup (n := 19) _ p8.regs rfl,
      keep8 25 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 25) _ p7.regs rfl),
      gholds_lookup (n := 8) _ p8.regs rfl, trivial⟩
    (by decide) rfl
    (by
      rw [mem8 _ (Or.inl (slotLow _ (by unfold slotOne; omega))), mem6, out1 _ (Or.inl (slotLow _ (by unfold slotOne; omega)))]
      exact slot.dirByte)).run f8 ⟨p8.pc, rfl⟩
  have ready9 := ready8.stack_log p9 (by decide) (by simp only [keysG]; decide) (by decide)
    ((p9.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready8.stack)
    ((p9.toEffectPost.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans ready8.raReg) (by decide)
    frameO (structWin_widen frameO (resolveFileLog_struct frameO))
  -- the loop frame, back to the save
  have toF1 (x : Nat) (lo : (resolveStack spo).toNat ≤ x) (hi : x < nativeFrameBase spo 80) :
      (f9.σ.mem[x]?).getD 0 = (f1.σ.mem[x]?).getD 0 := by
    rw [p9.memory, frameOn_writeLog _ _ _ (resolveFileLog_struct frameO) x ⟨Or.inl hi, trivial⟩,
      mem8 x (Or.inr lo), mem6]
  have loopSlots : resolveLoopLog (nativeStack spo 80) s0 s1 s2 s5 s6 s7 s8 s10 =
      (resolveLoopSlots s0 s1 s2 s5 s6 s7 s8 s10).map
        (fun (off, value) => (nativeFrameBase (nativeStack spo 80) 96 + off, 8, value)) :=
    frameR.word_log_slots fun off value member => by
      simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
  have frameWord (off : Nat) (h : off + 8 ≤ 96) :
      bytesT f9.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 =
        bytesT f1.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 :=
    word_observed _ fun i hi => toF1 _ (by simp only [nativeFrameBase, hO, hR] at *; omega)
      (by simp only [nativeFrameBase, hO] at *; omega)
  have savedF9 (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ resolveRestored ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) :
      bytesT f9.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value := by
    have loopRead (off : Nat) (value : BitVec 64) (hm : (off, value) ∈ resolveLoopSlots s0 s1 s2 s5 s6 s7 s8 s10) :
        bytesT f9.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value := by
      have bound : off + 8 ≤ 96 := by
        simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm; omega
      rw [frameWord off bound, p1.memory]
      exact frameR.word_log_read (fun k v hk => by
        simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
        (by simp [resolveLoopSlots]) _ hm
    have entryRead (off : Nat) (value : BitVec 64) (hm : (off, value) ∈ resolveSlots ra0 s3 s4 s9) :
        bytesT f9.σ.mem (nativeFrameBase (nativeStack spo 80) 96 + off) 8 = value := by
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
  obtain ⟨f10, run10, p10⟩ := (resolve_return f9 (nativeStack spo 80) ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 1#64 _
    ready9.toLeafInput frameR
    ⟨(p9.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans ready8.stack,
      gholds_lookup (n := 10) _ p9.regs rfl, trivial⟩ savedF9 aligned0).run f9 ⟨p9.pc, rfl⟩
  have ready10 := ready9.stack_log p10 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p10.regs rfl) (gholds_lookup (n := 1) _ p10.regs rfl) aligned0 frameR
    (by simp only [LogInW])
  have mem10 : f10.σ.mem = f9.σ.mem := p10.memory
  refine ⟨f10, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans run10)))))))), {
    pc := p10.pc
    regs := p10.regs
    ready := ready10
    kept := fun x h => ?_
    res := fun x h => ?_ }⟩
  · rw [mem10, p9.memory, frameOn_writeLog _ _ _ (resolveFileLog_struct frameO) x ⟨by
      simp only [structWin, nativeFrameBase] at h ⊢; omega, trivial⟩]
    rcases h with low | high
    · rw [mem8 x (Or.inl low), mem6, out1 x (Or.inl low)]
    · rw [mem8 x (Or.inr (by simp only [nativeFrameBase, hR] at high ⊢; omega)), mem6, out1 x (Or.inr high)]
  · rw [mem10, p9.memory]
    apply writeLog_getD_congr
    rw [mem8 x (Or.inr (by simp only [nativeFrameBase, hR] at h ⊢; omega)), mem6, p1.memory,
      frameOn_writeLog _ _ _ loopInside x ⟨Or.inr (by simp only [nativeFrameBase, hO] at h ⊢; omega), trivial⟩]
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

theorem read4_observed {m m' : Std.ExtHashMap Nat (BitVec 8)} (a : Nat)
    (same : ∀ k, k < 4 → (m'[a + k]?).getD 0 = (m[a + k]?).getD 0) : read4 m' a = read4 m a := by
  have h0 := same 0 (by decide)
  rw [Nat.add_zero] at h0
  unfold read4
  rw [h0, same 1 (by decide), same 2 (by decide), same 3 (by decide)]

/-- **The second `resolve("/prog", r)`**: `r` says `R_FILE`, slot 1. -/
structure ResolveProgDone (H : List (Nat × Nat)) (capacity : Nat)
    (spo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64) (before after : Config) : Prop where
  pc : PCAt ra after
  regs : GHolds after.σ [(2, nativeStack spo 80), (25, s9), (20, s4), (19, s3), (26, s10), (24, s8), (23, s7),
    (22, s6), (21, s5), (18, s2), (9, s1), (1, ra), (8, s0), (10, 1#64)]
  ready : RuntimeReady H capacity (nativeStack spo 80) ra after
  kept : ∀ x, x < nativeFrameBase (resolveStack spo) 64 ∨ nativeFrameBase spo 80 + 48 ≤ x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  kind : read4 after.σ.mem (resAt spo 0) = [1#8, 0#8, 0#8, 0#8]
  node : read4 after.σ.mem (resAt spo 8) = [1#8, 0#8, 0#8, 0#8]
  flag : read4 after.σ.mem (resAt spo 36) = [0#8, 0#8, 0#8, 0#8]

theorem resolve_prog (c : Config) (H : List (Nat × Nat)) (capacity : Nat)
    (spo ra path node s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : BitVec 64)
    (ready : RuntimeReady H capacity (nativeStack spo 80) ra c) (frame : NativeFrame spo (80 + (96 + 64)))
    (regs : GHolds c.σ (resolveEntry spo ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ++ [(26, s10)]))
    (fsReady : read4 c.σ.mem Layout.sym_fs_ready = [1#8, 0#8, 0#8, 0#8])
    (prog : ProgPath c.σ.mem path) (below : path.toNat + 16 ≤ nativeFrameBase (resolveStack spo) 64)
    (slot : FsSlotOne c.σ.mem node) (nodeWin : ReadWindow node 5)
    (nodeBelow : node.toNat + 5 ≤ nativeFrameBase (resolveStack spo) 64) :
    FnSummary 0x8000056c#64 (fun d => d = c) (ResolveProgDone H capacity spo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have entry := (gholds_append _ _).1 regs
  have outer : NativeFrame (nativeStack spo 80) (96 + 64) := frame.nested (front := 80) (by decide)
  have frameR := outer.resize (small := 96) (by decide) (by decide)
  have frameO := frame.resize (small := 80) (by decide) (by decide)
  have oNat := frameO.stack_nat
  have rNat := frameR.stack_nat
  have hO : (nativeStack spo 80).toNat = spo.toNat - 80 := by rw [oNat]; rfl
  have hR : (resolveStack spo).toNat = spo.toNat - 176 := by
    unfold resolveStack; rw [rNat]; unfold nativeFrameBase; rw [hO]; omega
  have lower := frame.lower
  have baseO : nativeFrameBase spo 80 = spo.toNat - 80 := rfl
  -- save, and `fs_ready` is set
  obtain ⟨d, run1, p1⟩ := (resolve_entry_ready c (nativeStack spo 80) ra s3 s4 s9 path (nativeStack spo 80)
    ready.toLeafInput frameR
    ⟨gholds_lookup (n := 2) _ entry.1 rfl, gholds_lookup (n := 19) _ entry.1 rfl,
      gholds_lookup (n := 25) _ entry.1 rfl, gholds_lookup (n := 1) _ entry.1 rfl,
      gholds_lookup (n := 20) _ entry.1 rfl, gholds_lookup (n := 10) _ entry.1 rfl,
      gholds_lookup (n := 11) _ entry.1 rfl, trivial⟩ fsReady).run c ⟨pc, rfl⟩
  have ready1 := ready.stack_log p1 (by decide) (by simp only [resolveEnteredReady, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) ready.aligned frameR
    (resolveLog_inside frameR)
  have out1 (x : Nat) (h : x < nativeFrameBase (nativeStack spo 80) 96 ∨ nativeFrameBase spo 80 ≤ x) :
      (d.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ (resolveLog_inside frameR) x ⟨by
      simp only [nativeFrameBase, hO] at h ⊢; omega, trivial⟩]
  have frame96 : nativeFrameBase (nativeStack spo 80) 96 = spo.toNat - 176 := by
    simp only [nativeFrameBase, hO]; omega
  have frame64 : nativeFrameBase (resolveStack spo) 64 = spo.toNat - 240 := by
    simp only [nativeFrameBase, hR]; omega
  have keepE (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [19, 25, 2, 15]) {v : BitVec 64}
      (hv : gprGet c.σ n = some v) : gprGet d.σ n = some v :=
    (p1.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have probD : ProgPath d.σ.mem path := prog.transport fun k hk => out1 _ (Or.inl (by omega))
  -- the scan
  obtain ⟨e, run2, B⟩ := (resolve_scan_prog d H capacity spo path s0 s1 s2 s5 s6 s7 s8 s10 _ ready1 frameO
    ((gholds_append _ _).2 ⟨⟨gholds_lookup (n := 19) _ p1.regs rfl, gholds_lookup (n := 25) _ p1.regs rfl,
        gholds_lookup (n := 2) _ p1.regs rfl, trivial⟩,
      ⟨keepE 8 (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ entry.1 rfl),
        keepE 9 (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ entry.1 rfl),
        keepE 18 (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ entry.1 rfl),
        keepE 21 (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ entry.1 rfl),
        keepE 22 (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ entry.1 rfl),
        keepE 23 (by decide) (by decide) (by decide) (gholds_lookup (n := 23) _ entry.1 rfl),
        keepE 24 (by decide) (by decide) (by decide) (gholds_lookup (n := 24) _ entry.1 rfl),
        keepE 26 (by decide) (by decide) (by decide) (gholds_lookup (n := 26) _ entry.2 rfl), trivial⟩⟩)
    probD (by omega)).run d ⟨p1.pc, rfl⟩
  have toC (x : Nat) (h : x < nativeFrameBase (nativeStack spo 80) 96) :
      (e.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 :=
    (B.kept x (Or.inl (by omega))).trans (out1 x (Or.inl h))
  have slotLow (x : Nat) (hx : x < slotOne + 56) : x < nativeFrameBase (nativeStack spo 80) 96 := by
    simp only [frame96, slotOne, Layout.sym_files, heapEnd] at *; omega
  -- strchr through the return
  obtain ⟨after, run3, C⟩ := (resolve_finish_prog e H capacity spo path node ra _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
    B.ready frame B.regs B.prog below
    (slot.transport (fun x _ hi => toC x (slotLow x hi)) (fun j hj => toC _ (by omega))) nodeWin nodeBelow
    (fun off value member => by
      have bound : off + 8 ≤ 96 := by
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega
      rw [word_observed (m := d.σ.mem) _ (fun i hi => B.kept _ (Or.inl (by simp only [frame96, baseO]; omega))),
        p1.memory]
      exact frameR.word_log_read (fun k v hk => by
        simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk; omega)
        (by simp [resolveSlots]) _ member) ready.aligned).run e ⟨B.pc, rfl⟩
  have resolved (A : Nat) (lo : nativeFrameBase spo 80 ≤ A) (k : Nat) :
      (after.σ.mem[A + k]?).getD 0 =
        ((writeLog e.σ.mem (resolveFileLog spo 0#64 1#64 (path + 1#64) 4#64))[A + k]?).getD 0 :=
    C.res _ (by omega)
  have r0 := resAt_nat frameO (off := 0) (by decide)
  have r8 := resAt_nat frameO (off := 8) (by decide)
  have r36 := resAt_nat frameO (off := 36) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), {
    pc := C.pc
    regs := C.regs
    ready := C.ready
    kept := fun x h => ?_
    kind := ?_
    node := ?_
    flag := ?_ }⟩
  · rw [C.kept x (by simp only [frame64, baseO] at h ⊢; omega)]
    rcases h with low | high
    · rw [B.kept x (Or.inl (by simp only [frame64, baseO] at low ⊢; omega)), out1 x (Or.inl (by omega))]
    · rw [B.kept x (Or.inr high), out1 x (Or.inr (by omega))]
  · obtain ⟨b0, b1, b2, b3⟩ := pin4_of_writeLog e.σ.mem
      [(resAt spo 4, 4, 0#64), (resAt spo 8, 4, 1#64), (resAt spo 16, 8, path + 1#64), (resAt spo 24, 8, 4#64)] []
      (resAt spo 0) 1#64 trivial
    rw [read4_observed _ fun k _ => resolved (resAt spo 0) (by rw [r0]; omega) k]
    unfold read4
    rw [show resolveFileLog spo 0#64 1#64 (path + 1#64) 4#64 =
      [(resAt spo 4, 4, 0#64), (resAt spo 8, 4, 1#64), (resAt spo 16, 8, path + 1#64), (resAt spo 24, 8, 4#64)] ++
        [(resAt spo 0, 4, 1#64)] from rfl, b0, b1, b2, b3]
    decide
  · obtain ⟨b0, b1, b2, b3⟩ := pin4_of_writeLog e.σ.mem [(resAt spo 4, 4, 0#64)]
      [(resAt spo 16, 8, path + 1#64), (resAt spo 24, 8, 4#64), (resAt spo 0, 4, 1#64)] (resAt spo 8) 1#64 (by
        simp only [OutLRange, resAt_nat frameO (by decide : 16 ≤ 80), resAt_nat frameO (by decide : 24 ≤ 80), r0, r8,
          and_true]
        omega)
    rw [read4_observed _ fun k _ => resolved (resAt spo 8) (by rw [r8]; omega) k]
    unfold read4
    rw [show resolveFileLog spo 0#64 1#64 (path + 1#64) 4#64 =
      [(resAt spo 4, 4, 0#64)] ++ (resAt spo 8, 4, 1#64) ::
        [(resAt spo 16, 8, path + 1#64), (resAt spo 24, 8, 4#64), (resAt spo 0, 4, 1#64)] from rfl, b0, b1, b2, b3]
    decide
  · have out : OutLRange (resolveFileLog spo 0#64 1#64 (path + 1#64) 4#64) (resAt spo 36) 4 := by
      simp only [resolveFileLog, OutLRange, resAt_nat frameO (by decide : 4 ≤ 80),
        resAt_nat frameO (by decide : 16 ≤ 80), resAt_nat frameO (by decide : 24 ≤ 80), r0, r8, r36, and_true]
      omega
    have w (k : Nat) (hk : k < 4) : (after.σ.mem[resAt spo 36 + k]?).getD 0 = (e.σ.mem[resAt spo 36 + k]?).getD 0 := by
      rw [resolved _ (by rw [r36]; omega), writeLog_out _ _ _ (outL_of_range out (by omega) (by omega))]
    rw [read4_observed _ w]
    exact B.flag
end OCaml.Vm.Boot.Startup
