import OCaml.Vm.Primitives.Uncaught.Sinit
import OCaml.Vm.Primitives.Uncaught.GlobalStdioInit
import OCaml.Vm.Primitives.Uncaught.RetargetLockInit
import OCaml.Vm.Primitives.Uncaught.StdioState
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.MemsetBytes
import OCaml.Vm.Boot.Startup.MemsetTail

/-!
# newlib's stdio initialization (`__sinit`)

On the first stdio call (`fprintf(stderr, …)` on the fatal path) `__sinit`
installs `cleanup_stdio` as `reent->__cleanup` and, with no
`__stdio_exit_handler` yet, runs `global_stdio_init`: `stdio_exit_handler`
installed, and stdin, stdout and stderr set up (flags, descriptor, cookie,
the four I/O functions, `_mbstate` cleared by `memset(…, 0, 8)`).
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioInit
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives VsaIris.Inst
open OCaml.Vm.Boot.Startup (memsetBytesLog MemsetBytesInput memset_bytes memsetPrefix_code)

private theorem zero_imm : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

local macro "memset8_nf" : tactic =>
  `(tactic| simp only [OCaml.Vm.Boot.Startup.memsetprefix_line_8004276c, OCaml.Vm.Boot.Startup.memsetprefix_line_80042770, OCaml.Vm.Boot.Startup.memsettail_line_800427a8,
    OCaml.Vm.Boot.Startup.memsettail_line_800427ac, OCaml.Vm.Boot.Startup.memsettail_line_800427b0, OCaml.Vm.Boot.Startup.memsettail_line_800427b4, memsetX276cTSeg, memsetX27a8Seg,
    evalBlocksPC, chainEndPC, endPCB, nextPC0, ldsRunM, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append,
    runGM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, imm20Of, Option.getD_some, BitVec.add_zero,
    Nat.reduceEqDiff, ite_true, ite_false, tgtPCT, zero_imm])

/-- `memset(p, 0, 8)`'s entry and dispatch: `n < 16`, so a computed jump into
the byte-store ladder at its eighth entry. -/
theorem memset8_dispatch (c : Config) (p ra : BitVec 64) (h : LeafInput ra c)
    (a0 : gprGet c.σ 10 = some p) (a2 : gprGet c.σ 12 = some 8#64) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [5, 6, 13, 14] c ra 0x800427d8#64 [(14, p)]) := by
  have input : BlockInput (memsetX276cTSeg ++ memsetX27a8Seg) 0x8004276c#64 [(10, p), (12, 8#64)] [] c := {
    good := h.good
    minstret := h.minstret
    regs := ⟨a0, a2, trivial⟩
    keys := by change KeysOK [10, 12]; decide
    shape := by change ChainOK _ [10, 12] _; decide
    tick := h.tick
    facts := by
      have code := memsetPrefix_code h.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals memset8_nf
      all_goals decide }
  apply boundary_of_blocks h (block_summary _ _ _ _ _ input)
  · rfl
  · memset8_nf; decide
  · intro σ pins
    exact ⟨gholds_lookup _ pins (by memset8_nf), trivial⟩
  · decide
  · decide

/-- **`memset(p, 0, 8)`**: the eight bytes at `p` cleared, `p` returned. -/
theorem memset8 (c : Config) (p ra : BitVec 64) (h : LeafInput ra c)
    (a0 : gprGet c.σ 10 = some p) (a1 : gprGet c.σ 11 = some 0#64) (a2 : gprGet c.σ 12 = some 8#64)
    (windows : ∀ i : Nat, i < 8 → WriteWindow (p + BitVec.ofNat 64 i) 1)
    (outside : ImageOutside (memsetBytesLog p)) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (EffectPost [5, 6, 13, 14] (writeLog c.σ.mem (memsetBytesLog p)) c ra p) := by
  apply summary_bind (memset8_dispatch c p ra h a0 a2) (fun _ q => q.pc)
  intro d q
  have input : MemsetBytesInput p p ra d :=
    { toLeafInput := q.toLeafInput
      destination := (q.frame .x10 (by decide) (by decide)).trans a0
      cursor := gholds_lookup _ q.regs rfl
      zero := (q.frame .x11 (by decide) (by decide)).trans a1
      windows := windows
      outside := outside }
  apply (memset_bytes d p p ra input).weaken (fun _ e => e)
  intro e post
  refine { post.toEffectPost with memory := ?_, output := ?_, frame := ?_, kept := q.kept.trans post.kept }
  · rw [post.memory, q.memory]
  · exact post.output.trans q.output
  · intro r out noise
    exact (post.frame r (by simp) noise).trans (q.frame r out noise)

/-- Eight byte-wide windows of a global above `.rodata` and the HTIF registers. -/
theorem bytes_windows {p : BitVec 64} (lo : Layout.sym_tohost + 16 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x100000000) :
    ∀ i : Nat, i < 8 → WriteWindow (p + BitVec.ofNat 64 i) 1 := by
  intro i hi'
  have t : 0x80000000 ≤ Layout.sym_tohost := by decide
  have e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e]; omega, by omega⟩

theorem bytes_outside {p : BitVec 64} (lo : 0x80061fb0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x100000000) :
    ImageOutside (memsetBytesLog p) := by
  apply StdioFrame.imageOutside_above
  intro e he
  have n (k : Nat) (hk : k < 8) : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [OCaml.Vm.Boot.Startup.memsetBytesLog, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [n 7 (by decide), n 6 (by decide), n 5 (by decide), n 4 (by decide), n 3 (by decide),
      n 2 (by decide), n 1 (by decide)] <;> omega

open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gpr_some_of)
open OCaml.Vm.Boot.Startup (NativeFrame GprsSame)
open OCaml.Vm.Primitives.Uncaught.StdioClose (frame_nat frame_word frame_outside)
open OCaml.Vm.Primitives.Uncaught.StdioFlush (stdinFile)

/-- `__sf`'s I/O functions as `global_stdio_init` holds them in `s1`–`s4`:
`__sclose`, `__sseek`, `__swrite`, `__sread`; `s0 = __sf`. -/
def fnsR (n : Nat) : BitVec 64 :=
  if n = 9 then 0x80040184#64 else if n = 18 then 0x80040120#64 else if n = 19 then 0x80040098#64
  else if n = 20 then 0x80040034#64 else stdinFile

/-- `global_stdio_init`'s stores: its saves and the handler, then per stream
the flags/descriptor word and cleared fields, `_mbstate` (`memset`), the
cookie and the I/O functions. -/
def initLog (R : Nat → BitVec 64) : List WEntry :=
  GlobalStdioInit.stdinLog R [] ++ memsetBytesLog 2147994336#64 ++ GlobalStdioInit.stdinFnsLog fnsR [] ++
    GlobalStdioInit.stdoutLog fnsR [] ++ memsetBytesLog 2147994520#64 ++ GlobalStdioInit.stdoutFnsLog fnsR [] ++
    GlobalStdioInit.stderrLog fnsR [] ++ memsetBytesLog 2147994704#64 ++ GlobalStdioInit.stderrFnsLog fnsR []

/-- A direct call from a block: `ra` becomes the link, nothing else changes. -/
theorem call_from {c : Config} {call : CallInstr} (shape : CallShape call) (decode : CallDecode call)
    (pins : CallPins call c) (good : GoodState c.σ) (image : ExecutableImage c) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w) {v : BitVec 64} (a0 : gprGet c.σ 10 = some v) :
    FnSummary call.pc (fun d => d = c) (RegistersPost [1] c.σ.mem c call.target v [(1, call.link), (10, v)]) :=
  call_registers_summary shape decode c pins good image tick minstret [(10, v)] ⟨a0, trivial⟩
    (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl

/-- **`jal memset` with `(p, 0, 8)`**, back at the link. -/
theorem memset_call {c : Config} {call : CallInstr} {p : BitVec 64} (shape : CallShape call)
    (decode : CallDecode call) (pins : CallPins call c) (target : call.target = 0x8004276c#64)
    (al : call.link.toNat % 4 = 0) (good : GoodState c.σ) (image : ExecutableImage c) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (a0 : gprGet c.σ 10 = some p) (a1 : gprGet c.σ 11 = some 0#64) (a2 : gprGet c.σ 12 = some 8#64)
    (lo : Layout.sym_tohost + 16 ≤ p.toNat) (ro : 0x80061fb0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x100000000) :
    FnSummary call.pc (fun d => d = c)
      (fun d => EffectPost ([1] ++ [5, 6, 13, 14]) (writeLog c.σ.mem (memsetBytesLog p)) c call.link p d ∧
        gprGet d.σ 1 = some call.link) := by
  apply summary_bind (call_from shape decode pins good image tick minstret a0) (fun _ q => q.pc)
  intro d q
  rw [target]
  have k (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1]) : gprGet d.σ n = gprGet c.σ n :=
    q.toEffectPost.gpr_frame (by decide) n lo hi out
  apply (memset8 d p call.link ⟨q.good, q.image, q.minstret, gholds_lookup (n := 1) _ q.regs rfl, al, q.tick⟩
    (gholds_lookup (n := 10) _ q.regs rfl) ((k 11 (by decide) (by decide) (by decide)).trans a1)
    ((k 12 (by decide) (by decide) (by decide)).trans a2) (bytes_windows lo hi) (bytes_outside ro hi)).weaken
    (fun _ e => e)
  intro e m
  have t := q.toEffectPost.trans m
  rw [q.memory] at t
  exact ⟨t, (m.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 1) _ q.regs rfl)⟩

/-- **A `jal` to a `ret` leaf** (the `__retarget_lock_*` stubs), back at the link. -/
theorem retLeaf_call {c : Config} {call : CallInstr} {t v : BitVec 64} (shape : CallShape call)
    (decode : CallDecode call) (pins : CallPins call c) (target : call.target = t)
    (leaf : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ [(1, R 1), (10, R 10)] →
      FnSummary t (fun d => d = c) (WriteRegistersPost [] [] c (R 1) (R 10) [(1, R 1), (10, R 10)]))
    (al : call.link.toNat % 4 = 0) (good : GoodState c.σ) (image : ExecutableImage c) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w) (a0 : gprGet c.σ 10 = some v) :
    FnSummary call.pc (fun d => d = c)
      (fun d => EffectPost ([1] ++ []) c.σ.mem c call.link v d ∧ gprGet d.σ 1 = some call.link) := by
  apply summary_bind (call_from shape decode pins good image tick minstret a0) (fun _ q => q.pc)
  intro d q
  rw [target]
  have l1 := gholds_lookup (n := 1) _ q.regs rfl
  have l10 := gholds_lookup (n := 10) _ q.regs rfl
  apply (leaf d (regsAt d) (by rw [regsAt_of l1]; exact ⟨q.good, q.image, q.minstret, l1, al, q.tick⟩)
    ⟨gpr_some (gpr_some_of l1), gpr_some (gpr_some_of l10), trivial⟩).weaken (fun _ e => e)
  intro e l
  have t := q.toEffectPost.trans l.toEffectPost
  rw [regsAt_of l1, regsAt_of l10, Named.NamedValue.wl_nil, q.memory] at t
  have r := gholds_lookup (n := 1) _ l.regs rfl
  rw [regsAt_of l1] at r
  exact ⟨t, r⟩

/-- **`jal __retarget_lock_init_recursive`**, back at the link. -/
theorem lockInit_call {c : Config} {call : CallInstr} {v : BitVec 64} (shape : CallShape call)
    (decode : CallDecode call) (pins : CallPins call c) (target : call.target = 0x80042528#64)
    (al : call.link.toNat % 4 = 0) (good : GoodState c.σ) (image : ExecutableImage c) (tick : c.tick < 2)
    (minstret : ∃ w, c.σ.regs.get? Register.minstret = some w) (a0 : gprGet c.σ 10 = some v) :
    FnSummary call.pc (fun d => d = c)
      (fun d => EffectPost ([1] ++ []) c.σ.mem c call.link v d ∧ gprGet d.σ 1 = some call.link) :=
  retLeaf_call shape decode pins target RetargetLockInit.leaf_fast al good image tick minstret a0

/-- Everything `global_stdio_init` stores after its own saves: the
standard streams, within `__sf`. -/
def streamsLog : List WEntry :=
  memsetBytesLog 2147994336#64 ++ GlobalStdioInit.stdinFnsLog fnsR [] ++ GlobalStdioInit.stdoutLog fnsR [] ++
    memsetBytesLog 2147994520#64 ++ GlobalStdioInit.stdoutFnsLog fnsR [] ++ GlobalStdioInit.stderrLog fnsR [] ++
    memsetBytesLog 2147994704#64 ++ GlobalStdioInit.stderrFnsLog fnsR []

theorem streamsLog_within : ExitPath.LogWithin streamsLog 0x8007ca38 0x8007cd00 := by
  unfold ExitPath.LogWithin; decide

theorem initLog_eq (R : Nat → BitVec 64) : initLog R = GlobalStdioInit.stdinLog R [] ++ streamsLog := by
  simp only [initLog, streamsLog, List.append_assoc]

/-- The registers `global_stdio_init` writes (its saved ones restored). -/
def initWrites : List Nat := [1, 2, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20]

/-- The prefix of `streamsLog` before stderr's I/O functions. -/
def streamsPre : List WEntry :=
  memsetBytesLog 2147994336#64 ++ GlobalStdioInit.stdinFnsLog fnsR [] ++ GlobalStdioInit.stdoutLog fnsR [] ++
    memsetBytesLog 2147994520#64 ++ GlobalStdioInit.stdoutFnsLog fnsR [] ++ GlobalStdioInit.stderrLog fnsR [] ++
    memsetBytesLog 2147994704#64

theorem streamsPre_within : ExitPath.LogWithin streamsPre 0x8007ca38 0x8007cd00 := by
  unfold ExitPath.LogWithin; decide

/-- **`global_stdio_init`** (first stdio use): `stdio_exit_handler`
installed; stdin, stdout, stderr set up; back at `ra` with `sp` and `s0`–`s4`
restored. -/
theorem global_stdio_init_run {c : Config} {ra sp s0 s1 s2 s3 s4 : BitVec 64} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (s1r : gprGet c.σ 9 = some s1)
    (s2r : gprGet c.σ 18 = some s2) (s3r : gprGet c.σ 19 = some s3) (s4r : gprGet c.σ 20 = some s4)
    (a0r : (gprGet c.σ 10).isSome) (frame : NativeFrame sp 48) :
    FnSummary 0x8003ea0c#64 (fun d => d = c)
      (fun d => EffectPost initWrites (writeLog c.σ.mem (initLog (regsAt c))) c ra
        2147994696#64 d ∧ GHolds d.σ [(1, ra), (2, sp), (8, s0), (9, s1), (18, s2), (19, s3), (20, s4)]) := by
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have sp48 : sp + 18446744073709551568#64 = sp - 48#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e0 : sp - 48#64 = sp - BitVec.ofNat 64 48 + BitVec.ofNat 64 0 := by simp
  have ww (off : Nat) (ho : off + 8 ≤ 48) (ao : off % 8 = 0) :
      WriteWindow (sp - BitVec.ofNat 64 48 + BitVec.ofNat 64 off) 8 :=
    frame_word (k := 48) (off := off) frame (by decide) ho (by decide) ao
  have n (off : Nat) (ho : off ≤ 48) := frame_nat (k := 48) (off := off) frame (by decide) ho
  have n0 : (sp - 48#64).toNat = sp.toNat - 48 := by rw [BitVec.toNat_sub]; simp; omega
  -- `stdin`: the saves, the handler, stdin's word and cleared fields
  apply summary_bind (GlobalStdioInit.stdin_fast c (regsAt c) (by rw [r1]; exact h)
    (by simp only [GlobalStdioInit.stdin_input, GHolds]
        exact ⟨gpr_some (gpr_some_of h.raReg), gpr_some (gpr_some_of sp0), gpr_some (gpr_some_of s0r),
          gpr_some (gpr_some_of s1r), gpr_some a0r, gpr_some (gpr_some_of s2r), gpr_some (gpr_some_of s3r),
          gpr_some (gpr_some_of s4r), trivial⟩)
    (by rw [r2, sp48]; exact ww 40 (by decide) (by decide)) (by rw [r2, sp48]; exact ww 32 (by decide) (by decide))
    (by rw [r2, sp48]; exact ww 24 (by decide) (by decide)) (by rw [r2, sp48]; exact ww 16 (by decide) (by decide))
    (by rw [r2, sp48]; exact ww 8 (by decide) (by decide)) (by rw [r2, sp48, e0]; exact ww 0 (by decide) (by decide))
    (StdioFrame.imageOutside_above fun e he => by
      simp only [GlobalStdioInit.stdinLog, r2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | decide | (simp only [n 40 (by decide), n 32 (by decide), n 24 (by decide), n 16 (by decide),
          n 8 (by decide), n0]; omega))) (fun _ p => p.pc)
  intro c1 p1
  have q8 : gprGet c1.σ 8 = some stdinFile := gholds_lookup (n := 8) _ p1.regs rfl
  have q2 : gprGet c1.σ 2 = some (sp + 18446744073709551568#64) := by
    have := gholds_lookup (n := 2) _ p1.regs rfl; rwa [r2] at this
  have g1 := GprsSame.of_post p1 (by decide)
  -- `memset(&stdin->_mbstate, 0, 8)`
  apply summary_bind (memset_call GlobalStdioInit.stdin_call_shape GlobalStdioInit.stdin_call_decode
    (GlobalStdioInit.stdin_call_pins p1.image) GlobalStdioInit.stdin_call_target (by decide) p1.good p1.image
    p1.tick p1.minstret (gholds_lookup (n := 10) _ p1.regs rfl) (gholds_lookup (n := 11) _ p1.regs rfl)
    (gholds_lookup (n := 12) _ p1.regs rfl) (by decide) (by decide) (by decide)) (fun _ m => m.1.pc)
  intro c3 m3
  have g3 := GprsSame.of_effect m3.1 (by decide)
  have f3 (k : Nat) {v : BitVec 64} (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1] ++ [5, 6, 13, 14])
      (hv : gprGet c1.σ k = some v) : gprGet c3.σ k = some v := g3.get lo hi out hv
  -- stdin's cookie and I/O functions; `__retarget_lock_init_recursive(&stdin->_lock)`
  have l3 : LeafInput (regsAt c3 1) c3 := by
    rw [regsAt_of m3.2]; exact ⟨m3.1.good, m3.1.image, m3.1.minstret, m3.2, by decide, m3.1.tick⟩
  have s8 := f3 8 (by decide) (by decide) (by decide) q8
  apply summary_bind (GlobalStdioInit.stdinFns_fast c3 (regsAt c3) l3
    (by simp only [GlobalStdioInit.stdinFns_input, GHolds]
        exact ⟨gpr_some (gpr_some_of m3.2), gpr_some (gpr_some_of s8), gpr_some (gpr_some_of m3.1.result), trivial⟩)
    (by rw [regsAt_of s8]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [GlobalStdioInit.stdinFnsLog, regsAt_of s8]
        exact ⟨by simp only [OutLRange]; decide, by simp only [OutLRange]; decide⟩)) (fun _ p => p.pc)
  intro c4 p4
  have g4 := GprsSame.of_post p4 (by decide)
  have fn9 : gprGet c4.σ 9 = some 0x80040184#64 := gholds_lookup (n := 9) _ p4.regs rfl
  have fn18 : gprGet c4.σ 18 = some 0x80040120#64 := gholds_lookup (n := 18) _ p4.regs rfl
  have fn19 : gprGet c4.σ 19 = some 0x80040098#64 := gholds_lookup (n := 19) _ p4.regs rfl
  have fn20 : gprGet c4.σ 20 = some 0x80040034#64 := gholds_lookup (n := 20) _ p4.regs rfl
  have s8' : gprGet c4.σ 8 = some stdinFile := by
    have := gholds_lookup (n := 8) _ p4.regs rfl; rwa [regsAt_of s8] at this
  apply summary_bind (lockInit_call GlobalStdioInit.stdinFns_call_shape GlobalStdioInit.stdinFns_call_decode
    (GlobalStdioInit.stdinFns_call_pins p4.image) GlobalStdioInit.stdinFns_call_target (by decide) p4.good p4.image
    p4.tick p4.minstret (gholds_lookup (n := 10) _ p4.regs rfl)) (fun _ m => m.1.pc)
  intro c6 m6
  have g6 := GprsSame.of_effect m6.1 (by decide)
  have f6 (k : Nat) {v : BitVec 64} (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1] ++ [])
      (hv : gprGet c4.σ k = some v) : gprGet c6.σ k = some v := g6.get lo hi out hv
  have s8_6 := f6 8 (by decide) (by decide) (by decide) s8'
  -- stdout's word and cleared fields; `memset(&stdout->_mbstate, 0, 8)`
  have l6 : LeafInput (regsAt c6 1) c6 := by
    rw [regsAt_of m6.2]; exact ⟨m6.1.good, m6.1.image, m6.1.minstret, m6.2, by decide, m6.1.tick⟩
  apply summary_bind (GlobalStdioInit.stdout_fast c6 (regsAt c6) l6
    (by simp only [GlobalStdioInit.stdout_input, GHolds]
        exact ⟨gpr_some (gpr_some_of m6.2), gpr_some (gpr_some_of s8_6), gpr_some (gpr_some_of m6.1.result), trivial⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_6]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [GlobalStdioInit.stdoutLog, regsAt_of s8_6]
        exact ⟨by simp only [OutLRange]; decide, by simp only [OutLRange]; decide⟩)) (fun _ p => p.pc)
  intro c7 p7
  have g7 := GprsSame.of_post p7 (by decide)
  apply summary_bind (memset_call GlobalStdioInit.stdout_call_shape GlobalStdioInit.stdout_call_decode
    (GlobalStdioInit.stdout_call_pins p7.image) GlobalStdioInit.stdout_call_target (by decide) p7.good p7.image
    p7.tick p7.minstret (gholds_lookup (n := 10) _ p7.regs rfl) (gholds_lookup (n := 11) _ p7.regs rfl)
    (gholds_lookup (n := 12) _ p7.regs rfl) (by decide) (by decide) (by decide)) (fun _ m => m.1.pc)
  intro c9 m9
  have g9 := GprsSame.of_effect m9.1 (by decide)
  have g69 := (g7.trans g9)
  have f9 (k : Nat) {v : BitVec 64} (lo : 1 ≤ k) (hi : k ≤ 31)
      (out : k ∉ ([1] ++ [5, 6, 13, 14]) ++ [10, 11, 12, 15]) (hv : gprGet c6.σ k = some v) : gprGet c9.σ k = some v :=
    g69.get lo hi out hv
  have s8_9 : gprGet c9.σ 8 = some stdinFile := by
    have := gholds_lookup (n := 8) _ p7.regs rfl
    rw [regsAt_of s8_6] at this
    exact g9.get (by decide) (by decide) (by decide) this
  have fn9_9 := f9 9 (by decide) (by decide) (by decide) (f6 9 (by decide) (by decide) (by decide) fn9)
  have fn18_9 := f9 18 (by decide) (by decide) (by decide) (f6 18 (by decide) (by decide) (by decide) fn18)
  have fn19_9 := f9 19 (by decide) (by decide) (by decide) (f6 19 (by decide) (by decide) (by decide) fn19)
  have fn20_9 := f9 20 (by decide) (by decide) (by decide) (f6 20 (by decide) (by decide) (by decide) fn20)
  -- stdout's cookie and I/O functions; its lock
  have l9 : LeafInput (regsAt c9 1) c9 := by
    rw [regsAt_of m9.2]; exact ⟨m9.1.good, m9.1.image, m9.1.minstret, m9.2, by decide, m9.1.tick⟩
  apply summary_bind (GlobalStdioInit.stdoutFns_fast c9 (regsAt c9) l9
    (by simp only [GlobalStdioInit.stdoutFns_input, GHolds]
        exact ⟨gpr_some (gpr_some_of m9.2), gpr_some (gpr_some_of s8_9), gpr_some (gpr_some_of fn9_9),
          gpr_some (gpr_some_of m9.1.result), gpr_some (gpr_some_of fn18_9), gpr_some (gpr_some_of fn19_9),
          gpr_some (gpr_some_of fn20_9), trivial⟩)
    (by rw [regsAt_of s8_9]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_9]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_9]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_9]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_9]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [GlobalStdioInit.stdoutFnsLog, regsAt_of s8_9, regsAt_of fn9_9, regsAt_of fn18_9,
          regsAt_of fn19_9, regsAt_of fn20_9]
        exact ⟨by simp only [OutLRange]; decide, by simp only [OutLRange]; decide⟩)) (fun _ p => p.pc)
  intro c10 p10
  have g10 := GprsSame.of_post p10 (by decide)
  apply summary_bind (lockInit_call GlobalStdioInit.stdoutFns_call_shape GlobalStdioInit.stdoutFns_call_decode
    (GlobalStdioInit.stdoutFns_call_pins p10.image) GlobalStdioInit.stdoutFns_call_target (by decide) p10.good
    p10.image p10.tick p10.minstret (gholds_lookup (n := 10) _ p10.regs rfl)) (fun _ m => m.1.pc)
  intro c12 m12
  have g12 := GprsSame.of_effect m12.1 (by decide)
  have g912 := g10.trans g12
  have f12 (k : Nat) {v : BitVec 64} (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ ([1] ++ []) ++ [10, 15])
      (hv : gprGet c9.σ k = some v) : gprGet c12.σ k = some v := g912.get lo hi out hv
  have s8_12 := f12 8 (by decide) (by decide) (by decide) s8_9
  -- stderr's word and cleared fields; `memset(&stderr->_mbstate, 0, 8)`
  have l12 : LeafInput (regsAt c12 1) c12 := by
    rw [regsAt_of m12.2]; exact ⟨m12.1.good, m12.1.image, m12.1.minstret, m12.2, by decide, m12.1.tick⟩
  apply summary_bind (GlobalStdioInit.stderr_fast c12 (regsAt c12) l12
    (by simp only [GlobalStdioInit.stderr_input, GHolds]
        exact ⟨gpr_some (gpr_some_of m12.2), gpr_some (gpr_some_of s8_12), gpr_some (gpr_some_of m12.1.result),
          trivial⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_12]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [GlobalStdioInit.stderrLog, regsAt_of s8_12]
        exact ⟨by simp only [OutLRange]; decide, by simp only [OutLRange]; decide⟩)) (fun _ p => p.pc)
  intro c13 p13
  have g13 := GprsSame.of_post p13 (by decide)
  apply summary_bind (memset_call GlobalStdioInit.stderr_call_shape GlobalStdioInit.stderr_call_decode
    (GlobalStdioInit.stderr_call_pins p13.image) GlobalStdioInit.stderr_call_target (by decide) p13.good p13.image
    p13.tick p13.minstret (gholds_lookup (n := 10) _ p13.regs rfl) (gholds_lookup (n := 11) _ p13.regs rfl)
    (gholds_lookup (n := 12) _ p13.regs rfl) (by decide) (by decide) (by decide)) (fun _ m => m.1.pc)
  intro c15 m15
  have g15 := GprsSame.of_effect m15.1 (by decide)
  -- the registers through the whole run, from the first block's post
  have run := (((((((g3.trans (GprsSame.of_post p4 (by decide))).trans g6).trans g7).trans g9).trans g10).trans
    g12).trans g13).trans g15
  have s8_15 : gprGet c15.σ 8 = some stdinFile := by
    have := gholds_lookup (n := 8) _ p13.regs rfl
    rw [regsAt_of s8_12] at this
    exact g15.get (by decide) (by decide) (by decide) this
  have sp15 : gprGet c15.σ 2 = some (sp + 18446744073709551568#64) := run.get (by decide) (by decide) (by decide) q2
  have fn (k : Nat) {v : BitVec 64} (lo : 1 ≤ k) (hi : k ≤ 31) (hk : k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20)
      (hv : gprGet c9.σ k = some v) : gprGet c15.σ k = some v := by
    have g := (((g10.trans g12).trans g13).trans g15)
    exact g.get lo hi (by rcases hk with rfl | rfl | rfl | rfl <;> decide) hv
  have fn9_15 := fn 9 (by decide) (by decide) (by decide) fn9_9
  have fn18_15 := fn 18 (by decide) (by decide) (by decide) fn18_9
  have fn19_15 := fn 19 (by decide) (by decide) (by decide) fn19_9
  have fn20_15 := fn 20 (by decide) (by decide) (by decide) fn20_9
  -- the memory so far: the saves and stdin's stores, then the streams' stores
  have M1 : c1.σ.mem = writeLog c.σ.mem (GlobalStdioInit.stdinLog (regsAt c) []) := p1.memory
  have M4 : c4.σ.mem = writeLog c3.σ.mem (GlobalStdioInit.stdinFnsLog fnsR []) := by
    rw [p4.memory]; simp only [GlobalStdioInit.stdinFnsLog, regsAt_of s8]; rfl
  have M7 : c7.σ.mem = writeLog c6.σ.mem (GlobalStdioInit.stdoutLog fnsR []) := by
    rw [p7.memory]; simp only [GlobalStdioInit.stdoutLog, regsAt_of s8_6]; rfl
  have M10 : c10.σ.mem = writeLog c9.σ.mem (GlobalStdioInit.stdoutFnsLog fnsR []) := by
    rw [p10.memory]
    simp only [GlobalStdioInit.stdoutFnsLog, regsAt_of s8_9, regsAt_of fn9_9, regsAt_of fn18_9, regsAt_of fn19_9,
      regsAt_of fn20_9]
    rfl
  have M13 : c13.σ.mem = writeLog c12.σ.mem (GlobalStdioInit.stderrLog fnsR []) := by
    rw [p13.memory]; simp only [GlobalStdioInit.stderrLog, regsAt_of s8_12]; rfl
  have M15 : c15.σ.mem = writeLog (writeLog c.σ.mem (GlobalStdioInit.stdinLog (regsAt c) [])) streamsPre := by
    rw [m15.1.memory, M13, m12.1.memory, M10, m9.1.memory, M7, m6.1.memory, M4, m3.1.memory, M1]
    simp only [streamsPre, writeLog_append]
  -- the saved words, untouched since the prologue
  have slot (off idx : Nat) (ho : off + 8 ≤ 48) (v : BitVec 64)
      (sel : (GlobalStdioInit.stdinLog (regsAt c) [])[idx]? = some ((sp - 48#64 + BitVec.ofNat 64 off).toNat, 8, v))
      (out : OutLRange ((GlobalStdioInit.stdinLog (regsAt c) []).drop (idx + 1)) (sp.toNat - 48 + off) 8) :
      bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64 + BitVec.ofNat 64 off).toNat) = v := by
    have e := n off (by omega)
    rw [sp48, M15, ConsoleWrite.read8_outside streamsPre_within (Or.inr (by rw [e]; omega)), read8_value]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ idx _ _ sel (by rw [e]; exact out)
  have r8 := regsAt_of s0r
  have r9 := regsAt_of s1r
  have r18 := regsAt_of s2r
  have r19 := regsAt_of s3r
  have r20 := regsAt_of s4r
  have sv0 : bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64 + 32#64).toNat) = s0 :=
    slot 32 1 (by decide) s0 (by simp only [GlobalStdioInit.stdinLog, r2, r8]; rfl) (by
      simp only [GlobalStdioInit.stdinLog, r2, List.drop, OutLRange, n 24 (by decide), n 16 (by decide),
        n 8 (by decide), n0, BitVec.toNat_ofNat, and_true]
      omega)
  have svra : bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64 + 40#64).toNat) = ra :=
    slot 40 0 (by decide) ra (by simp only [GlobalStdioInit.stdinLog, r2, r1]; rfl) (by
      simp only [GlobalStdioInit.stdinLog, r2, List.drop, OutLRange, n 32 (by decide), n 24 (by decide),
        n 16 (by decide), n 8 (by decide), n0, BitVec.toNat_ofNat, and_true]
      omega)
  have sv1 : bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64 + 24#64).toNat) = s1 :=
    slot 24 2 (by decide) s1 (by simp only [GlobalStdioInit.stdinLog, r2, r9]; rfl) (by
      simp only [GlobalStdioInit.stdinLog, r2, List.drop, OutLRange, n 16 (by decide), n 8 (by decide), n0,
        BitVec.toNat_ofNat, and_true]
      omega)
  have sv2 : bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64 + 16#64).toNat) = s2 :=
    slot 16 3 (by decide) s2 (by simp only [GlobalStdioInit.stdinLog, r2, r18]; rfl) (by
      simp only [GlobalStdioInit.stdinLog, r2, List.drop, OutLRange, n 8 (by decide), n0, BitVec.toNat_ofNat, and_true]
      omega)
  have sv3 : bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64 + 8#64).toNat) = s3 :=
    slot 8 4 (by decide) s3 (by simp only [GlobalStdioInit.stdinLog, r2, r19]; rfl) (by
      simp only [GlobalStdioInit.stdinLog, r2, List.drop, OutLRange, n0, BitVec.toNat_ofNat, and_true]
      omega)
  have sv4 : bytesVal .ld (read8 c15.σ.mem (sp + 18446744073709551568#64).toNat) = s4 := by
    have := slot 0 5 (by decide) s4 (by simp only [GlobalStdioInit.stdinLog, r2, r20, ← e0]; rfl) (by
      simp only [GlobalStdioInit.stdinLog, r2, List.drop, OutLRange, BitVec.toNat_ofNat, and_true]
      omega)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  -- stderr's cookie and I/O functions; the saves reloaded; `j __retarget_lock_init_recursive`
  have l15 : LeafInput (regsAt c15 1) c15 := by
    rw [regsAt_of m15.2]; exact ⟨m15.1.good, m15.1.image, m15.1.minstret, m15.2, by decide, m15.1.tick⟩
  have sw (off : Nat) (ho : off + 8 ≤ 48) (ao : off % 8 = 0) :
      ReadWindow (regsAt c15 2 + BitVec.ofNat 64 off) 8 := by
    rw [regsAt_of sp15, sp48]; exact (ww off ho ao).read
  have L16 : GlobalStdioInit.stderrFnsLog (regsAt c15) (GlobalStdioInit.stderrFns_loads c15.σ.mem (regsAt c15)) =
      GlobalStdioInit.stderrFnsLog fnsR [] := by
    simp only [GlobalStdioInit.stderrFnsLog, regsAt_of s8_15, regsAt_of fn9_15, regsAt_of fn18_15,
      regsAt_of fn19_15, regsAt_of fn20_15]
    rfl
  have W16 : ExitPath.LogWithin ((GlobalStdioInit.stderrFnsLog fnsR []).take 5) 0x8007ca38 0x8007cd00 := by
    unfold ExitPath.LogWithin; decide
  have away (off : Nat) (ho : off + 8 ≤ 48) :
      OutLRange ((GlobalStdioInit.stderrFnsLog (regsAt c15) (GlobalStdioInit.stderrFns_loads c15.σ.mem
        (regsAt c15))).take 5) (regsAt c15 2 + BitVec.ofNat 64 off).toNat 8 := by
    rw [L16, regsAt_of sp15, sp48, n off (by omega)]
    exact ExitPath.LogWithin.outLRange W16 (Or.inr (by omega))
  have zero0 : regsAt c15 2 = regsAt c15 2 + BitVec.ofNat 64 0 := by simp
  apply summary_bind (GlobalStdioInit.stderrFns_fast c15 (regsAt c15) l15
    (by simp only [GlobalStdioInit.stderrFns_input, GHolds]
        exact ⟨gpr_some (gpr_some_of sp15), gpr_some (gpr_some_of s8_15), gpr_some (gpr_some_of fn9_15),
          gpr_some (gpr_some_of m15.1.result), gpr_some (gpr_some_of fn18_15), gpr_some (gpr_some_of fn19_15),
          gpr_some (gpr_some_of fn20_15), trivial⟩)
    (by rw [regsAt_of s8_15]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_15]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_15]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_15]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by rw [regsAt_of s8_15]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (sw 32 (by decide) (by decide)) (away 32 (by decide)) (sw 40 (by decide) (by decide)) (away 40 (by decide))
    (sw 24 (by decide) (by decide)) (away 24 (by decide)) (sw 16 (by decide) (by decide)) (away 16 (by decide))
    (sw 8 (by decide) (by decide)) (away 8 (by decide))
    (by rw [zero0]; exact sw 0 (by decide) (by decide)) (by rw [zero0]; exact away 0 (by decide))
    (by rw [L16]
        exact ⟨by simp only [GlobalStdioInit.stderrFnsLog, OutLRange]; decide,
          by simp only [GlobalStdioInit.stderrFnsLog, OutLRange]; decide⟩)) (fun _ p => p.pc)
  intro c16 p16
  have o := p16.regs
  simp only [GlobalStdioInit.stderrFns_regs, GlobalStdioInit.stderrFns_loads, regsAt_of sp15, List.getD_cons_zero,
    List.getD_cons_succ, GHolds] at o
  obtain ⟨d2, d10, d20, d19, d18, d9, d1, d8, -⟩ := o
  rw [sv4] at d20
  rw [sv3] at d19
  rw [sv2] at d18
  rw [sv1] at d9
  rw [svra] at d1
  rw [sv0] at d8
  have d2' : gprGet c16.σ 2 = some sp := by rw [d2, BitVec.add_assoc]; simp
  -- the lock leaf returns to `ra`
  apply (RetargetLockInit.leaf_fast c16 (regsAt c16) (by rw [regsAt_of d1]; exact ⟨p16.good, p16.image, p16.minstret,
    d1, h.aligned, p16.tick⟩) ⟨gpr_some (gpr_some_of d1), gpr_some (gpr_some_of d10), trivial⟩).weaken (fun _ e => e)
  intro c17 l17
  have k17 (k : Nat) {v : BitVec 64} (lo : 1 ≤ k) (hi : k ≤ 31) (hv : gprGet c16.σ k = some v) :
      gprGet c17.σ k = some v := (l17.gpr_frame (by decide) k lo hi (by simp)).trans hv
  have E := (((((((((((p1.toEffectPost.trans m3.1).trans p4.toEffectPost).trans m6.1).trans p7.toEffectPost).trans
    m9.1).trans p10.toEffectPost).trans m12.1).trans p13.toEffectPost).trans m15.1).trans p16.toEffectPost).trans
    l17.toEffectPost).widen (writes' := initWrites) (by decide)
  have mem : c17.σ.mem = writeLog c.σ.mem (initLog (regsAt c)) := by
    rw [l17.memory, Named.NamedValue.wl_nil, p16.memory, L16, M15, initLog_eq, streamsLog]
    simp only [streamsPre, writeLog_append, List.append_assoc]
  have pc : pcOf c17 = some ra := by have := l17.pc; rwa [regsAt_of d1] at this
  have res : gpr c17 10 = some 2147994696#64 := by have := l17.result; rwa [regsAt_of d10] at this
  exact ⟨⟨E.good, E.image, E.minstret, E.tick, pc, res, mem, E.output, E.frame, E.kept⟩,
    ⟨k17 1 (by decide) (by decide) d1, k17 2 (by decide) (by decide) d2', k17 8 (by decide) (by decide) d8, k17 9 (by decide) (by decide) d9,
      k17 18 (by decide) (by decide) d18, k17 19 (by decide) (by decide) d19, k17 20 (by decide) (by decide) d20,
      trivial⟩⟩

theorem outLRange_append {left right : List WEntry} {a n : Nat}
    (hl : OutLRange left a n) (hr : OutLRange right a n) : OutLRange (left ++ right) a n := by
  induction left with
  | nil => exact hr
  | cons entry left ih => exact ⟨hl.1, ih hl.2⟩

open OCaml.Vm.Primitives.Uncaught.StdioState (impure)

/-- The registers `__sinit` hands `global_stdio_init`: the link, `sp - 16`,
`s0 = reent`, and `s1`–`s4` as at its own call. -/
def sinitR (sp s1 s2 s3 s4 : BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 1 then 0x8003ed50#64 else if n = 2 then sp + 18446744073709551600#64 else if n = 8 then impure
  else if n = 9 then s1 else if n = 18 then s2 else if n = 19 then s3 else if n = 20 then s4 else 0#64

/-- `__sinit`'s stores: its saves, `reent->__cleanup = cleanup_stdio`, then
`global_stdio_init`'s. -/
def sinitLog (sp ra s0 s1 s2 s3 s4 : BitVec 64) : List WEntry :=
  [((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra), ((impure + 72#64).toNat, 8, 0x8003e91c#64)] ++
    initLog (sinitR sp s1 s2 s3 s4)

/-- The registers `__sinit` writes (its saved ones restored). -/
def sinitWrites : List Nat := [1, 2, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20]

/-- **`__sinit(reent)` on the first stdio call** (`reent->__cleanup` and
`__stdio_exit_handler` unset): `cleanup_stdio` installed, then
`global_stdio_init`; back at `ra` with `sp` and `s0`–`s4` restored. -/
theorem sinit_run {c : Config} {ra sp s0 s1 s2 s3 s4 : BitVec 64} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (a0 : gprGet c.σ 10 = some impure) (s0r : gprGet c.σ 8 = some s0)
    (s1r : gprGet c.σ 9 = some s1) (s2r : gprGet c.σ 18 = some s2) (s3r : gprGet c.σ 19 = some s3)
    (s4r : gprGet c.σ 20 = some s4) (frame : NativeFrame sp 64)
    (fresh : bytesVal .ld (read8 c.σ.mem (impure + 72#64).toNat) = 0#64)
    (noHandler : bytesVal .ld (read8 c.σ.mem (0x80064d38#64).toNat) = 0#64) :
    FnSummary 0x8003ecf8#64 (fun d => d = c)
      (fun d => EffectPost sinitWrites (writeLog c.σ.mem (sinitLog sp ra s0 s1 s2 s3 s4)) c ra 0x80064d88#64 d ∧
        GHolds d.σ [(2, sp), (8, s0), (9, s1), (18, s2), (19, s3), (20, s4)]) := by
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have sp16 : sp + 18446744073709551600#64 = sp - 16#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have e0 : sp - 16#64 = sp - BitVec.ofNat 64 16 + BitVec.ofNat 64 0 := by simp
  have n0 : (sp - 16#64).toNat = sp.toNat - 16 := by rw [BitVec.toNat_sub]; simp; omega
  have n8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 16 + 8 := frame_nat (k := 16) (off := 8) frame (by decide) (by decide)
  -- `pro`: save `s0`, `ra`; `s0 = reent`; `__lock_acquire_recursive(&__sfp_recursive_mutex)`
  apply summary_bind (Sinit.pro_fast c (regsAt c) (by rw [r1]; exact h)
    (by simp only [Sinit.pro_input, GHolds]
        exact ⟨gpr_some (gpr_some_of h.raReg), gpr_some (gpr_some_of sp0), gpr_some (gpr_some_of s0r),
          gpr_some (gpr_some_of a0), trivial⟩)
    (by rw [r2, sp16, e0]; exact frame_word (k := 16) (off := 0) frame (by decide) (by decide) (by decide) (by decide))
    (by rw [r2, sp16]; exact frame_word (k := 16) (off := 8) frame (by decide) (by decide) (by decide) (by decide))
    (StdioFrame.imageOutside_above fun e he => by
      simp only [Sinit.proLog, r2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp only [n0, n8] <;> omega)) (fun _ p => p.pc)
  intro c1 p1
  have M1 : c1.σ.mem = writeLog c.σ.mem [((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra)] := by
    rw [p1.memory]; simp only [Sinit.proLog, r2, regsAt_of s0r, r1]
  have W1 : ExitPath.LogWithin [((sp - 16#64).toNat, 8, s0), ((sp - 16#64 + 8#64).toNat, 8, ra)]
      (sp.toNat - 16) sp.toNat := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp only [n0, n8] <;> omega
  have rd1 (a : Nat) (ha : a + 8 ≤ sp.toNat - 16) : read8 c1.σ.mem a = read8 c.σ.mem a := by
    rw [M1]; exact ConsoleWrite.read8_outside W1 (Or.inl ha)
  have q8 : gprGet c1.σ 8 = some impure := by have := gholds_lookup (n := 8) _ p1.regs rfl; rwa [regsAt_of a0] at this
  have q2 : gprGet c1.σ 2 = some (sp + 18446744073709551600#64) := by
    have := gholds_lookup (n := 2) _ p1.regs rfl; rwa [r2] at this
  have g1 := GprsSame.of_post p1 (by decide)
  apply summary_bind (retLeaf_call Sinit.pro_call_shape Sinit.pro_call_decode (Sinit.pro_call_pins p1.image)
    Sinit.pro_call_target ExitPath.RetargetLockAcquireRecursive.leaf_fast (by decide) p1.good p1.image p1.tick
    p1.minstret (gholds_lookup (n := 10) _ p1.regs rfl)) (fun _ m => m.1.pc)
  intro c3 m3
  have g3 := GprsSame.of_effect m3.1 (by decide)
  have s8_3 : gprGet c3.σ 8 = some impure := g3.get (by decide) (by decide) (by decide) q8
  have l3 : LeafInput (regsAt c3 1) c3 := by
    rw [regsAt_of m3.2]; exact ⟨m3.1.good, m3.1.image, m3.1.minstret, m3.2, by decide, m3.1.tick⟩
  have mem3 : c3.σ.mem = c1.σ.mem := m3.1.memory
  -- `reent->__cleanup` is unset
  apply summary_bind (Sinit.fresh_fast c3 (regsAt c3) l3
    (by simp only [Sinit.fresh_input, GHolds]
        exact ⟨gpr_some (gpr_some_of s8_3), gpr_some (gpr_some_of m3.1.result), trivial⟩)
    (by rw [regsAt_of s8_3]; exact ⟨by decide, by decide, by decide⟩)
    (by simp only [Sinit.fresh_loads, List.getD_cons_zero, regsAt_of s8_3, mem3]
        rw [rd1 _ (by rw [show (impure + 72#64).toNat = 2147894960 by decide]; omega), fresh]; decide)) (fun _ p => p.pc)
  intro c4 p4
  have g4 := GprsSame.of_post p4 (by decide)
  have s8_4 : gprGet c4.σ 8 = some impure := g4.get (by decide) (by decide) (by decide) s8_3
  have ra4 : gprGet c4.σ 1 = some 0x8003ed14#64 := g4.get (by decide) (by decide) (by decide) m3.2
  have mem4 : c4.σ.mem = c1.σ.mem := by rw [p4.memory, Named.NamedValue.wl_nil, mem3]
  -- `__cleanup = cleanup_stdio`; no `__stdio_exit_handler` yet
  apply summary_bind (Sinit.install_fast c4 (regsAt c4) (by rw [regsAt_of ra4]; exact ⟨p4.good, p4.image, p4.minstret,
      ra4, by decide, p4.tick⟩)
    (by simp only [Sinit.install_input, GHolds]
        exact ⟨gpr_some (gpr_some_of s8_4), gpr_some (gpr_some_of p4.result), trivial⟩)
    (by rw [regsAt_of s8_4]; exact ⟨by decide, by decide, by decide, by decide⟩)
    (by simp only [Sinit.installLog, regsAt_of s8_4]
        exact ⟨by simp only [OutLRange]; decide, by simp only [OutLRange]; decide⟩)
    (by simp only [Sinit.install_loads, List.getD_cons_zero, mem4]
        rw [rd1 _ (by rw [show (0x80064d38#64 : BitVec 64).toNat = 2147896632 by decide]; omega), noHandler]; decide))
    (fun _ p => p.pc)
  intro c5 p5
  have g5 := GprsSame.of_post p5 (by decide)
  have ra5 : gprGet c5.σ 1 = some 0x8003ed14#64 := g5.get (by decide) (by decide) (by decide) ra4
  have M5 : c5.σ.mem = writeLog c1.σ.mem [((impure + 72#64).toNat, 8, 0x8003e91c#64)] := by
    rw [p5.memory, mem4]; simp only [Sinit.installLog, regsAt_of s8_4]
  -- `jal global_stdio_init`
  apply summary_bind (Sinit.init_fast c5 (regsAt c5) (by rw [regsAt_of ra5]; exact ⟨p5.good, p5.image, p5.minstret,
      ra5, by decide, p5.tick⟩)
    (by simp only [Sinit.init_input, GHolds]
        exact ⟨gpr_some (gpr_some_of ra5), gpr_some (gpr_some_of p5.result), trivial⟩)) (fun _ p => p.pc)
  intro c6 p6
  have g6 := GprsSame.of_post p6 (by decide)
  apply summary_bind (call_from Sinit.init_call_shape Sinit.init_call_decode (Sinit.init_call_pins p6.image) p6.good
    p6.image p6.tick p6.minstret p6.result) (fun _ q => q.pc)
  intro c7 q7
  rw [show Sinit.init_call.target = 0x8003ea0c#64 by decide]
  have g7 := GprsSame.of_post q7 (by decide)
  have run17 := (((g3.trans g4).trans g5).trans g6).trans g7
  have link7 : gprGet c7.σ 1 = some 0x8003ed50#64 := gholds_lookup (n := 1) _ q7.regs rfl
  have get7 (k : Nat) {v : BitVec 64} (hk : k = 2 ∨ k = 8 ∨ k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20)
      (hv : gprGet c1.σ k = some v) : gprGet c7.σ k = some v :=
    run17.get (by omega) (by omega) (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hv
  have get1 (k : Nat) {v : BitVec 64} (hk : k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20) (hv : gprGet c.σ k = some v) :
      gprGet c1.σ k = some v :=
    g1.get (by omega) (by omega) (by rcases hk with rfl | rfl | rfl | rfl <;> decide) hv
  have sp7 := get7 2 (by decide) q2
  have s8_7 := get7 8 (by decide) q8
  have s9_7 := get7 9 (by decide) (get1 9 (by decide) s1r)
  have s18_7 := get7 18 (by decide) (get1 18 (by decide) s2r)
  have s19_7 := get7 19 (by decide) (get1 19 (by decide) s3r)
  have s20_7 := get7 20 (by decide) (get1 20 (by decide) s4r)
  have frame' : NativeFrame (sp + 18446744073709551600#64) 48 :=
    StdioClose.frame_callee (front := 16) (size := 48) frame (by decide) _ (by decide)
  apply summary_bind (global_stdio_init_run ⟨q7.good, q7.image, q7.minstret, link7, by decide, q7.tick⟩ sp7 s8_7 s9_7
    s18_7 s19_7 s20_7 (gpr_some_of (gholds_lookup (n := 10) _ q7.regs rfl)) frame') (fun _ e => e.1.pc)
  intro c8 e8
  obtain ⟨E8, ra8, sp8, -, t9, t18, t19, t20, -⟩ := e8
  -- the log so far, from `__sinit`'s entry
  have St : GlobalStdioInit.stdinLog (regsAt c7) [] = GlobalStdioInit.stdinLog (sinitR sp s1 s2 s3 s4) [] := by
    have e1 : sinitR sp s1 s2 s3 s4 1 = 0x8003ed50#64 := rfl
    have e2 : sinitR sp s1 s2 s3 s4 2 = sp + 18446744073709551600#64 := rfl
    have e8 : sinitR sp s1 s2 s3 s4 8 = impure := rfl
    have e9 : sinitR sp s1 s2 s3 s4 9 = s1 := rfl
    have e18 : sinitR sp s1 s2 s3 s4 18 = s2 := rfl
    have e19 : sinitR sp s1 s2 s3 s4 19 = s3 := rfl
    have e20 : sinitR sp s1 s2 s3 s4 20 = s4 := rfl
    simp only [GlobalStdioInit.stdinLog, regsAt_of link7, regsAt_of sp7, regsAt_of s8_7, regsAt_of s9_7,
      regsAt_of s18_7, regsAt_of s19_7, regsAt_of s20_7, e1, e2, e8, e9, e18, e19, e20]
  have I7 : initLog (regsAt c7) = initLog (sinitR sp s1 s2 s3 s4) := by
    rw [initLog_eq, initLog_eq, St]
  have M8 : c8.σ.mem = writeLog c.σ.mem (sinitLog sp ra s0 s1 s2 s3 s4) := by
    rw [E8.memory, I7, q7.memory, p6.memory, Named.NamedValue.wl_nil, M5, M1, sinitLog, ← writeLog_append,
      ← writeLog_append]
    simp only [List.cons_append, List.nil_append]
  -- the saved words, untouched since the prologue
  have nn (off : Nat) (ho : off ≤ 48) := frame_nat (k := 64) (off := off) frame (by decide) (by omega)
  have rest (a : Nat) (ha : sp.toNat - 16 ≤ a) (ha' : a + 8 ≤ sp.toNat) :
      OutLRange ([((impure + 72#64).toNat, 8, 0x8003e91c#64)] ++ initLog (sinitR sp s1 s2 s3 s4)) a 8 := by
    rw [initLog_eq, ← List.append_assoc]
    refine outLRange_append (outLRange_append ?_ ?_) (ExitPath.LogWithin.outLRange streamsLog_within (Or.inr (by omega)))
    · simp only [OutLRange, show (impure + 72#64).toNat = 2147894960 by decide, and_true]; omega
    · have sR : sinitR sp s1 s2 s3 s4 2 = sp - 16#64 := by simp only [sinitR]; exact sp16
      have m48 : (sp - 16#64 - 48#64).toNat = sp.toNat - 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_sub]; simp; omega
      have mk (k : Nat) (hk : k ≤ 48) : (sp - 16#64 - 48#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 64 + k := by
        rw [BitVec.toNat_add, m48, BitVec.toNat_ofNat]; omega
      simp only [GlobalStdioInit.stdinLog, sR, OutLRange, mk 40 (by decide), mk 32 (by decide), mk 24 (by decide),
        mk 16 (by decide), mk 8 (by decide), m48, BitVec.toNat_ofNat, and_true]
      omega
  have slotS0 : bytesVal .ld (read8 c8.σ.mem (sp + 18446744073709551600#64).toNat) = s0 := by
    rw [read8_value, M8, sp16]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [sinitLog, List.drop, List.cons_append, List.nil_append]
      exact ⟨Or.inl (by rw [n0, n8]; omega), by
        exact (outLRange_append (show OutLRange [((sp - 16#64 + 8#64).toNat, 8, ra)] (sp - 16#64).toNat 8 from
          ⟨Or.inl (by rw [n0, n8]; omega), trivial⟩) (rest (sp - 16#64).toNat (by rw [n0]; omega)
            (by rw [n0]; omega))).2⟩)
  have slotRa : bytesVal .ld (read8 c8.σ.mem (sp + 18446744073709551600#64 + 8#64).toNat) = ra := by
    rw [read8_value, M8, sp16]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 1 _ _ rfl (by
      simp only [sinitLog, List.drop, List.cons_append, List.nil_append]
      exact rest _ (by rw [n8]; omega) (by rw [n8]; omega))
  -- `leave`: `s0`, `ra` reloaded; `j __retarget_lock_release_recursive`
  have w (off : Nat) (ho : off + 8 ≤ 16) (ao : off % 8 = 0) : ReadWindow (sp - 16#64 + BitVec.ofNat 64 off) 8 :=
    (frame_word (k := 16) (off := off) frame (by decide) ho (by decide) ao).read
  apply summary_bind (Sinit.leave_fast c8 (regsAt c8) (by rw [regsAt_of ra8]; exact ⟨E8.good, E8.image, E8.minstret,
      ra8, by decide, E8.tick⟩)
    (by simp only [Sinit.leave_input, GHolds]
        exact ⟨gpr_some (gpr_some_of sp8), gpr_some (gpr_some_of E8.result), trivial⟩)
    (by rw [regsAt_of sp8, sp16, e0]; exact w 0 (by decide) (by decide))
    (by rw [regsAt_of sp8, sp16]; exact w 8 (by decide) (by decide))) (fun _ p => p.pc)
  intro c9 p9
  have o9 := p9.regs
  simp only [Sinit.leave_regs, Sinit.leave_loads, regsAt_of sp8, List.getD_cons_zero, List.getD_cons_succ,
    GHolds] at o9
  obtain ⟨d2, d10, d1, d8, -⟩ := o9
  rw [slotRa] at d1
  rw [slotS0] at d8
  apply (ExitPath.RetargetLockReleaseRecursive.leaf_fast c9 (regsAt c9) (by rw [regsAt_of d1]; exact ⟨p9.good,
      p9.image, p9.minstret, d1, h.aligned, p9.tick⟩)
    ⟨gpr_some (gpr_some_of d1), gpr_some (gpr_some_of d10), trivial⟩).weaken (fun _ e => e)
  intro c10 l10
  have g9 := GprsSame.of_post p9 (by decide)
  have g10 := GprsSame.of_post l10 (by decide)
  have k (n : Nat) {v : BitVec 64} (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [] ++ [1, 2, 8, 10])
      (hv : gprGet c8.σ n = some v) : gprGet c10.σ n = some v := (g9.trans g10).get lo hi out hv
  have k' (n : Nat) {v : BitVec 64} (lo : 1 ≤ n) (hi : n ≤ 31) (hv : gprGet c9.σ n = some v) :
      gprGet c10.σ n = some v := g10.get lo hi (by simp) hv
  have E := ((((((((p1.toEffectPost.trans m3.1).trans p4.toEffectPost).trans p5.toEffectPost).trans
    p6.toEffectPost).trans q7.toEffectPost).trans E8).trans p9.toEffectPost).trans l10.toEffectPost).widen
    (writes' := sinitWrites) (by decide)
  have mem : c10.σ.mem = writeLog c.σ.mem (sinitLog sp ra s0 s1 s2 s3 s4) := by
    rw [l10.memory, Named.NamedValue.wl_nil, p9.memory, Named.NamedValue.wl_nil, M8]
  have pc : pcOf c10 = some ra := by have := l10.pc; rwa [regsAt_of d1] at this
  have res : gpr c10 10 = some 0x80064d88#64 := by have := l10.result; rwa [regsAt_of d10] at this
  have d2' : gprGet c9.σ 2 = some sp := by rw [d2, BitVec.add_assoc]; simp
  exact ⟨⟨E.good, E.image, E.minstret, E.tick, pc, res, mem, E.output, E.frame, E.kept⟩,
    ⟨k' 2 (by decide) (by decide) d2', k' 8 (by decide) (by decide) d8, k 9 (by decide) (by decide) (by decide) t9,
      k 18 (by decide) (by decide) (by decide) t18, k 19 (by decide) (by decide) (by decide) t19,
      k 20 (by decide) (by decide) (by decide) t20, trivial⟩⟩

end OCaml.Vm.Primitives.Uncaught.StdioInit
