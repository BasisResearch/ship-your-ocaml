import OCaml.Vm.Boot.Startup.ToMain

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The two writes made by main before entering the OCaml runtime. -/
def mainWrites (ra : BitVec 64) (env : List (BitVec 8)) : List WEntry :=
  [(Layout.sym_stack_top - 8, 8, ra), (Layout.sym_environ, 8, bytesVal .ld env)]

theorem main_log (ra : BitVec 64) (env argv : List (BitVec 8)) :
    (evalBlocks mainX1dccSeg
      (SegEvalState.init (mainX1dccL (BitVec.ofNat 64 Layout.sym_stack_top) ra)
        [env, argv])).log = mainWrites ra env := by
  simp [evalBlocks, evalBlock, SegEvalState.init, mainX1dccSeg, mainX1dccL,
    mainWrites, runGM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG,
    wvalM, widthOfM, wentryM, imm20Of, mkLine, decodeM, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    Layout.sym_stack_top, Layout.sym_environ]

/-- The main-to-runtime call seam, for arbitrary embedded argument/environment data. -/
structure CamlMainEntry (before after : Config) : Prop where
  gprs : GprPresent before.σ → GprPresent after.σ
  good : GoodState after.σ
  tick : after.tick < 2
  pc : PCAt (BitVec.ofNat 64 Layout.sym_caml_main) after
  memory : after.σ.mem = writeLog before.σ.mem
    (mainWrites ((gprGet before.σ 1).getD 0) (read8 before.σ.mem Layout.sym_embedded_env))
  stack : gprGet after.σ 2 = some (BitVec.ofNat 64 (Layout.sym_stack_top - 16))
  argv : gprGet after.σ 10 = some (bytesVal .ld (read8 before.σ.mem Layout.sym_embedded_argv))
  linkReg : gprGet after.σ 1 = some 0x80001df0#64
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1, 2, 10, 14, 15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem main_to_caml_main (c : Config) (ra : BitVec 64) (h : MainReady ra c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_main) (fun d => d = c) (CamlMainEntry c) := by
  constructor
  rintro d ⟨pc, eq⟩
  subst d
  obtain ⟨call, front, p⟩ := (main_prefix c ra h).run c ⟨pc, rfl⟩
  have memory : call.σ.mem = writeLog c.σ.mem
      (mainWrites ra (read8 c.σ.mem Layout.sym_embedded_env)) := by
    rw [p.memory, mainLoads, main_log]
  have code : Code.MainLoaded call.σ.mem := Code.main_transport h.code (by
    intro a lo hi
    rw [memory]
    apply writeLog_out
    unfold mainWrites OutL Layout.sym_stack_top Layout.sym_environ
    exact ⟨Or.inl (by omega), Or.inl (by omega), True.intro⟩)
  obtain ⟨out, jump, q⟩ := (call_80001dec call p.good p.tick code).run call ⟨p.pc, rfl⟩
  refine ⟨out, front.trans jump, ⟨?_, q.good, q.tick, q.pc, ?_, ?_, ?_, q.linkReg,
    q.output.trans p.output, ?_⟩⟩
  · intro beforePins
    exact (BlockPost.gpr_present p beforePins (by decide) (by
      change ∀ n ∈ wrChain mainX1dccSeg, n ∈ [14, 2, 10, 15, 1]
      decide)).of_link q.linkReg q.frame
  · rw [q.memory, memory, h.linkReg]; rfl
  · have sp : gprGet call.σ 2 = some (BitVec.ofNat 64 (Layout.sym_stack_top - 16)) :=
      gholds_lookup _ p.regs (by
        simp [evalBlocks, evalBlock, SegEvalState.init, mainX1dccSeg, mainX1dccL,
          mainLoads, runGM, stepGM, stepLdsM, srcVal, lookupG, eraseG, wvalM, mkLine, decodeM,
          LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, Layout.sym_stack_top])
    exact (q.frame .x2 (by decide) (by decide)).trans sp
  · have argv : gprGet call.σ 10 = some (bytesVal .ld (read8 c.σ.mem Layout.sym_embedded_argv)) :=
      gholds_lookup _ p.regs (by
        simp [evalBlocks, evalBlock, SegEvalState.init, mainX1dccSeg, mainX1dccL,
          mainLoads, runGM, stepGM, stepLdsM, srcVal, lookupG, eraseG, wvalM, mkLine, decodeM,
          LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, Layout.sym_stack_top])
    exact (q.frame .x10 (by decide) (by decide)).trans argv

  · intro r noise outside
    have x1 : r ≠ .x1 := by
      intro eq; subst r
      have no := outside 1 (by decide)
      contradiction
    exact (q.frame r noise x1).trans
      (p.frame_subset (writes := [1, 2, 10, 14, 15]) (by decide) r noise outside)

theorem clearWords_above (m : Std.ExtHashMap Nat (BitVec 8)) (base n a : Nat)
    (ha : base + 8 * n ≤ a) : (clearWords m base n)[a]? = m[a]? := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clearWords, writeLog_out _ _ _ (show OutL [(base + 8 * n, 8, 0#64)] a from
      ⟨Or.inr (by omega), True.intro⟩), ih (by omega)]

theorem read8_clearWords_above (m : Std.ExtHashMap Nat (BitVec 8)) (base n a : Nat)
    (ha : base + 8 * n ≤ a) : read8 (clearWords m base n) a = read8 m a := by
  simp (disch := omega) only [Primitives.read8, clearWords_above]

/-- C startup reaches caml_main with the embedded header preserved by BSS clearing. -/
structure CrtCamlMainPost (initial c : Config) : Prop where
  gp : gprGet c.σ 3 = some (BitVec.ofNat 64 Layout.sym_global_pointer)
  gprs : GprPresent initial.σ → GprPresent c.σ
  good : GoodState c.σ
  tick : c.tick < 2
  pc : PCAt (BitVec.ofNat 64 Layout.sym_caml_main) c
  memory : c.σ.mem = writeLog (clearWords initial.σ.mem Layout.sym_bss_start bssWords)
    (mainWrites 0x8000003c#64 (read8 initial.σ.mem Layout.sym_embedded_env))
  stack : gprGet c.σ 2 = some (BitVec.ofNat 64 (Layout.sym_stack_top - 16))
  argv : gprGet c.σ 10 = some (bytesVal .ld (read8 initial.σ.mem Layout.sym_embedded_argv))
  linkReg : gprGet c.σ 1 = some 0x80001df0#64
  output : c.σ.sailOutput = initial.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1, 2, 3, 5, 6, 10, 11, 14, 15], (gprReg n == r) = false) →
    c.σ.regs.get? r = initial.σ.regs.get? r

theorem crt0_to_caml_main (initial : Config) (h : CrtReady initial)
    (mainCode : Code.MainLoaded initial.σ.mem) :
    FnSummary (BitVec.ofNat 64 Layout.sym_start) (fun c => c = initial)
      (CrtCamlMainPost initial) := by
  constructor
  rintro c ⟨pc, eq⟩
  subst c
  obtain ⟨mid, front, m⟩ := (crt0_to_main initial h mainCode).run initial ⟨pc, rfl⟩
  obtain ⟨out, back, p⟩ := (main_to_caml_main mid _ m.ready).run mid ⟨m.pc, rfl⟩
  have env : read8 mid.σ.mem Layout.sym_embedded_env = read8 initial.σ.mem Layout.sym_embedded_env := by
    rw [m.memory]; exact read8_clearWords_above _ _ _ _ (by decide)
  have argv : read8 mid.σ.mem Layout.sym_embedded_argv = read8 initial.σ.mem Layout.sym_embedded_argv := by
    rw [m.memory]; exact read8_clearWords_above _ _ _ _ (by decide)
  refine ⟨out, front.trans back, ⟨(p.frame .x3 (by decide) (by decide)).trans m.gp, (fun h => p.gprs (m.gprs h)), p.good, p.tick, p.pc, ?_, p.stack, ?_, p.linkReg,
    p.output.trans m.output, ?_⟩⟩
  · rw [p.memory, m.ready.linkReg, env, m.memory]; rfl
  · rw [← argv]; exact p.argv

  · intro r noise outside
    exact (p.frame r noise (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega))).trans
      (m.frame r noise (fun n hn => outside n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)))

end OCaml.Vm.Boot.Startup
