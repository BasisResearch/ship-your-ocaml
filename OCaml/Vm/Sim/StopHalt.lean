import OCaml.Vm.Sim.StopCaller
import OCaml.Vm.Primitives.ExitPath.Machine

/-!
# STOP's process exit: `caml_do_exit(0)` halts

`stop_do_exit_summary` discharges STOP's named exit obligation
(`StopDoExitSummary`, `StopCaller.lean`) from a1-prims' machine run of
`caml_do_exit` (`ExitPath.do_exit_halts`): at caml_do_exit's entry with
status 0, the machine halts with exit code 0 and the console unchanged.

The exit facts the run needs are named in `StopExitReady`: the four
runtime globals that select the quiet exit path, the exit's native stack
window, and the platform facts at caml_do_exit's entry (all GPRs present,
HTIF idle). The globals transfer from the STOP state because STOP's three
runtime stores miss them.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ExitPath LeanRV64DExecutable

/-- Total eight-byte reads outside a write log are unchanged. -/
theorem read8_writeLog_out (m : Std.ExtHashMap Nat (BitVec 8)) {log : List WEntry} {a : Nat}
    (h : OutLRange log a 8) : Primitives.read8 (writeLog m log) a = Primitives.read8 m a := by
  simp only [Primitives.read8]
  rw [writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega)),
    writeLog_out _ _ _ (outL_of_range h (by omega) (by omega))]

/-- **What STOP's exit needs**, at the STOP state `before`. -/
structure StopExitReady (before : Config) (nativeSp : Nat) (vmSp : BitVec 64) : Prop where
  /-- the quiet exit path: no GC verbosity, no cleanup, no atexit, no stdio handler -/
  globals : ExitGlobals before
  /-- STOP's runtime stores miss those globals -/
  globalsOutside : ∀ g ∈ [verbGc, cleanupOnExit, atexitList, stdioExitHandler],
    OutLRange (stopLog nativeSp vmSp before) g.toNat 8
  /-- caml_do_exit's native stack window below caml_main's caller frame -/
  layout : ExitLayout doExitDepth (BitVec.ofNat 64 (nativeSp + Layout.interpFrameBytes + Layout.camlMainFrameBytes))
  /-- the platform facts at caml_do_exit's entry -/
  platform : ∀ after, StopExitCallPost before nativeSp vmSp after →
    (∀ n, 1 ≤ n → n ≤ 31 → (gprGet after.σ n).isSome) ∧
      after.σ.regs.get? Register.htif_payload_writes = some (0#4)

/-- **STOP's exit obligation**, from caml_do_exit's machine run. -/
theorem stop_do_exit_summary {before : Config} {nativeSp : Nat} {vmSp : BitVec 64}
    (ready : StopExitReady before nativeSp vmSp) :
    StopDoExitSummary before nativeSp vmSp (output before.σ) := by
  constructor
  intro after post
  obtain ⟨present, idle⟩ := ready.platform after post
  have same (g : BitVec 64) (hg : g ∈ [verbGc, cleanupOnExit, atexitList, stdioExitHandler]) :
      Primitives.read8 after.σ.mem g.toNat = Primitives.read8 before.σ.mem g.toNat := by
    rw [post.memory]; exact read8_writeLog_out _ (ready.globalsOutside g hg)
  have globals : ExitGlobals after := by
    obtain ⟨q, c, a, h⟩ := ready.globals
    exact ⟨by rw [same _ (by simp)]; exact q, by rw [same _ (by simp)]; exact c,
      by rw [same _ (by simp)]; exact a, by rw [same _ (by simp)]; exact h⟩
  have input : DoExitInput 0x80001df8#64
      (BitVec.ofNat 64 (nativeSp + Layout.interpFrameBytes + Layout.camlMainFrameBytes)) 0#64 after :=
    { good := post.good, image := post.image, minstret := post.good.minstret,
      raReg := post.returnAddress, aligned := by decide, tick := post.tick,
      ok := ⟨post.good, post.tick, idle, fun n hn => by
        have : 1 ≤ n ∧ n ≤ 31 := by simp [exitReads] at hn; omega
        exact present n this.1 this.2⟩,
      stack := post.stack, arg := post.status, layout := ready.layout, globals := globals }
  have halts := do_exit_halts input post.pc
  rw [exitStatus_zero] at halts
  have out : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ := by
    simp only [Vsa.Machine.output, post.output]
  rwa [out] at halts

end OCaml.Vm.Sim
