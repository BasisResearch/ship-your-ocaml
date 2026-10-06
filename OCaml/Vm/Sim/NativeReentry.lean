import OCaml.Vm.Sim.RaiseLongjmp
import OCaml.Vm.Sim.ReentryQuiet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def reentryControlWords (c : Config) : List Nat :=
  [Layout.sym_Caml_state, (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
    (word c Layout.sym_Caml_state).toNat + Layout.off_trap_barrier,
    (word c Layout.sym_Caml_state).toNat + Layout.off_backtrace_active]

/-- Raising may change extern_sp and the exception bucket, while retaining re-entry controls. -/
theorem ReentryMemory.frame_log {nativeSp : Nat} {c after : Config} {log : List WEntry}
    (h : ReentryMemory nativeSp c) (memory : after.σ.mem = writeLog c.σ.mem log)
    (outside : ∀ a ∈ reentryControlWords c, OutLRange log a 8) : ReentryMemory nativeSp after := by
  have read : ∀ a ∈ reentryControlWords c, word after a = word c a := by
    intro a member
    rw [word, memory]
    exact bytesT_writeLog_out _ (outside a member)
  have domain := read Layout.sym_Caml_state (by simp [reentryControlWords])
  refine ⟨h.savedRootsRead, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [domain] using h.reads
  · simpa only [domain] using h.rootsWrite
  · rw [domain, read _ (by simp [reentryControlWords]), read _ (by simp [reentryControlWords])]
    exact h.quiet
  · rw [domain, read _ (by simp [reentryControlWords])]
    exact h.backtrace
  · constructor
    · simpa only [reentryLog, domain, OutLRange] using h.imageOutside.text
    · simpa only [reentryLog, domain, OutLRange] using h.imageOutside.rodata

/-- Canonical memory/output view of a checked native write log. -/
def nativeMemoryView (before : Config) (log : List WEntry) : Config :=
  { before with σ := { before.σ with mem := writeLog before.σ.mem log } }

/-- Any checked native raise can reuse the actual quiet interpreter re-entry. -/
theorem native_reentry {entry : BitVec 64} {log : List WEntry} {saved : Nat → BitVec 64}
    {nativeSp : Nat} {c : Config}
    (summary : FnSummary entry (fun start => start = c) (NativeRaisePost log saved c))
    (memory : ReentryMemory nativeSp c)
    (outside : ∀ a ∈ reentryControlWords c, OutLRange log a 8)
    (returnPc : saved 1 = 0x80001e80#64) (returnSp : saved 2 = BitVec.ofNat 64 nativeSp) :
    FnSummary entry (fun start => start = c) (ReentryControl nativeSp (nativeMemoryView c log)) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, nativeRun, native⟩ := summary.run c ⟨pc, rfl⟩
  have input : ReentryQuietInput nativeSp 1#64 middle := {
    toReentryMemory := memory.frame_log native.memory outside
    good := native.good, image := native.image, tick := native.tick
    pc := native.pc.trans (congrArg some returnPc)
    stack := (native.registers 2 (by decide)).trans (congrArg some returnSp)
    resultReg := native.result, nonzero := by decide }
  obtain ⟨count, after, run, post⟩ := reentry_quiet input
  exact ⟨after, nativeRun.trans run.toSteps, post.toReentryControl.before_read native.memory native.frame.out
    (native.frame.frame _ (by decide))⟩

end OCaml.Vm.Sim
