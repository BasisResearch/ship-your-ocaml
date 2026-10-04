import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.RaiseQuietState
import OCaml.Vm.Sim.Longjmp

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Interpreter re-entry restores the roots saved before setjmp. -/
def reentryLog (nativeSp : Nat) (c : Config) : List WEntry :=
  [((word c Layout.sym_Caml_state).toNat + Layout.off_local_roots, 8,
    word c (nativeSp + Layout.interpSavedRootsOffset))]

def reentryReadOffsets : List Nat :=
  [Layout.off_trapsp, Layout.off_trap_barrier, Layout.off_extern_sp,
    Layout.off_exn_bucket, Layout.off_backtrace_active]

/-- The restored local-roots slot is disjoint from every domain field read on re-entry. -/
theorem reentry_read_outside (nativeSp : Nat) (c : Config) (offset : Nat)
    (member : offset ∈ reentryReadOffsets) :
    OutLRange (reentryLog nativeSp c) ((word c Layout.sym_Caml_state).toNat + offset) 8 := by
  simp only [reentryReadOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [reentryLog, OutLRange, and_true]
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Layout.off_trapsp, Layout.off_trap_barrier, Layout.off_extern_sp,
      Layout.off_exn_bucket, Layout.off_backtrace_active, Layout.off_local_roots] <;> omega

/-- Memory readiness for the quiet nonlocal-return path; independent of registers and PC. -/
structure ReentryMemory (nativeSp : Nat) (c : Config) : Prop where
  savedRootsRead : RamReadAt (nativeSp + Layout.interpSavedRootsOffset) 8
  reads : ∀ offset ∈ reentryReadOffsets, RamReadAt ((word c Layout.sym_Caml_state).toNat + offset) 8
  rootsWrite : RamWriteAt ((word c Layout.sym_Caml_state).toNat + Layout.off_local_roots) 8
  quiet : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).ult
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trap_barrier)) = true
  backtrace : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_backtrace_active) = 0#64
  imageOutside : ImageOutside (reentryLog nativeSp c)

/-- Read-only native restoration retains all re-entry memory facts. -/
theorem ReentryMemory.frame {nativeSp : Nat} {c after : Config}
    (h : ReentryMemory nativeSp c) (memory : after.σ.mem = c.σ.mem) :
    ReentryMemory nativeSp after := by
  have words (a : Nat) : word after a = word c a := by simp only [word, memory]
  refine ⟨h.savedRootsRead, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [words] using h.reads
  · simpa only [words] using h.rootsWrite
  · simpa only [words] using h.quiet
  · simpa only [words] using h.backtrace
  · simpa only [reentryLog, words] using h.imageOutside

/-- Scalar runtime conditions at the setjmp continuation for the quiet raising path.
The primitive raising summary and the native invocation invariant supply these facts. -/
structure ReentryQuietInput (nativeSp : Nat) (result : BitVec 64) (c : Config) : Prop
    extends ReentryMemory nativeSp c where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x80001e80#64)
  tick : c.tick < 2
  stack : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  resultReg : gpr c 10 = some result
  nonzero : result ≠ 0#64

/-- Re-entry exposes the actual exception and VM stack at the common handler check. -/
structure ReentryControl (nativeSp : Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (0x80001ed4#64)
  domain : gpr after 15 = some (word before Layout.sym_Caml_state)
  trap : gpr after 14 = some (word before ((word before Layout.sym_Caml_state).toNat + Layout.off_trapsp))
  vmStack : gpr after Layout.reg_sp = some (word before ((word before Layout.sym_Caml_state).toNat + Layout.off_extern_sp))
  exceptionValue : gpr after Layout.reg_accu = some (word before ((word before Layout.sym_Caml_state).toNat + Layout.off_exn_bucket))
  nativeStack : gpr after 2 = some (BitVec.ofNat 64 nativeSp)
  memory : after.σ.mem = writeLog before.σ.mem (reentryLog nativeSp before)
  output : after.σ.sailOutput = before.σ.sailOutput

/-- The direct interpreter re-entry additionally preserves its native register frame. -/
structure ReentryQuietPost (nativeSp : Nat) (before after : Config) : Prop
    extends ReentryControl nativeSp before after where
  frame : StepFrameOut ([Register.x8, Register.x12, Register.x13, Register.x14, Register.x15, Register.x9, Register.x21] ++ noiseRegs) before.σ after.σ

/-- Rebase the final observations through a preceding read-only native restoration. -/
theorem ReentryControl.before_read {nativeSp : Nat} {before middle after : Config}
    (h : ReentryControl nativeSp middle after) (memory : middle.σ.mem = before.σ.mem)
    (output : middle.σ.sailOutput = before.σ.sailOutput) :
    ReentryControl nativeSp before after := by
  have words (a : Nat) : word middle a = word before a := by simp only [word, memory]
  refine ⟨h.good, h.image, h.tick, h.pc, ?_, ?_, ?_, ?_, h.nativeStack, ?_, h.output.trans output⟩
  · simpa only [words] using h.domain
  · simpa only [words] using h.trap
  · simpa only [words] using h.vmStack
  · simpa only [words] using h.exceptionValue
  · simpa only [reentryLog, words, memory] using h.memory

end OCaml.Vm.Sim
