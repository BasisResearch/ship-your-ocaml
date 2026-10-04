import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Primitives.MemoryFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Native frame stores preserve every total read lying below the frame. -/
theorem native_log_read_below {sp size log a n} (mem : Std.ExtHashMap Nat (BitVec 8))
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (below : a + n ≤ nativeFrameBase sp size) :
    bytesT (writeLog mem log) a n = bytesT mem a n :=
  bytesT_writeLog_out mem (OCaml.Vm.Sim.outLRange_of_windows inside ⟨Or.inl below, trivial⟩)

/-- A nonnull environment array whose first entry is null, below a native frame.
Startup supplies its two memory observations; query summaries preserve them. -/
structure EmptyEnvironment (sp : BitVec 64) (size : Nat) (env : BitVec 64) (c : Config) : Prop where
  frame : NativeFrame sp size
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  nonnull : env ≠ 0#64
  envWindow : ReadWindow env 8
  empty : bytesT c.σ.mem env.toNat 8 = 0#64
  envBelow : env.toNat + 8 ≤ nativeFrameBase sp size

theorem EmptyEnvironment.same_mem {sp size env before after} (h : EmptyEnvironment sp size env before)
    (memory : after.σ.mem = before.σ.mem) : EmptyEnvironment sp size env after := by
  refine ⟨h.frame, ?_, h.nonnull, h.envWindow, ?_, h.envBelow⟩ <;> rw [memory]
  · exact h.environment
  · exact h.empty

theorem EmptyEnvironment.reframe {sp size env c nextSp nextSize} (h : EmptyEnvironment sp size env c)
    (frame : NativeFrame nextSp nextSize) (below : nativeFrameBase sp size ≤ nativeFrameBase nextSp nextSize) :
    EmptyEnvironment nextSp nextSize env c :=
  ⟨frame, h.environment, h.nonnull, h.envWindow, h.empty, Nat.le_trans h.envBelow below⟩

/-- Any query store log confined to the certified stack frame preserves the
complete empty-environment contract. -/
theorem EmptyEnvironment.stack_log {sp size env before after log} (h : EmptyEnvironment sp size env before)
    (inside : LogInW [⟨nativeFrameBase sp size, sp.toNat⟩] log)
    (memory : after.σ.mem = writeLog before.σ.mem log) : EmptyEnvironment sp size env after := by
  refine ⟨h.frame, ?_, h.nonnull, h.envWindow, ?_, h.envBelow⟩
  · rw [memory, native_log_read_below before.σ.mem inside ?_]
    · exact h.environment
    · have lower := h.frame.lower
      have globalBound : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
      unfold nativeFrameBase
      omega
  · rw [memory, native_log_read_below before.σ.mem inside h.envBelow]
    exact h.empty
end OCaml.Vm.Boot.Startup
