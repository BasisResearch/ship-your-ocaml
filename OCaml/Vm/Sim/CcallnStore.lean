import OCaml.Vm.Sim.Ccall1Store
import OCaml.Vm.Sim.StackPush

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- C_CALLN pushes its accumulator, saves the VM frame, publishes extern_sp,
and saves the next bytecode PC in the native stack frame. -/
def ccallnLog (sp domain nativeSp : Nat) (next env accu : BitVec 64) : List WEntry :=
  [(sp - 8, 8, accu), (sp - 24, 8, env), (sp - 16, 8, next),
   (domain + Layout.off_extern_sp, 8, BitVec.ofNat 64 (sp - 24)),
   (nativeSp + 88, 8, next)]

def ccallnWindows (sp domain nativeSp : Nat) : List W :=
  [⟨sp - 24, sp⟩, ⟨domain + Layout.off_extern_sp, domain + Layout.off_extern_sp + 8⟩,
   ⟨nativeSp + 88, nativeSp + 96⟩]

/-- Static separation and writable geometry for the variable-arity call's
five stores. The invariant-to-arm adapter must supply these facts. -/
structure CcallnWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp domain nativeSp : Nat) (next env accu : BitVec 64) : Prop where
  room : 24 ≤ sp
  stackNat : sp < 2^64
  domainNat : domain + Layout.off_extern_sp < 2^64
  nativeNat : nativeSp + 88 < 2^64
  accuWindow : WriteWindow (BitVec.ofNat 64 (sp - 8)) 8
  envWindow : WriteWindow (BitVec.ofNat 64 (sp - 24)) 8
  pcWindow : WriteWindow (BitVec.ofNat 64 (sp - 16)) 8
  externWindow : WriteWindow (BitVec.ofNat 64 (domain + Layout.off_extern_sp)) 8
  nativeWindow : WriteWindow (BitVec.ofNat 64 (nativeSp + 88)) 8
  externApart : sp ≤ domain + Layout.off_extern_sp ∨ domain + Layout.off_extern_sp + 8 ≤ sp - 24
  nativeApart : sp ≤ nativeSp + 88 ∨ nativeSp + 96 ≤ sp - 24
  externNativeApart : domain + Layout.off_extern_sp + 8 ≤ nativeSp + 88 ∨
    nativeSp + 96 ≤ domain + Layout.off_extern_sp
  payload : PayloadOutside (ccallnLog sp domain nativeSp next env accu) P s c pl cp sp
  image : ImageOutside (ccallnLog sp domain nativeSp next env accu)
  bindings : BindingsOutside (ccallnLog sp domain nativeSp next env accu) P c

/-- Named readback facts supplied by the exact setup store log. -/
structure CcallnStored (sp domain nativeSp : Nat) (next env accu : BitVec 64)
    (c : Config) : Prop where
  argument : word c (sp - 8) = accu
  environment : word c (sp - 24) = env
  stack : word c (domain + Layout.off_extern_sp) = BitVec.ofNat 64 (sp - 24)
  pc : word c (nativeSp + 88) = next

/-- Reuse the indexed write-log readback theorem for every saved word. -/
theorem CcallnWriteOk.stored {P s c pl cp sp domain nativeSp next env accu}
    (h : CcallnWriteOk P s c pl cp sp domain nativeSp next env accu) {after : Config}
    (memory : after.σ.mem = writeLog c.σ.mem (ccallnLog sp domain nativeSp next env accu)) :
    CcallnStored sp domain nativeSp next env accu after := by
  have room := h.room
  have ext := h.externApart
  have native := h.nativeApart
  have extNative := h.externNativeApart
  have read (i a : Nat) (w : BitVec 64)
      (selected : (ccallnLog sp domain nativeSp next env accu)[i]? = some (a, 8, w))
      (later : OutLRange ((ccallnLog sp domain nativeSp next env accu).drop (i + 1)) a 8) :
      word after a = w := by
    rw [word, memory]
    exact word_writeLog_at _ _ i _ _ selected later
  constructor
  · apply read 0 _ _ rfl
    simp only [ccallnLog, List.drop, OutLRange, and_true]
    omega
  · apply read 1 _ _ rfl
    simp only [ccallnLog, List.drop, OutLRange, and_true]
    omega
  · apply read 3 _ _ rfl
    simp only [ccallnLog, List.drop, OutLRange, and_true]
    omega
  · exact read 4 _ _ rfl trivial

/-- The generated setup writes stay in its VM/domain/native frame windows. -/
theorem ccalln_log_in {sp domain nativeSp : Nat} (next env accu : BitVec 64) (room : 24 ≤ sp) :
    LogInW (ccallnWindows sp domain nativeSp) (ccallnLog sp domain nativeSp next env accu) := by
  simp only [ccallnLog, ccallnWindows, LogInW, InsideW, or_false, and_true]
  omega

/-- Preserve allocator/runtime state by the exact generated write footprint. -/
theorem ccalln_runtime {L : OCaml.Layout} {c after : Config} {sp domain nativeSp : Nat}
    {next env accu : BitVec 64} (stable : WindowStable L.runtimeOk (ccallnWindows sp domain nativeSp))
    (runtime : L.runtimeOk c) (room : 24 ≤ sp)
    (memory : after.σ.mem = writeLog c.σ.mem (ccallnLog sp domain nativeSp next env accu)) :
    L.runtimeOk after := by
  apply stable c after _ runtime
  rw [memory]
  apply frameOn_writeLog
  exact ccalln_log_in next env accu room

/-- The argument array consists of the pushed accumulator followed by a
represented prefix of the original stack. Reuse the existing stack predicate. -/
theorem ccalln_array {P : Prog} {s : St} {c after : Config} {pl : Place} {cp : ChanPlace}
    {sp high domain nativeSp count : Nat} {next env accu : BitVec 64}
    (h : VmPayload P s c pl cp sp high)
    (space : CcallnWriteOk P s c pl cp sp domain nativeSp next env accu)
    (repr : valWord pl s.accu = some accu)
    (memory : after.σ.mem = writeLog c.σ.mem (ccallnLog sp domain nativeSp next env accu)) :
    StackRepr after pl (sp - 8) (sp - 8 + 8 * (s.accu :: s.stack.take count).length)
      (s.accu :: s.stack.take count) := by
  refine ⟨rfl, ?_⟩
  intro i v selected
  cases i with
  | zero =>
    cases Option.some.inj selected
    simpa only [Nat.mul_zero, Nat.add_zero, (space.stored memory).argument] using repr
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_take] at selected
    split at selected
    next lt =>
      have preserved : word after (sp + 8 * i) = word c (sp + 8 * i) := by
        simpa only [word, bytesT_eight_eq, LeanRV64DExecutable.Functions.sign_extend,
          Sail.BitVec.signExtend, BitVec.signExtend_eq] using
          word_read_writeLog_out (space.payload.stack i v selected) memory
      have address : sp - 8 + 8 * (i + 1) = sp + 8 * i := by have := space.room; omega
      rw [address, preserved]
      exact h.stack.2 i v selected
    next => cases selected

end OCaml.Vm.Sim
