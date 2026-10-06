import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Sim.ReadOnly
import OCaml.Vm.Primitives.ImageFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Setup_for_c_call saves env and the next bytecode PC, then publishes extern_sp. -/
def ccall1Log (sp domain : Nat) (next env : BitVec 64) : List WEntry :=
  [(sp - 16, 8, env), (sp - 8, 8, next),
   (domain + Layout.off_extern_sp, 8, BitVec.ofNat 64 (sp - 16))]

/-- The caller's temporary stack frame and the domain's extern_sp field. -/
def ccall1Windows (sp domain : Nat) : List W :=
  [⟨sp - 16, sp⟩, ⟨domain + Layout.off_extern_sp, domain + Layout.off_extern_sp + 8⟩]

/-- Static separation for C_CALL1's three generated stores. The full loop
invariant must supply these facts; no machine execution is assumed. -/
structure Ccall1WriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp domain : Nat) (next env : BitVec 64) : Prop where
  room : 16 ≤ sp
  stackNat : sp < 2^64
  domainNat : domain + Layout.off_extern_sp < 2^64
  envWindow : WriteWindow (BitVec.ofNat 64 (sp - 16)) 8
  pcWindow : WriteWindow (BitVec.ofNat 64 (sp - 8)) 8
  externWindow : WriteWindow (BitVec.ofNat 64 (domain + Layout.off_extern_sp)) 8
  externApart : sp ≤ domain + Layout.off_extern_sp ∨ domain + Layout.off_extern_sp + 8 ≤ sp - 16
  payload : PayloadOutside (ccall1Log sp domain next env) P s c pl cp sp
  image : ImageOutside (ccall1Log sp domain next env)
  young : YoungOutside (ccall1Log sp domain next env) c
  bindings : BindingsOutside (ccall1Log sp domain next env) P c

/-- The three writes establish the return frame's exact saved environment word. -/
theorem Ccall1WriteOk.savedEnv {P s c pl cp sp domain next env}
    (h : Ccall1WriteOk P s c pl cp sp domain next env) {after : Config}
    (memory : after.σ.mem = writeLog c.σ.mem (ccall1Log sp domain next env)) :
    word after (sp - 16) = env := by
  rw [word, memory]
  apply word_writeLog_at _ _ 0 _ _ rfl
  simp only [ccall1Log, List.drop, OutLRange, and_true]
  have room := h.room
  have apart := h.externApart
  omega

/-- The final store publishes exactly the temporary VM stack pointer. -/
theorem ccall1_savedStack {c after : Config} {sp domain : Nat} {next env : BitVec 64}
    (memory : after.σ.mem = writeLog c.σ.mem (ccall1Log sp domain next env)) :
    word after (domain + Layout.off_extern_sp) = BitVec.ofNat 64 (sp - 16) := by
  rw [word, memory]
  exact word_writeLog_at _ _ 2 _ _ rfl trivial

/-- Setup's exact write log is confined to its named runtime windows. -/
theorem ccall1_log_in {sp domain : Nat} (next env : BitVec 64) (room : 16 ≤ sp) :
    LogInW (ccall1Windows sp domain) (ccall1Log sp domain next env) := by
  simp only [ccall1Log, ccall1Windows, LogInW, InsideW, or_false, and_true]
  omega

/-- Preserve the runtime invariant using the same frame law as stack writes. -/
theorem ccall1_runtime {L : OCaml.Layout} {c after : Config} {sp domain : Nat}
    {next env : BitVec 64} (stable : WindowStable L.runtimeOk (ccall1Windows sp domain))
    (runtime : L.runtimeOk c) (room : 16 ≤ sp)
    (memory : after.σ.mem = writeLog c.σ.mem (ccall1Log sp domain next env)) :
    L.runtimeOk after := by
  apply stable c after _ runtime
  rw [memory]
  apply frameOn_writeLog
  exact ccall1_log_in next env room

end OCaml.Vm.Sim
