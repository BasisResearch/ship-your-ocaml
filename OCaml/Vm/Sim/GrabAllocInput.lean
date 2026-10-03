import OCaml.Vm.Sim.GrabInitialize

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def grabSuffixLog (a code : Nat) : List WEntry :=
  [(a, 8, BitVec.ofNat 64 code), (a + 8, 8, 5#64)]

def grabAllocationLog (c : Config) (pl : Place) (s : St) (sp a domain : Nat) (env : BitVec 64) : List WEntry :=
  grabReserveLog domain a ++ partialClosureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc - 1))) env
    (stackWords c sp (1 + s.extra))

/-- The native setup, copy and suffix logs are exactly the allocation effect. -/
theorem grab_allocation_log_parts (c : Config) (pl : Place) (s : St) (sp a domain : Nat) (env : BitVec 64) :
    (grabSetupLog domain a s.extra env ++ valueLog (a + 24) (stackWords c sp (1 + s.extra))) ++
      grabSuffixLog a (pl.codeBase + 4 * (s.pc - 1)) = grabAllocationLog c pl s sp a domain env := by
  have length : (stackWords c sp (1 + s.extra)).length + 3 = s.extra + 4 := by simp [stackWords]; omega
  simp only [grabAllocationLog, partialClosureLog, grabSetupLog, grabInitLog, grabSuffixLog,
    length, List.append_assoc]

/-- Remaining G1 geometry and separation needed by the complete allocating arm.
All address-bearing fields are scalar memory observations or layout conditions. -/
structure GrabAllocInput (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high a domain limit : Nat) (env : BitVec 64) : Prop where
  nursery : GrabNurseryInput s.extra a domain limit c
  initializer : GrabInitInput sp s.extra a domain env c
  allocation : GrabWriteOk P s c pl cp sp high a (grabAllocationLog c pl s sp a domain env)
  codeWrite : RamWriteAt a 8
  arityWrite : RamWriteAt (a + 8) 8
  frameReads : ReturnFrameReads (sp + 8 * (1 + s.extra))
  pcPositive : 0 < s.pc

/-- The post-copy suffix returns a represented initialized partial closure. -/
theorem grab_allocation_layout {P : Prog} {s : St} {before after : Config} {pl : Place} {cp : ChanPlace}
    {sp high a domain limit : Nat} {env : BitVec 64} {dest : Nat} {savedEnv : Val} {savedExtra : BitVec 63} {rest : List Val}
    (data : VmReprAt P s before pl cp sp high) (space : GrabAllocInput P s before pl cp sp high a domain limit env)
    (environment : valWord pl s.env = some env)
    (stack : s.stack.drop (1 + s.extra) = .code dest :: savedEnv :: .int savedExtra :: rest)
    (memory : after.σ.mem = writeLog before.σ.mem (grabAllocationLog before pl s sp a domain env)) :
    ObjAt after pl cp a (grabClosure s) := by
  have bound : 1 + s.extra ≤ s.stack.length := by
    have lengths := congrArg List.length stack
    simp only [List.length_drop, List.length_cons] at lengths
    omega
  let reserved : Config := {before with σ := {before.σ with mem := writeLog before.σ.mem (grabReserveLog domain a)}}
  have objectMemory : after.σ.mem = writeLog reserved.σ.mem
      (partialClosureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc - 1))) env (stackWords before sp (1 + s.extra))) := by
    rw [memory, grabAllocationLog, writeLog_append]
  exact partial_closure_layout space.nursery.room
    (by have small := space.nursery.small; simp only [stackWords, List.length_map, List.length_range]; omega)
    environment (stack_value_words data.stack bound) objectMemory

end OCaml.Vm.Sim
