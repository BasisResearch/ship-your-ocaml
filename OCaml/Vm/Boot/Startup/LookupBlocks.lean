import OCaml.Vm.Boot.Startup.PrimitiveLookupRows
import OCaml.Vm.Boot.Startup.PrimitiveLookupCalls
import OCaml.Vm.Primitives.Blocks
import Vsa.Sim.ChainFactsTac

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

structure LookupReady (c : Config) : Prop where
  good : GoodState c.σ
  code : Code.Caml_build_primitive_tableLoaded c.σ.mem
  tick : c.tick < 2

/-- Prepare the required name in a0 before the generated strcmp call. -/
theorem lookup_argument_input {c : Config} {name : BitVec 64}
    (h : LookupReady c) (hn : gprGet c.σ 9 = some name) :
    BlockInput caml_build_primitive_tableX4e30Seg 0x80024e30#64
      (caml_build_primitive_tableX4e30L name) [] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hn, True.intro⟩
  keys := by show KeysOK [9]; decide
  shape := by show ChainOK 0x80024e30#64 [9] caml_build_primitive_tableX4e30Seg; decide
  tick := h.tick
  facts := by chain_facts h.code with "Vsa.Sim.Code.caml_build_primitive_table_at_"

def lookupBranch (taken : Bool) : List BBlock :=
  if taken then caml_build_primitive_tableX4e38TSeg else caml_build_primitive_tableX4e38FSeg

/-- The post-strcmp branch keeps all general registers and memory unchanged. -/
structure LookupBranchPost (taken : Bool) (before after : Config) : Prop where
  ready : LookupReady after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (if taken then 0x80024e1c#64 else 0x80024e3c#64) after
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem lookup_branch_input {c : Config} {result : BitVec 64} {taken : Bool}
    (h : LookupReady c) (hr : gprGet c.σ 10 = some result)
    (branch : guardB .BNE result 0 = taken) :
    BlockInput (lookupBranch taken) 0x80024e38#64
      (caml_build_primitive_tableX4e38TL result) [] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hr, True.intro⟩
  keys := by show KeysOK [10]; decide
  shape := by
    change ChainOK 0x80024e38#64 [10] (lookupBranch taken)
    cases taken <;> decide
  tick := h.tick
  facts := by
    cases taken <;> chain_facts h.code with "Vsa.Sim.Code.caml_build_primitive_table_at_"
    all_goals exact branch

theorem lookup_branch (c : Config) (result : BitVec 64) (taken : Bool)
    (h : LookupReady c) (hr : gprGet c.σ 10 = some result)
    (branch : guardB .BNE result 0 = taken) :
    FnSummary 0x80024e38#64 (fun d => d = c) (LookupBranchPost taken c) := by
  apply (block_summary _ _ _ _ _ (lookup_branch_input h hr branch)).weaken (fun _ hc => hc)
  intro d post
  have empty : (evalBlocks (lookupBranch taken)
      (SegEvalState.init (caml_build_primitive_tableX4e38TL result) [])).log = [] := by
    cases taken <;> rfl
  have hm := post.memory
  rw [empty] at hm
  change d.σ.mem = c.σ.mem at hm
  refine ⟨⟨post.good, ?_, post.tick⟩, hm, ?_, post.output, ?_⟩
  · rw [hm]; exact h.code
  · have pc := post.pc
    cases taken <;> exact pc
  · intro r noise
    apply post.frame r noise
    cases taken <;> simp [lookupBranch, caml_build_primitive_tableX4e38TSeg,
      caml_build_primitive_tableX4e38FSeg, wrChain, wrRegsM]

end OCaml.Vm.Boot.Startup
