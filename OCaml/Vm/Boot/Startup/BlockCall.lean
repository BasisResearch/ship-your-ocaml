import OCaml.Vm.Boot.Startup.PrefixCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A generated block followed by its direct call: the block summary plus the
call seam, for every "set up arguments, then `jal`" span. -/
theorem block_then_call {entry : BitVec 64} {writes : List Nat} {log : List WEntry} {value : BitVec 64}
    {regs : GRegs} {a : CallInstr} (c : Config) (shape : CallShape a) (decode : CallDecode a)
    (pins : ∀ d : Config, ExecutableImage d → CallPins a d)
    (front : FnSummary entry (fun d => d = c) (WriteRegistersPost writes log c a.pc value regs))
    (keys : KeysOK (keysG regs)) (avoid : KeysAvoidRa regs) (result : lookupG 10 regs = some value) :
    FnSummary entry (fun d => d = c)
      (WriteRegistersPost (writes ++ [1]) log c a.target value ((1, a.link) :: regs)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary shape decode request (pins _ setup.image) setup.good
    setup.image setup.tick setup.minstret _ setup.regs keys avoid result).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩

/-- Two write-log summaries in sequence: writes and logs concatenate. -/
theorem write_post_seq {w1 w2 : List Nat} {l1 l2 : List WEntry} {before mid after : Config}
    {pc1 v1 pc2 v2 : BitVec 64} {r1 r2 : GRegs}
    (front : WriteRegistersPost w1 l1 before pc1 v1 r1 mid) (back : WriteRegistersPost w2 l2 mid pc2 v2 r2 after) :
    WriteRegistersPost (w1 ++ w2) (l1 ++ l2) before pc2 v2 r2 after := by
  have effects := front.toEffectPost.trans back.toEffectPost
  exact ⟨⟨effects.good, effects.image, effects.minstret, effects.tick, effects.pc, effects.result,
    by rw [back.memory, front.memory, writeLog_append], effects.output, effects.frame⟩, back.regs⟩

/-- A write-log summary followed by another from its end state. -/
theorem blocks_then {entry pc1 v1 pc2 v2 : BitVec 64} {w1 w2 : List Nat} {l1 l2 : List WEntry} {r1 r2 : GRegs}
    (c : Config) (front : FnSummary entry (fun d => d = c) (WriteRegistersPost w1 l1 c pc1 v1 r1))
    (back : ∀ d, WriteRegistersPost w1 l1 c pc1 v1 r1 d →
      FnSummary pc1 (fun e => e = d) (WriteRegistersPost w2 l2 d pc2 v2 r2)) :
    FnSummary entry (fun d => d = c) (WriteRegistersPost (w1 ++ w2) (l1 ++ l2) c pc2 v2 r2) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨mid, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, done⟩ := (back mid setup).run mid ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, write_post_seq setup done⟩
end OCaml.Vm.Boot.Startup
