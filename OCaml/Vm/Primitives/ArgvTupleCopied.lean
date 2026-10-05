import OCaml.Vm.Primitives.ArgvTupleFast
import OCaml.Vm.Primitives.ByteCopyLog

namespace OCaml.Vm.Primitives.ArgvTuple
open Vsa.Machine Vsa.Sim VsaIris.Inst

/-- A first-order memory view used to state a subsequent call's requirements.
It is not an assertion that an execution has taken place. -/
def memoryView (c : Config) (mem : Std.ExtHashMap Nat (BitVec 8)) : Config :=
  { c with σ := { c.σ with mem := mem } }

theorem memoryView_mem (c : Config) (mem : Std.ExtHashMap Nat (BitVec 8)) :
    (memoryView c mem).σ.mem = mem := rfl

theorem memoryView_gpr (c : Config) (mem : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) :
    gpr (memoryView c mem) n = gpr c n := rfl

def copiedLog (R : Nat → BitVec 64) (domain roots young : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) : List WEntry :=
  prepareLog R domain roots ++ StringCopy.completeLog prepare_call.link (frameSp (R 2)) a len g domain young

/-- Scalar access and static constructor obligations for the first call.
The ABI and actual call execution are derived from the generated boundaries. -/
structure CopyStageInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (bd be br : List (BitVec 8)) (a len : Nat) (g : Nat → BitVec 8)
    (young limit : BitVec 64) (c : Config) : Prop extends LeafInput (R 1) c where
  libraryGood : VsaOk live c
  regs : GHolds c.σ (prepare_input R)
  access : AccessPlan c.σ.mem (prepare_input R) [bd, be, br] prepare_body
  outside : ImageOutside (prepareLog R (bytesVal .ld bd) (bytesVal .ld br))
  source : bytesVal .ld be = BitVec.ofNat 64 a
  copyMemory : StringCopy.CopyMemory live Dt DA prepare_call.link (frameSp (R 2)) a len g
    (bytesVal .ld bd) young limit
    (memoryView c (writeLog c.σ.mem (prepareLog R (bytesVal .ld bd) (bytesVal .ld br))))

structure CopyStagePost (live : Nat → Prop) (R : Nat → BitVec 64) (domain roots young : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) (before after : Config) : Prop
    extends LeafInput prepare_call.link after where
  libraryGood : VsaOk live after
  pc : pcOf after = some prepare_call.link
  result : gpr after 10 = some (StringCopy.resultWord young len)
  stack : gpr after 2 = some (frameSp (R 2))
  rootsReg : gpr after 8 = some roots
  domainReg : gpr after 9 = some DoubleAllocation.domainGlobal
  sizeReg : gpr after 18 = some 2#64
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (copiedLog R domain roots young a len g))
  shell : StringAllocation.StringShell after (StringCopy.resultWord young len).toNat len
  bytes : ∀ i, i < len → byte after ((StringCopy.resultWord young len).toNat + i) = g (a + i)
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 →
    n ∉ ([1,2,8,9,10,13,14,15,18] ++ StringCopy.copyWrites) → gpr after n = gpr before n

theorem argv_copy_stage {live Dt DA R bd be br a len g young limit c}
    (h : CopyStageInput live Dt DA R bd be br a len g young limit c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_argv) (fun d => d = c)
      (CopyStagePost live R (bytesVal .ld bd) (bytesVal .ld br) young a len g c) := by
  apply summary_bind (prepare_fast c R bd be br h.toLeafInput h.regs h.access h.outside) (fun _ p => p.pc)
  intro prepared p
  let args : GRegs := [(2, frameSp (R 2)), (8, bytesVal .ld br),
    (9, DoubleAllocation.domainGlobal), (18, 2#64), (10, BitVec.ofNat 64 a)]
  have argsHold : GHolds prepared.σ args := holds_project p.regs (by
    simp [args, prepare_regs, frameSp, lookupG, h.source, BitVec.sub_eq_add_neg])
  have J := call_registers_summary prepare_call_shape prepare_call_decode prepared (prepare_call_pins p.image)
    p.good p.image p.tick p.minstret args argsHold (by change KeysOK [2,8,9,18,10]; decide)
    (by simp [KeysAvoidRa, args, keysG]) (by rfl)
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good1 := p.vsaOk h.libraryGood (by decide) (by simp [prepare_regs, keysG])
  have good2 := q.vsaOk (log := []) good1 (by decide) (by simp [args, keysG])
  have leaf : LeafInput prepare_call.link entered :=
    ⟨q.good, q.image, q.minstret, gholds_lookup _ q.regs rfl, by decide, q.tick⟩
  have stack : gpr entered 2 = some (frameSp (R 2)) := gholds_lookup _ q.regs rfl
  have memory : entered.σ.mem = writeLog c.σ.mem (prepareLog R (bytesVal .ld bd) (bytesVal .ld br)) :=
    q.memory.trans p.memory
  have gp : gpr entered 3 = gpr c 3 :=
    (q.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)).trans
      (p.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide))
  have gpView : gpr entered 3 = gpr (memoryView c
      (writeLog c.σ.mem (prepareLog R (bytesVal .ld bd) (bytesVal .ld br)))) 3 := by
    rw [memoryView_gpr]
    exact gp
  have transported := h.copyMemory.memory_transport (after := entered) memory gpView
  have input := transported.input leaf good2 stack
  have C := StringCopy.copy_string_machine entered input (gholds_lookup _ q.regs (by rfl))
  apply C.weaken (fun _ eq => eq)
  intro after copied
  refine ⟨copied.toLeafInput, copied.libraryGood, copied.pc, copied.result, copied.stack,
    ?_, ?_, ?_, ?_, copied.shell, copied.bytes, ?_, ?_⟩
  · exact (copied.registers 8 (by decide) (by decide) (by decide)).trans (gholds_lookup _ q.regs rfl)
  · exact (copied.registers 9 (by decide) (by decide) (by decide)).trans (gholds_lookup _ q.regs rfl)
  · exact (copied.registers 18 (by decide) (by decide) (by decide)).trans (gholds_lookup _ q.regs rfl)
  · intro x
    have observed := copied.observed_log x
    rw [memory, ← writeLog_append] at observed
    exact observed
  · exact copied.output.trans (by simp only [Vsa.Machine.output, q.output, p.output])
  · intro n low high untouched
    have noCopy : n ∉ StringCopy.copyWrites := fun hn => untouched (List.mem_append_right _ hn)
    have noPrefix : n ∉ [1,2,8,9,10,13,14,15,18] := fun hn => untouched (List.mem_append_left _ hn)
    apply (copied.registers n low high noCopy).trans
    apply (q.toEffectPost.gpr_frame (by decide) n low high (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at noPrefix ⊢; omega)).trans
    apply p.toEffectPost.gpr_frame (by decide) n low high
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at noPrefix ⊢
    omega

end OCaml.Vm.Primitives.ArgvTuple
