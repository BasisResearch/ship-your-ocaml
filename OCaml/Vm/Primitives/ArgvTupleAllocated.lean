import OCaml.Vm.Primitives.ArgvTupleCopied
import OCaml.Vm.Primitives.SmallMemory
import OCaml.Vm.Primitives.SmallLayout

namespace OCaml.Vm.Primitives.ArgvTuple
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst

def allocateRegisters (R : Nat → BitVec 64) (young : BitVec 64) (len : Nat) : Nat → BitVec 64
  | 1 => prepare_call.link | 2 => frameSp (R 2) | 10 => StringCopy.resultWord young len | 18 => 2#64 | _ => 0

def beforeSmallLog (R : Nat → BitVec 64) (domain roots young : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) : List WEntry :=
  copiedLog R domain roots young a len g ++ allocateLog (allocateRegisters R young len)

def afterCopyLog (R : Nat → BitVec 64) (domain young blockYoung : BitVec 64) (len : Nat) : List WEntry :=
  allocateLog (allocateRegisters R young len) ++
    SmallAllocation.constructorLog allocate_call.link 2#64 0#64 domain blockYoung

def allocatedLog (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) : List WEntry :=
  copiedLog R domain roots young a len g ++ afterCopyLog R domain young blockYoung len

def tupleWord (blockYoung : BitVec 64) : BitVec 64 := SmallAllocation.nurseryHeader blockYoung 2#64 + 8#64

def callerWrites : List Nat := [1,2,5,6,8,9,10,11,12,13,14,15,16,17,18,28,29,30,31]

/-- Static memory requirements of the tuple allocation after copying the
executable name. The caller supplies separation from that fresh byte object. -/
structure AllocateStageInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (bd be br : List (BitVec 8)) (a len : Nat) (g : Nat → BitVec 8)
    (young limit blockYoung : BitVec 64) (c : Config) : Prop
    extends CopyStageInput live Dt DA R bd be br a len g young limit c where
  resultSlot : WriteWindow (frameSp (R 2)) 8
  resultImage : ImageOutside (allocateLog (allocateRegisters R young len))
  small : SmallAllocation.NurseryMemory allocate_call.link 2#64 0#64 (bytesVal .ld bd) blockYoung limit
    (memoryView c (writeLog c.σ.mem (beforeSmallLog R (bytesVal .ld bd) (bytesVal .ld br) young a len g)))
  stringOutside : ObjectOutside (afterCopyLog R (bytesVal .ld bd) young blockYoung len)
    (StringCopy.resultWord young len).toNat (.bytes (List.replicate len 0))

structure AllocateStagePost (live : Nat → Prop) (R : Nat → BitVec 64) (domain roots young blockYoung : BitVec 64)
    (a len : Nat) (g : Nat → BitVec 8) (before after : Config) : Prop
    extends LeafInput allocate_call.link after where
  libraryGood : VsaOk live after
  pc : pcOf after = some allocate_call.link
  result : gpr after 10 = some (tupleWord blockYoung)
  stack : gpr after 2 = some (frameSp (R 2))
  rootsReg : gpr after 8 = some roots
  domainReg : gpr after 9 = some DoubleAllocation.domainGlobal
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (allocatedLog R domain roots young blockYoung a len g))
  stringObject : ∀ (pl : Place) (cp : ChanPlace) (bs : List UInt8), bs.length = len →
    (∀ i x, bs[i]? = some x → g (a + i) = BitVec.ofNat 8 x.toNat) →
    ObjAt after pl cp (StringCopy.resultWord young len).toNat (.bytes bs)
  header : HeaderOk (word after (SmallAllocation.nurseryHeader blockYoung 2#64).toNat) 2 0
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ callerWrites → gpr after n = gpr before n

theorem argv_allocate_stage {live Dt DA R bd be br a len g young limit blockYoung c}
    (h : AllocateStageInput live Dt DA R bd be br a len g young limit blockYoung c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_get_argv) (fun d => d = c)
      (AllocateStagePost live R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g c) := by
  apply summary_bind (argv_copy_stage h.toCopyStageInput) (fun _ p => p.pc)
  intro copied copy
  let A := allocateRegisters R young len
  have input : GHolds copied.σ (allocate_input A) := ⟨copy.raReg, copy.stack, copy.result, copy.sizeReg, True.intro⟩
  apply summary_bind (allocate_fast copied A copy.toLeafInput input h.resultSlot h.resultImage) (fun _ p => p.pc)
  intro saved p
  have stack : gpr saved 2 = some (frameSp (R 2)) := gholds_lookup _ p.regs rfl
  have roots : gpr saved 8 = some (bytesVal .ld br) :=
    (p.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans copy.rootsReg
  have domainReg : gpr saved 9 = some DoubleAllocation.domainGlobal :=
    (p.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans copy.domainReg
  let args : GRegs := [(2, frameSp (R 2)), (8, bytesVal .ld br), (9, DoubleAllocation.domainGlobal), (10, 2#64), (11, 0#64)]
  have argsHold : GHolds saved.σ args := ⟨stack, roots, domainReg, p.result, gholds_lookup _ p.regs rfl, True.intro⟩
  have J := call_registers_summary allocate_call_shape allocate_call_decode saved (allocate_call_pins p.image)
    p.good p.image p.tick p.minstret args argsHold (by change KeysOK [2,8,9,10,11]; decide)
    (by simp [KeysAvoidRa, args, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good1 := p.vsaOk copy.libraryGood (by decide) (by simp [allocate_regs, keysG])
  have good2 := q.vsaOk (log := []) good1 (by decide) (by simp [args, keysG])
  have leaf : LeafInput allocate_call.link entered :=
    ⟨q.good, q.image, q.minstret, gholds_lookup _ q.regs rfl, by decide, q.tick⟩
  have observed : Vsa.Densify.MemEqv entered.σ.mem
      (writeLog c.σ.mem (beforeSmallLog R (bytesVal .ld bd) (bytesVal .ld br) young a len g)) := by
    rw [q.memory, p.memory, beforeSmallLog, writeLog_append]
    exact copy.memory.writeLog _
  have observedView : Vsa.Densify.MemEqv entered.σ.mem
      (memoryView c (writeLog c.σ.mem (beforeSmallLog R (bytesVal .ld bd) (bytesVal .ld br) young a len g))).σ.mem := by
    rw [memoryView_mem]
    exact observed
  have small := (h.small.observed_transport (after := entered) observedView).input leaf
    (gholds_lookup _ q.regs rfl) (gholds_lookup _ q.regs rfl)
  have S := SmallAllocation.alloc_small_nursery entered allocate_call.link 2#64 0#64 (bytesVal .ld bd) blockYoung limit small
  apply S.weaken (fun _ eq => eq)
  intro after finish
  have fromCopy : after.σ.mem = writeLog copied.σ.mem (afterCopyLog R (bytesVal .ld bd) young blockYoung len) := by
    rw [finish.memory, q.memory, p.memory, ← writeLog_append]
    rfl
  have finalMemory : Vsa.Densify.MemEqv after.σ.mem
      (writeLog c.σ.mem (allocatedLog R (bytesVal .ld bd) (bytesVal .ld br) young blockYoung a len g)) := by
    rw [fromCopy, allocatedLog, writeLog_append]
    exact copy.memory.writeLog _
  have frame (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31)
      (unwritten : n ∉ [1,6,10,11,12,13,14,15,16,17]) : gpr after n = gpr copied n := by
    apply (finish.toEffectPost.gpr_frame (by decide) n lo hi (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢; omega)).trans
    apply (q.toEffectPost.gpr_frame (by decide) n lo hi (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢; omega)).trans
    apply p.toEffectPost.gpr_frame (by decide) n lo hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢
    omega
  refine ⟨⟨finish.good, finish.image, finish.minstret, gholds_lookup _ finish.regs rfl, by decide, finish.tick⟩,
    finish.libraryGood live good2, finish.pc, finish.result,
    (frame 2 (by decide) (by decide) (by decide)).trans copy.stack,
    (frame 8 (by decide) (by decide) (by decide)).trans copy.rootsReg,
    (frame 9 (by decide) (by decide) (by decide)).trans copy.domainReg,
    finalMemory, ?_, finish.header (by decide) (by decide), ?_, ?_⟩
  · intro pl cp bs length source
    have shell : StringAllocation.StringShell copied (StringCopy.resultWord young len).toNat bs.length := by
      simpa only [length] using copy.shell
    have object : ObjAt copied pl cp (StringCopy.resultWord young len).toNat (.bytes bs) := shell.object (by
      intro i x hi
      have bound : i < len := by simpa only [← length] using (List.getElem?_eq_some_iff.mp hi).1
      exact (copy.bytes i bound).trans (source i x hi))
    apply object_copied object (copied_of_writeLog fromCopy h.stringOutside.header)
    apply copied_of_writeLog fromCopy
    simpa only [Obj.wosize, List.length_replicate, length] using h.stringOutside.payload
  · have unchanged : Vsa.Machine.output after.σ = Vsa.Machine.output copied.σ := by
      simp only [Vsa.Machine.output, finish.output, q.output, p.output]
    exact unchanged.trans copy.output
  · intro n lo hi unwritten
    apply (frame n lo hi (by
      simp only [callerWrites, List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢; omega)).trans
    apply copy.registers n lo hi
    simp only [callerWrites, StringCopy.copyWrites, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at unwritten ⊢
    omega

end OCaml.Vm.Primitives.ArgvTuple
