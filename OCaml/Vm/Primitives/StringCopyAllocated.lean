import OCaml.Vm.Primitives.StringCopySized
import OCaml.Vm.Primitives.StringReadback
import OCaml.Vm.Primitives.StringConstructorLayout
import OCaml.Vm.Primitives.DoubleLayout
import OCaml.Vm.Primitives.WriteLogObservation

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim VsaIris.Inst
open StringAllocation

def lengthRegisters (sp : BitVec 64) (len : Nat) : Nat → BitVec 64 :=
  entryRegisters save_call.link (sp - 32#64) len

def prefixLog (ra sp : BitVec 64) (a len : Nat) : List WEntry :=
  saveLog (entryRegisters ra sp a) ++ sizeLog (lengthRegisters sp len)

def allocationLog (ra sp : BitVec 64) (a len : Nat) (domain young : BitVec 64) : List WEntry :=
  prefixLog ra sp a len ++ constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young

def resultWord (young : BitVec 64) (len : Nat) : BitVec 64 :=
  nurseryHeader young (BitVec.ofNat 64 len) + 8#64

/-- Static nursery space, stack and metadata facts for the second native call. -/
structure AllocateMemory (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young limit : BitVec 64) (c : Config) : Prop
    extends SizedMemory live Dt DA ra sp a len g c where
  lengthSlot : WriteWindow (sp - 32#64) 8
  lengthImage : ImageOutside (sizeLog (lengthRegisters sp len))
  metadata : NurseryMetadata domain young limit c
  metadataOutside : MetadataOutside (prefixLog ra sp a len) domain
  geometry : NurseryGeometry size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young limit
  separate : NurserySeparation size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young

structure AllocateInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young limit : BitVec 64) (c : Config) : Prop
    extends SizedInput live Dt DA ra sp a len g c,
      AllocateMemory live Dt DA ra sp a len g domain young limit c

/-- The string object is allocated and its shell initialized, ready for memcpy. -/
structure AllocatedPost (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (domain young : BitVec 64) (before after : Config) : Prop extends LeafInput size_call.link after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x8000c26c#64
  result : gpr after 10 = some (resultWord young len)
  stack : gpr after 2 = some (sp - 32#64)
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (allocationLog ra sp a len domain young))
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 10, 11, 12, 13, 14, 15, 16, 17] →
    gpr after n = gpr before n
  shell : StringShell after (resultWord young len).toNat len

/-- Compose the computed length, generated JAL and complete nursery constructor. -/
theorem copy_string_allocated {live Dt DA ra sp a len g domain young limit} (c : Config)
    (h : AllocateInput live Dt DA ra sp a len g domain young limit c)
    (source : gpr c 10 = some (BitVec.ofNat 64 a)) :
    FnSummary 0x8000c254#64 (fun d => d = c)
      (AllocatedPost live ra sp a len domain young c) := by
  apply summary_bind (copy_string_sized c h.toSizedInput source) (fun _ p => p.pc)
  intro sized s
  let R := lengthRegisters sp len
  have regs : GHolds sized.σ (size_input R) := ⟨s.raReg, s.stack, s.result, True.intro⟩
  have P := size_fast sized R s.toLeafInput regs h.lengthSlot h.lengthImage
  apply summary_bind P (fun _ p => p.pc)
  intro prepared p
  have good := p.vsaOk s.libraryGood (by decide) (by simp)
  have args : GHolds prepared.σ [(2, sp - 32#64), (10, BitVec.ofNat 64 len)] :=
    holds_project p.regs (by simp [size_regs, R, lengthRegisters, entryRegisters, lookupG])
  have J := call_registers_summary size_call_shape size_call_decode prepared (size_call_pins p.image)
    p.good p.image p.tick p.minstret _ args (by change KeysOK [2, 10]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good' := q.vsaOk (log := []) good (by decide) (by simp [keysG])
  have memory : Vsa.Densify.MemEqv entered.σ.mem (writeLog c.σ.mem (prefixLog ra sp a len)) := by
    rw [q.memory, p.memory, prefixLog, writeLog_append]
    exact s.memory.writeLog (sizeLog R)
  have metadata := h.metadata.frame_observedLog h.metadataOutside memory
  have input : NurseryInput size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young limit entered := {
    toLeafInput := ⟨q.good, q.image, q.minstret, gholds_lookup _ q.regs rfl, by decide, q.tick⟩
    toNurseryReadback := nursery_readback metadata h.separate
    toNurseryGeometry := h.geometry
    stackReg := gholds_lookup _ q.regs rfl
    lengthReg := gholds_lookup _ q.regs rfl }
  have A := alloc_string_nursery entered size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young limit input
  apply A.weaken (fun _ eq => eq)
  intro after finish
  refine ⟨⟨finish.good, finish.image, finish.minstret, finish.returnReg, by decide, finish.tick⟩,
    finish.libraryGood live good', finish.pc, finish.result, ?_, ?_, ?_, ?_, ?_⟩
  · exact gholds_lookup _ finish.regs rfl
  · have observed := memory.writeLog (constructorLog size_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young)
    rw [← finish.memory, ← writeLog_append] at observed
    exact observed
  · exact (show output after.σ = output entered.σ from by simp only [output, finish.output]).trans
      ((show output entered.σ = output sized.σ from by simp only [output, q.output, p.output]).trans s.output)
  · intro n low high untouched
    have one : n ∉ [1] := by simp only [List.mem_cons] at untouched; simpa using (show n ≠ 1 by omega)
    have sizedUntouched : n ∉ [1, 2, 10, 11, 12, 13, 14, 15] := by
      intro hn
      apply untouched
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢
      omega
    exact (finish.toEffectPost.gpr_frame (by decide) n low high untouched).trans
      ((q.toEffectPost.gpr_frame (by decide) n low high one).trans
       ((p.toEffectPost.gpr_frame (by decide) n low high (by simp)).trans
        (s.registers n low high sizedUntouched)))
  · have bound : len < 2^32 := by have hi := h.string.hi; have lo := h.string.lo; omega
    rw [resultWord, DoubleAllocation.field_address h.geometry.headerWrite]
    exact finish.shell bound h.geometry.headerWrite

end OCaml.Vm.Primitives.StringCopy
