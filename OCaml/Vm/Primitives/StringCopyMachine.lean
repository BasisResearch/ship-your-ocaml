import OCaml.Vm.Primitives.StringCopyFinish

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Memcpy StringAllocation

/-- Static source/code separation and nursery space for the complete C-string
copy. The fixed image and source bytes supply the read-only library cells. -/
structure CopyMemory (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young limit : BitVec 64) (c : Config) : Prop
    extends AllocateMemory live Dt DA ra sp a len g domain young limit c where
  callerSeparate : CallerSeparation ra sp a len domain young
  copyGeometry : Geo (resultWord young len) (BitVec.ofNat 64 a) arguments_call.link len
  copyCodeLive : ∀ p ∈ mText, live p.1
  copyImage : ImageSeparate (InExt ((resultWord young len).toNat, len))
  copyTextSeparate : ∀ p ∈ mText ++ srcText a len g, ¬ InExt ((resultWord young len).toNat, len) p.1
  copyReadOnly : ROHolds (vsaModel live) c [] (mText ++ srcText a len g)
  copyReadsOutside : ∀ p ∈ mText ++ srcText a len g, OutL (allocationLog ra sp a len domain young) p.1
  returnOutsideCopy : (sp - 8#64).toNat + 8 ≤ (resultWord young len).toNat ∨
    (resultWord young len).toNat + len ≤ (sp - 8#64).toNat

structure CopyInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young limit : BitVec 64) (c : Config) : Prop
    extends AllocateInput live Dt DA ra sp a len g domain young limit c,
      CopyMemory live Dt DA ra sp a len g domain young limit c

/-- A read-only tail prefix can install the source argument while transporting
all copy requirements; only gp, native sp and the return ABI are needed. -/
theorem CopyMemory.memory_transport {live Dt DA ra sp a len g domain young limit before after}
    (h : CopyMemory live Dt DA ra sp a len g domain young limit before)
    (memory : after.σ.mem = before.σ.mem) (gp : gpr after 3 = gpr before 3)
    :
    CopyMemory live Dt DA ra sp a len g domain young limit after := by
  have observations : Vsa.Densify.MemEqv after.σ.mem before.σ.mem := fun x => by rw [memory]
  have gpObserved : (vsaModel live).reg after 3 = (vsaModel live).reg before 3 := by
    change (gpr after 3).getD 0 = (gpr before 3).getD 0
    rw [gp]
  have ro := readonly_transport h.readOnly (fun p hp => by
    have eq : p = (3, VsaIris.MallocFast.gpV) := List.mem_singleton.mp hp
    subst p; exact gpObserved) observations
  have copyRo := readonly_transport h.copyReadOnly (fun _ hp => nomatch hp) observations
  have metadata : NurseryMetadata domain young limit after := by
    constructor
    · simpa only [word, memory] using h.metadata.domainValue
    · simpa only [word, memory] using h.metadata.youngValue
    · simpa only [word, memory] using h.metadata.limitValue
  exact { h with
    readOnly := ro
    string := strlen_readOnly_memory h.string after.σ.mem
    metadata := metadata
    copyReadOnly := copyRo }

/-- Attach execution-proved entry facts to memory-only call requirements. -/
theorem CopyMemory.input {live Dt DA ra sp a len g domain young limit c}
    (h : CopyMemory live Dt DA ra sp a len g domain young limit c)
    (leaf : LeafInput ra c) (good : VsaOk live c) (stack : gpr c 2 = some sp) :
    CopyInput live Dt DA ra sp a len g domain young limit c :=
  { h with toLeafInput := leaf, libraryGood := good, stack := stack }

/-- Preserve the existing read-only-tail interface. -/
theorem CopyInput.memory_transport {live Dt DA ra sp a len g domain young limit before after}
    (h : CopyInput live Dt DA ra sp a len g domain young limit before)
    (memory : after.σ.mem = before.σ.mem) (gp : gpr after 3 = gpr before 3)
    (leaf : LeafInput ra after) (good : VsaOk live after) (stack : gpr after 2 = some sp) :
    CopyInput live Dt DA ra sp a len g domain young limit after :=
  (h.toCopyMemory.memory_transport memory gp).input leaf good stack

/-- Compatibility instance of the common allocated byte-copy result. -/
abbrev CopyPost (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (domain young : BitVec 64) (before after : Config) :=
  CopyPostAt (allocationLog ra sp a len domain young) (resultWord young len)
    live ra sp a len g before after

/-- Full caml_copy_string execution: generated boundaries around strlen,
the G1 constructor, complete memcpy, and restoration of the native caller. -/
theorem copy_string_machine {live Dt DA ra sp a len g domain young limit} (c : Config)
    (h : CopyInput live Dt DA ra sp a len g domain young limit c)
    (source : gpr c 10 = some (BitVec.ofNat 64 a)) :
    FnSummary 0x8000c254#64 (fun d => d = c)
      (CopyPost live ra sp a len g domain young c) := by
  apply summary_bind (copy_string_allocated c h.toAllocateInput source) (fun _ p => p.pc)
  intro allocated p
  have readonly := memcpy_readOnly_log h.copyReadOnly h.copyReadsOutside p.memory
  have input : FinishInput live ra sp (resultWord young len) a len g allocated := {
    toLeafInput := p.toLeafInput
    libraryGood := p.libraryGood
    stack := p.stack
    result := p.result
    slots := caller_readback h.callerSeparate p.memory
    shell := p.shell
    lengthWindow := h.lengthSlot.read
    sourceWindow := h.sourceSlot.read
    returnWindow := h.returnSlot.read
    returnAligned := h.aligned
    sourceBound := by have hi := h.string.hi; omega
    geometry := h.copyGeometry
    codeLive := h.copyCodeLive
    liveImage := h.libraryImage
    imageSeparate := h.copyImage
    textSeparate := h.copyTextSeparate
    readOnly := readonly
    returnOutside := h.returnOutsideCopy }
  apply (copy_string_finish allocated input).weaken (fun _ eq => eq)
  intro after finish
  refine ⟨finish.toLeafInput, finish.libraryGood, finish.pc, finish.result, finish.stack,
    finish.shell, finish.bytes, ?_, finish.output.trans p.output, ?_⟩
  · intro x copyOutside
    apply (finish.memory x copyOutside).trans
    rw [byte_total]
    exact p.memory x
  · intro n low high untouched
    apply (finish.registers n low high untouched).trans
    apply p.registers n low high
    simp only [copyWrites, List.mem_cons, List.mem_nil_iff, or_false] at untouched ⊢
    omega

end OCaml.Vm.Primitives.StringCopy
