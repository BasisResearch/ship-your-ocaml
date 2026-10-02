import OCaml.Vm.Primitives.StringCopyFinish

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Memcpy StringAllocation

/-- Static source/code separation and nursery space for the complete C-string
copy. The fixed image and source bytes supply the read-only library cells. -/
structure CopyInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8)
    (domain young limit : BitVec 64) (c : Config) : Prop
    extends AllocateInput live Dt DA ra sp a len g domain young limit c where
  callerSeparate : CallerSeparation ra sp a len domain young
  copyGeometry : Geo (resultWord young len) (BitVec.ofNat 64 a) arguments_call.link len
  copyCodeLive : ∀ p ∈ mText, live p.1
  copyImage : ImageSeparate (InExt ((resultWord young len).toNat, len))
  copyTextSeparate : ∀ p ∈ mText ++ srcText a len g, ¬ InExt ((resultWord young len).toNat, len) p.1
  copyReadOnly : ROHolds (vsaModel live) c [] (mText ++ srcText a len g)
  copyReadsOutside : ∀ p ∈ mText ++ srcText a len g, OutL (allocationLog ra sp a len domain young) p.1
  returnOutsideCopy : (sp - 8#64).toNat + 8 ≤ (resultWord young len).toNat ∨
    (resultWord young len).toNat + len ≤ (sp - 8#64).toNat

/-- A read-only tail prefix can install the source argument while transporting
all copy requirements; only gp, native sp and the return ABI are needed. -/
theorem CopyInput.memory_transport {live Dt DA ra sp a len g domain young limit before after}
    (h : CopyInput live Dt DA ra sp a len g domain young limit before)
    (memory : after.σ.mem = before.σ.mem) (gp : gpr after 3 = gpr before 3)
    (leaf : LeafInput ra after) (good : VsaOk live after) (stack : gpr after 2 = some sp) :
    CopyInput live Dt DA ra sp a len g domain young limit after := by
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
    toLeafInput := leaf
    libraryGood := good
    stack := stack
    readOnly := ro
    string := strlen_readOnly_memory h.string after.σ.mem
    metadata := metadata
    copyReadOnly := copyRo }

/-- Whole native copy result, with its explicit allocation footprint and
payload-only copy frame. Neither output nor the abstract byte string changes. -/
structure CopyPost (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (domain young : BitVec 64) (before after : Config) : Prop
    extends LeafInput ra after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some (resultWord young len)
  stack : gpr after 2 = some sp
  shell : StringShell after (resultWord young len).toNat len
  bytes : ∀ i, i < len → byte after ((resultWord young len).toNat + i) = g (a + i)
  memory : ∀ x, ¬ InExt ((resultWord young len).toNat, len) x →
    byte after x = ((writeLog before.σ.mem (allocationLog ra sp a len domain young))[x]?).getD 0
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ copyWrites → gpr after n = gpr before n

/-- Full caml_copy_string execution: generated boundaries around strlen,
the G1 constructor, complete memcpy, and restoration of the native caller. -/
theorem copy_string_machine {live Dt DA ra sp a len g domain young limit} (c : Config)
    (h : CopyInput live Dt DA ra sp a len g domain young limit c)
    (source : gpr c 10 = some (BitVec.ofNat 64 a)) :
    FnSummary 0x8000c254#64 (fun d => d = c)
      (CopyPost live ra sp a len g domain young c) := by
  apply summary_bind (copy_string_allocated c h.toAllocateInput source) (fun _ p => p.pc)
  intro allocated p
  have readonly : ROHolds (vsaModel live) allocated [] (mText ++ srcText a len g) := by
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro point member
    have same := p.memory point.1
    change (allocated.σ.mem[point.1]?).getD 0 =
      ((writeLog c.σ.mem (allocationLog ra sp a len domain young))[point.1]?).getD 0 at same
    rw [writeLog_out _ _ _ (h.copyReadsOutside point member)] at same
    exact same.trans (h.copyReadOnly.2 point member)
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
