import OCaml.Vm.Primitives.InitializedStringFast
import OCaml.Vm.Primitives.Memcpy

/-! Native `caml_alloc_initialized_string(length, source)`, nursery path.
The source is an arbitrary readable byte buffer, including a caller stack
buffer. All preconditions describe the initial data, geometry and runtime;
the allocation and both native callees are executed by the proof. -/
namespace OCaml.Vm.Primitives.InitializedString
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Memcpy StringAllocation
open OCaml.Vm.Boot.Startup

/-- The wrapper's real save bank followed by the constructor's actual stores. -/
def allocationLog (ra sp : BitVec 64) (a len : Nat) (domain young : BitVec 64) : List WEntry :=
  StringCopy.callerLog ra sp a len ++
    constructorLog save_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young

/-- Data-only entry requirements. The source needs no OCaml header, sentinel,
static-image provenance or heap membership. Separation preserves every source
byte through the native save bank and nursery allocation. -/
structure Requirements (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (domain young limit : BitVec 64) : Prop where
  lengthBound : len < 2^32
  sourceBound : a < 2^64
  returnSlot : WriteWindow (sp - 8#64) 8
  sourceSlot : WriteWindow (sp - 24#64) 8
  lengthSlot : WriteWindow (sp - 32#64) 8
  saveImage : ImageOutside (StringCopy.callerLog ra sp a len)
  metadataOutside : MetadataOutside (StringCopy.callerLog ra sp a len) domain
  geometry : NurseryGeometry save_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young limit
  separate : NurserySeparation save_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young
  callerSeparate : StringCopy.CallerSeparationAt save_call.link ra sp a len domain young
  copyGeometry : Geo (StringCopy.resultWord young len) (BitVec.ofNat 64 a) arguments_call.link len
  codeLive : ∀ p ∈ mText, live p.1
  liveImage : ImageLive live
  copyImage : ImageSeparate (InExt ((StringCopy.resultWord young len).toNat, len))
  textSeparate : ∀ p ∈ mText ++ srcText a len g, ¬ InExt ((StringCopy.resultWord young len).toNat, len) p.1
  readsOutside : ∀ p ∈ mText ++ srcText a len g, OutL (allocationLog ra sp a len domain young) p.1
  returnOutside : (sp - 8#64).toNat + 8 ≤ (StringCopy.resultWord young len).toNat ∨
    (StringCopy.resultWord young len).toNat + len ≤ (sp - 8#64).toNat

/-- Geometry and read footprints can be supplied before a caller produces the
source bytes. Only metadata and readable bytes depend on the current state. -/
structure Memory (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (domain young limit : BitVec 64) (c : Config) : Prop
    extends Requirements live ra sp a len g domain young limit where
  metadata : NurseryMetadata domain young limit c
  readOnly : ROHolds (vsaModel live) c [] (mText ++ srcText a len g)

structure Input (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (domain young limit : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c, Memory live ra sp a len g domain young limit c where
  libraryGood : VsaOk live c
  stack : gpr c 2 = some sp
  length : gpr c 10 = some (BitVec.ofNat 64 len)
  source : gpr c 11 = some (BitVec.ofNat 64 a)

/-- Read-only caller setup transports all data requirements to the real JAL
entry without assuming a callee result. -/
theorem Memory.transport {live ra sp a len g domain young limit before after}
    (h : Memory live ra sp a len g domain young limit before)
    (memory : after.σ.mem = before.σ.mem) :
    Memory live ra sp a len g domain young limit after := by
  have observed : Vsa.Densify.MemEqv after.σ.mem before.σ.mem := fun _ => by rw [memory]
  exact { h with
    metadata := ⟨by simpa only [word, memory] using h.metadata.domainValue,
      by simpa only [word, memory] using h.metadata.youngValue,
      by simpa only [word, memory] using h.metadata.limitValue⟩
    readOnly := readonly_transport h.readOnly (fun _ member => nomatch member) observed }

/-- Attach the register and runtime facts supplied by the preceding native
boundary to its data-only requirements. -/
theorem Memory.input {live ra sp a len g domain young limit c}
    (h : Memory live ra sp a len g domain young limit c) (leaf : LeafInput ra c)
    (good : VsaOk live c) (stack : gpr c 2 = some sp)
    (length : gpr c 10 = some (BitVec.ofNat 64 len))
    (source : gpr c 11 = some (BitVec.ofNat 64 a)) :
    Input live ra sp a len g domain young limit c :=
  { h with toLeafInput := leaf, libraryGood := good, stack := stack, length := length, source := source }

/-- Actual allocation return at the native memcpy-argument boundary. -/
structure Allocated (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (domain young : BitVec 64) (before after : Config) : Prop
    extends LeafInput save_call.link after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x8000c298#64
  result : gpr after 10 = some (StringCopy.resultWord young len)
  stack : gpr after 2 = some (sp - 32#64)
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (allocationLog ra sp a len domain young))
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 10, 11, 12, 13, 14, 15, 16, 17] →
    gpr after n = gpr before n
  shell : StringShell after (StringCopy.resultWord young len).toNat len

/-- Save actual inputs, execute the decoded allocation JAL, then reuse the
complete nursery constructor. Callee reads follow from those preceding stores. -/
theorem allocate {live ra sp a len g domain young limit} (c : Config)
    (h : Input live ra sp a len g domain young limit c) :
    FnSummary 0x8000c284#64 (fun d => d = c) (Allocated live ra sp a len domain young c) := by
  let R := entryRegisters ra sp a len
  have regs : GHolds c.σ (save_input R) := ⟨h.raReg, h.stack, h.length, h.source, True.intro⟩
  apply summary_bind (save_fast c ra sp a len h.toLeafInput regs
    h.returnSlot h.sourceSlot h.lengthSlot h.saveImage) (fun _ p => p.pc)
  intro prepared p
  have good := p.vsaOk h.libraryGood (by decide) (by simp [save_regs, keysG])
  have args : GHolds prepared.σ [(2, sp - 32#64), (10, BitVec.ofNat 64 len)] :=
    holds_project p.regs (by simp [save_regs, entryRegisters, lookupG])
  have J := call_registers_summary save_call_shape save_call_decode prepared (save_call_pins p.image)
    p.good p.image p.tick p.minstret _ args (by change KeysOK [2, 10]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good' := q.vsaOk (log := []) good (by decide) (by simp [keysG])
  have memory : entered.σ.mem = writeLog c.σ.mem (StringCopy.callerLog ra sp a len) :=
    q.memory.trans p.memory
  have observed : Vsa.Densify.MemEqv entered.σ.mem
      (writeLog c.σ.mem (StringCopy.callerLog ra sp a len)) := fun x => by rw [memory]
  have metadata := h.metadata.frame_observedLog h.metadataOutside observed
  have input : NurseryInput save_call.link (sp - 32#64) (BitVec.ofNat 64 len) domain young limit entered := {
    toLeafInput := ⟨q.good, q.image, q.minstret, gholds_lookup _ q.regs rfl, by decide, q.tick⟩
    toNurseryReadback := nursery_readback metadata h.separate
    toNurseryGeometry := h.geometry
    stackReg := gholds_lookup _ q.regs rfl
    lengthReg := gholds_lookup _ q.regs rfl }
  apply (alloc_string_nursery entered save_call.link (sp - 32#64)
    (BitVec.ofNat 64 len) domain young limit input).weaken (fun _ eq => eq)
  intro after finish
  refine ⟨⟨finish.good, finish.image, finish.minstret, finish.returnReg, by decide, finish.tick⟩,
    finish.libraryGood live good', finish.pc, finish.result, gholds_lookup _ finish.regs rfl, ?_, ?_, ?_, ?_⟩
  · rw [finish.memory, memory, ← writeLog_append]
    exact fun _ => rfl
  · exact (show output after.σ = output entered.σ from by simp only [output, finish.output]).trans
      (by simp only [output, q.output, p.output])
  · have kept := ((GprsSame.of_post p (by decide)).trans
      (GprsSame.of_post q (by decide))).trans (GprsSame.of_effect finish.toEffectPost (by decide))
    intro n low high untouched
    exact kept.same n low high (by
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at untouched ⊢
      omega)
  · rw [StringCopy.resultWord, DoubleAllocation.field_address h.geometry.headerWrite]
    exact finish.shell h.lengthBound h.geometry.headerWrite

/-- Complete bytes, header, zero padding, padding count, ABI and output frames.
Memory outside the payload equals the explicit allocation write log. -/
abbrev Post (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (domain young : BitVec 64) (before after : Config) :=
  StringCopy.CopyPostAt (allocationLog ra sp a len domain young) (StringCopy.resultWord young len)
    live ra sp a len g before after

/-- Entry-to-original-native-return summary for caml_alloc_initialized_string.
No callee execution, readback or desired final postcondition is a premise. -/
theorem initialized_string_nursery {live ra sp a len g domain young limit} (c : Config)
    (h : Input live ra sp a len g domain young limit c) :
    FnSummary 0x8000c284#64 (fun d => d = c) (Post live ra sp a len g domain young c) := by
  apply summary_bind (allocate c h) (fun _ p => p.pc)
  intro allocated p
  have readonly := memcpy_readOnly_log h.readOnly h.readsOutside p.memory
  have input : StringCopy.TailInput tailBoundary live ra sp (StringCopy.resultWord young len) a len g allocated := {
    toLeafInput := p.toLeafInput
    libraryGood := p.libraryGood
    stack := p.stack
    result := p.result
    slots := StringCopy.caller_readback_at h.callerSeparate p.memory
    shell := p.shell
    lengthWindow := h.lengthSlot.read
    sourceWindow := h.sourceSlot.read
    returnWindow := h.returnSlot.read
    returnAligned := h.aligned
    sourceBound := h.sourceBound
    geometry := h.copyGeometry
    codeLive := h.codeLive
    liveImage := h.liveImage
    imageSeparate := h.copyImage
    textSeparate := h.textSeparate
    readOnly := readonly
    returnOutside := h.returnOutside }
  apply (StringCopy.finish_tail tailBoundary allocated input).weaken (fun _ eq => eq)
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
    simp only [StringCopy.copyWrites, List.mem_cons, List.mem_nil_iff, or_false] at untouched ⊢
    omega

end OCaml.Vm.Primitives.InitializedString
