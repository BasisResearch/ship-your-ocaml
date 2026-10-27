import OCaml.Vm.Primitives.StringCopyReadback
import OCaml.Vm.Primitives.LibraryMemcpy
import OCaml.Vm.Boot.Startup.GprsSame

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Memcpy

/-- An optional ABI register value determines its library observation. -/
theorem observed_register {live c n value} (below : n < 32) (h : gpr c n = some value) :
    (vsaModel live).reg c n = value := by
  change vsaReg c n = value
  rw [vsaReg_gpr (by change n ≠ 32; omega)]
  change (gpr c n).getD 0 = value
  rw [h]; rfl

namespace StringCopy
open StringAllocation OCaml.Vm.Boot.Startup

def copyWrites : List Nat := [1, 2, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]
def finishRegisters (sp dst : BitVec 64) : Nat → BitVec 64
  | 1 => arguments_call.link | 2 => sp - 32#64 | 10 => dst | _ => 0

def argumentRegisters (sp dst : BitVec 64) : Nat → BitVec 64
  | 1 => size_call.link | 2 => sp - 32#64 | 10 => dst | _ => 0

/-- The common native argument/return laws, instantiated from generated rows.
The two constructors share the stack layout, but have distinct native PCs. -/
structure TailBoundary where
  allocationLink : BitVec 64
  argumentsPC : BitVec 64
  call : CallInstr
  shape : CallShape call
  decode : CallDecode call
  target : call.target = 0x80042848#64
  pins : ∀ {c : Config}, ExecutableImage c → CallPins call c
  arguments : ∀ (c : Config) (R : Nat → BitVec 64) (len src : List (BitVec 8)),
    LeafInput (R 1) c → GHolds c.σ (arguments_input R) →
    ReadWindow (R 2) 8 → ReadWindow (R 2 + 8#64) 8 →
    LPins8 c.σ.mem (R 2).toNat len → LPins8 c.σ.mem (R 2 + 8#64).toNat src →
    FnSummary argumentsPC (fun d => d = c)
      (RegistersPost [11, 12] c.σ.mem c call.pc (R 10) (arguments_regs R [len, src]))
  restore : ∀ (c : Config) (R : Nat → BitVec 64) (ra : List (BitVec 8)),
    LeafInput (R 1) c → GHolds c.σ (restore_input R) →
    ReadWindow (R 2 + 24#64) 8 → LPins8 c.σ.mem (R 2 + 24#64).toNat ra →
    (bytesVal .ld ra).toNat % 4 = 0 →
    FnSummary call.link (fun d => d = c)
      (RegistersPost [1, 2] c.σ.mem c (bytesVal .ld ra) (R 10) (restore_regs R [ra]))

def copyTail : TailBoundary :=
  ⟨size_call.link, 0x8000c26c#64, arguments_call, arguments_call_shape,
    arguments_call_decode, arguments_call_target, arguments_call_pins,
    arguments_fast, restore_fast⟩

def tailRegisters (link sp dst : BitVec 64) : Nat → BitVec 64
  | 1 => link | 2 => sp - 32#64 | 10 => dst | _ => 0

/-- Memory-only facts at the generated memcpy-argument boundary. -/
structure TailInput (boundary : TailBoundary) (live : Nat → Prop) (ra sp dst : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (c : Config) : Prop extends LeafInput boundary.allocationLink c where
  libraryGood : VsaOk live c
  stack : gpr c 2 = some (sp - 32#64)
  result : gpr c 10 = some dst
  slots : CallerReadback ra sp a len c
  shell : StringShell c dst.toNat len
  lengthWindow : ReadWindow (sp - 32#64) 8
  sourceWindow : ReadWindow (sp - 24#64) 8
  returnWindow : ReadWindow (sp - 8#64) 8
  returnAligned : ra.toNat % 4 = 0
  sourceBound : a < 2^64
  geometry : Geo dst (BitVec.ofNat 64 a) boundary.call.link len
  codeLive : ∀ p ∈ mText, live p.1
  liveImage : ImageLive live
  imageSeparate : ImageSeparate (InExt (dst.toNat, len))
  textSeparate : ∀ p ∈ mText ++ srcText a len g, ¬ InExt (dst.toNat, len) p.1
  readOnly : ROHolds (vsaModel live) c [] (mText ++ srcText a len g)
  returnOutside : (sp - 8#64).toNat + 8 ≤ dst.toNat ∨ dst.toNat + len ≤ (sp - 8#64).toNat

abbrev FinishInput := TailInput copyTail

/-- The returned C-string copy has all bytes, canonical padding and a frame
outside the destination payload, with the original native stack restored. -/
structure FinishPost (live : Nat → Prop) (ra sp dst : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (before after : Config) : Prop extends LeafInput ra after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some dst
  stack : gpr after 2 = some sp
  shell : StringShell after dst.toNat len
  bytes : ∀ i, i < len → byte after (dst.toNat + i) = g (a + i)
  memory : ∀ x, ¬ InExt (dst.toNat, len) x → byte after x = byte before x
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ copyWrites → gpr after n = gpr before n

/-- Whole native copy result, with its explicit allocation footprint and
payload-only copy frame. Neither output nor the abstract byte string changes. -/
structure CopyPostAt (log : List WEntry) (dst : BitVec 64) (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (g : Nat → BitVec 8) (before after : Config) : Prop
    extends LeafInput ra after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some dst
  stack : gpr after 2 = some sp
  shell : StringShell after dst.toNat len
  bytes : ∀ i, i < len → byte after (dst.toNat + i) = g (a + i)
  memory : ∀ x, ¬ InExt (dst.toNat, len) x →
    byte after x = ((writeLog before.σ.mem log)[x]?).getD 0
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ copyWrites → gpr after n = gpr before n

/-- Generated argument loads/JAL, full memcpy, then the generated return. -/
theorem finish_tail (boundary : TailBoundary) {live ra sp dst a len g} (c : Config)
    (h : TailInput boundary live ra sp dst a len g c) :
    FnSummary boundary.argumentsPC (fun d => d = c) (FinishPost live ra sp dst a len g c) := by
  let R := tailRegisters boundary.allocationLink sp dst
  let blen := read8 c.σ.mem (sp - 32#64).toNat
  let bsrc := read8 c.σ.mem (sp - 24#64).toNat
  have vlen : bytesVal .ld blen = BitVec.ofNat 64 len := (read8_value _ _).trans h.slots.lengthValue
  have vsrc : bytesVal .ld bsrc = BitVec.ofNat 64 a := (read8_value _ _).trans h.slots.sourceValue
  have regs : GHolds c.σ (arguments_input R) := ⟨h.raReg, h.stack, h.result, True.intro⟩
  have P := boundary.arguments c R blen bsrc h.toLeafInput regs h.lengthWindow
    (by change ReadWindow (sp - 32#64 + 8#64) 8; rw [source_address]; exact h.sourceWindow)
    (read8_pins _ _)
    (by change LPins8 c.σ.mem (sp - 32#64 + 8#64).toNat bsrc; rw [source_address]; exact read8_pins _ _)
  apply summary_bind P (fun _ p => p.pc)
  intro prepared p
  have good := p.vsaOk (log := []) h.libraryGood (by decide) (by simp [arguments_regs, keysG])
  have args : GHolds prepared.σ [(2, sp - 32#64), (10, dst), (11, BitVec.ofNat 64 a), (12, BitVec.ofNat 64 len)] :=
    holds_project p.regs (by simp [arguments_regs, R, tailRegisters, lookupG, vlen, vsrc])
  have J := call_registers_summary boundary.shape boundary.decode prepared (boundary.pins p.image)
    p.good p.image p.tick p.minstret _ args (by change KeysOK [2, 10, 11, 12]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl
  rw [boundary.target] at J
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good' := q.vsaOk (log := []) good (by decide) (by simp [keysG])
  have memory : entered.σ.mem = c.σ.mem := q.memory.trans p.memory
  have sourceNat : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt h.sourceBound
  have readonly : ROHolds (vsaModel live) entered [] (mText ++ srcText a len g) := by
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro point member
    change (entered.σ.mem[point.1]?).getD 0 = point.2
    rw [memory]
    exact h.readOnly.2 point member
  have C := memcpy_summary entered h.codeLive h.geometry good' q.image h.liveImage h.imageSeparate
    (by constructor
        · intro p hp; nomatch hp
        · simpa only [sourceNat] using h.textSeparate)
    (by simpa only [sourceNat] using readonly)
    (observed_register (by decide) (gholds_lookup _ q.regs rfl))
    (observed_register (by decide) (gholds_lookup _ q.regs rfl))
    (observed_register (by decide) (gholds_lookup _ q.regs rfl))
    (observed_register (by decide) (gholds_lookup _ q.regs rfl))
  apply summary_bind C (fun _ cp => cp.pc)
  intro copied cp
  have frame : ∀ x, ¬ InExt (dst.toNat, len) x → byte copied x = byte c x := by
    intro x outside
    rw [byte_total, byte_total]
    have same := cp.observations.memory x outside
    change (copied.σ.mem[x]?).getD 0 = (entered.σ.mem[x]?).getD 0 at same
    rw [memory] at same
    exact same
  have saved : word copied (sp - 8#64).toNat = ra := by
    have words : word copied (sp - 8#64).toNat = word c (sp - 8#64).toNat :=
      Reloc.bytesT_congr (fun i hi => frame _ (by
        intro inside
        obtain ⟨low, high⟩ := inside
        rcases h.returnOutside with before | after <;> omega))
    exact words.trans h.slots.returnValue
  have spKept : gpr copied 2 = some (sp - 32#64) :=
    (library_register_frame good' cp.observations.good (by decide) (by decide)
      (cp.observations.registers 2 (by decide))).trans (gholds_lookup _ q.regs rfl)
  let R' := tailRegisters boundary.call.link sp dst
  let bra := read8 copied.σ.mem (sp - 8#64).toNat
  have vra : bytesVal .ld bra = ra := (read8_value _ _).trans saved
  have regs' : GHolds copied.σ (restore_input R') := ⟨spKept, cp.result, True.intro⟩
  have U := boundary.restore copied R' bra cp.toLeafInput regs'
    (by change ReadWindow (sp - 32#64 + 24#64) 8; rw [return_address]; exact h.returnWindow)
    (by change LPins8 copied.σ.mem (sp - 32#64 + 24#64).toNat bra; rw [return_address]; exact read8_pins _ _)
    (by rw [vra]; exact h.returnAligned)
  apply U.weaken (fun _ eq => eq)
  intro after finish
  have goodFinal := finish.vsaOk (log := []) cp.observations.good (by decide) (by simp [restore_regs, keysG])
  have returned : gpr after 1 = some ra := by
    have value := gholds_lookup _ finish.regs (n := 1) rfl
    change gprGet after.σ 1 = some ra
    simpa [restore_regs, vra] using value
  have lower : 8 ≤ dst.toNat := by have := h.geometry.dlo; omega
  have shell := h.shell.frame_payload lower (fun x outside => frame x (by simp only [InExt]; omega))
  refine ⟨⟨finish.good, finish.image, finish.minstret, returned, h.returnAligned, finish.tick⟩,
    goodFinal, ?_, finish.result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [vra] using finish.pc
  · have value := gholds_lookup _ finish.regs (n := 2) rfl
    have restoreSp : sp - 32#64 + 32#64 = sp := by bv_omega
    change gprGet after.σ 2 = some sp
    simpa only [restore_regs, R', tailRegisters, restoreSp] using value
  · exact shell.frame_payload lower (fun x _ => by simp only [byte, finish.memory])
  · intro i hi
    rw [byte, finish.memory]
    simpa only [byte, sourceNat] using cp.bytes i hi
  · intro x outside
    rw [byte, finish.memory]
    exact frame x outside
  · exact (show output after.σ = output copied.σ from by simp only [output, finish.output]).trans
      ((show output copied.σ = output entered.σ from cp.observations.output).trans
        (by simp only [output, q.output, p.output]))
  · have copyFrame : GprsSame entered copied mRegs :=
      ⟨fun n low high outside => library_register_frame good' cp.observations.good low high
        (cp.observations.registers n outside)⟩
    have kept := (((GprsSame.of_post p (by decide)).trans
      (GprsSame.of_post q (by decide))).trans copyFrame).trans
        (GprsSame.of_post finish (by decide))
    intro n low high untouched
    exact kept.same n low high (by
      simp only [copyWrites, mRegs, VsaIris.PC, List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at untouched ⊢
      omega)

/-- The C-string constructor instantiates the common generated native tail. -/
theorem copy_string_finish {live ra sp dst a len g} (c : Config)
    (h : FinishInput live ra sp dst a len g c) :
    FnSummary 0x8000c26c#64 (fun d => d = c) (FinishPost live ra sp dst a len g c) :=
  finish_tail copyTail c h

end StringCopy
end OCaml.Vm.Primitives
