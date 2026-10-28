import OCaml.Vm.Primitives.Format.AllocSprintfEntry
import OCaml.Vm.Primitives.Format.AllocSprintfLong
import OCaml.Vm.Boot.Startup.DomainRecord

/-! Plain signed LONGINT decimal: the real variadic entry, checked vsnprintf,
nursery initialized-string allocation, and restoring native return. -/
namespace OCaml.Vm.Primitives.Format.AllocSprintfLong
open Vsa.Machine Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open OCaml.Vm.Boot.Startup StringAllocation

/-- The enclosing stack window contains both callees' active frames, the
local output and all spills; it excludes the parsed format at its upper end. -/
def stackFoot (sp x : Nat) : Prop := sp + 48 - 1024 ≤ x ∧ x < sp + 240

def decimalImage (v : BitVec 64) (sp x : Nat) : BitVec 8 :=
  (decimalBytes v).getD (x - (sp + 16)) 0

def initializedLog (R : Nat → BitVec 64) (sp : Nat) (domain young : BitVec 64) : List WEntry :=
  InitializedString.allocationLog AllocSprintf.copy_call.link (BitVec.ofNat 64 sp)
    (sp + 16) (decimalBytes (R 11)).length domain young

def result (R : Nat → BitVec 64) (young : BitVec 64) : BitVec 64 :=
  StringCopy.resultWord young (decimalBytes (R 11)).length

/-- Exact allocation and copy effects outside the native stack window. -/
def effectLog (R : Nat → BitVec 64) (sp : Nat) (domain young : BitVec 64) : List WEntry :=
  initializedLog R sp domain young ++ byteCopyLog (result R young).toNat
    (decimalBytes (R 11)).length (fun i => (decimalBytes (R 11)).getD i 0)

/-- A byte whose value survives the complete native path. The scalar log is
actual allocation metadata/saves, while the final extent is the memcpy payload. -/
def preserved (R : Nat → BitVec 64) (sp : Nat) (domain young : BitVec 64) (x : Nat) : Prop :=
  ¬ stackFoot sp x ∧ OutL (initializedLog R sp domain young ++
    [((result R young).toNat, (decimalBytes (R 11)).length, 0)]) x

/-- Initial caller/runtime requirements. No execution or callee return is a
premise. Library bytes and allocator metadata are outside the enclosing stack;
the source bytes are produced by the proved formatter rather than assumed. -/
structure NativeInput (live : Nat → Prop) (Dt : Mem) (DA : List Nat)
    (R : Nat → BitVec 64) (sp : Nat) (domain young limit : BitVec 64) (c : Config) : Prop
    extends EntryInput live Dt DA R sp c where
  allocation : InitializedString.Requirements live AllocSprintf.copy_call.link (BitVec.ofNat 64 sp)
    (sp + 16) (decimalBytes (R 11)).length (decimalImage (R 11) sp) domain young limit
  imageLive : ImageLive live
  imageFrame : ImageSeparate (stackFoot sp)
  metadata : NurseryMetadata domain young limit c
  metadataFrame : ∀ a ∈ [DoubleAllocation.domainGlobal.toNat,
      (DoubleAllocation.youngSlot domain).toNat, (DoubleAllocation.limitSlot domain).toNat],
    ∀ i, i < 8 → ¬ stackFoot sp (a + i)
  allocationCode : ROHolds (vsaModel live) c [] VsaIris.Memcpy.mText
  allocationCodeFrame : ∀ p ∈ VsaIris.Memcpy.mText, ¬ stackFoot sp p.1
  saveBankFrame : ∀ k ∈ [168, 160, 144], OutLRange
    (initializedLog R sp domain young ++ [((result R young).toNat, (decimalBytes (R 11)).length, 0)])
    (sp + k) 8

/-- The native epilogue's three scalar loads, in their decoded order. -/
structure SaveBank (R : Nat → BitVec 64) (sp : Nat) (c : Config) : Prop where
  ra : bytesVal .ld (read8 c.σ.mem (sp + 168)) = R 1
  s0 : bytesVal .ld (read8 c.σ.mem (sp + 160)) = R 8
  s2 : bytesVal .ld (read8 c.σ.mem (sp + 144)) = R 18

/-- Everything needed at the actual initialized-string return, including the
original save bank and a frame relative to the original formatter entry. -/
structure BeforeReturn (live : Nat → Prop) (R : Nat → BitVec 64) (sp : Nat)
    (domain young : BitVec 64) (before after : Config) : Prop
    extends LeafInput AllocSprintf.copy_call.link after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x80013f20#64
  stack : gpr after 2 = some (BitVec.ofNat 64 sp)
  value : gpr after 10 = some (result R young)
  valueAligned : (result R young).toNat % 8 = 0
  shell : StringShell after (result R young).toNat (decimalBytes (R 11)).length
  bytes : ∀ i, i < (decimalBytes (R 11)).length →
    byte after ((result R young).toNat + i) = (decimalBytes (R 11)).getD i 0
  saves : SaveBank R sp after
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  memory : ∀ x, preserved R sp domain young x → byte after x = byte before x
  effects : ∀ x, ¬ stackFoot sp x →
    byte after x = imgM (writeLog before.σ.mem (effectLog R sp domain young)) x
  saved : ∀ n, n = 9 ∨ (19 ≤ n ∧ n ≤ 27) → gpr after n = gpr before n

/-- Execute from the real variadic entry through the existing checked
`short_initialized` run. No instruction in that continuation is re-proved. -/
theorem to_return {live Dt DA R sp domain young limit} (c : Config)
    (h : NativeInput live Dt DA R sp domain young limit c) :
    FnSummary 0x80013ec4#64 (fun d => d = c) (BeforeReturn live R sp domain young c) := by
  have low := h.lower
  have high := h.upper
  apply summary_bind (enter c h.toEntryInput) (fun _ p => p.pc)
  intro entered p
  apply summary_bind (vsnprintf_long_summary entered h.codeLive p.entry h.separate p.input)
    (fun _ q => library_pc q.good (q.result.pc.trans (by
      change (vsaModel live).reg entered 1 = AllocSprintf.pro_call.link
      change vsaReg entered 1 = AllocSprintf.pro_call.link
      rw [vsaReg_gpr (by decide), p.leaf.raReg]; rfl)))
  intro formatted q
  have ra : (vsaModel live).reg entered 1 = AllocSprintf.pro_call.link := by
    change vsaReg entered 1 = AllocSprintf.pro_call.link
    rw [vsaReg_gpr (by decide), p.leaf.raReg]; rfl
  have spreg : (vsaModel live).reg entered 2 = BitVec.ofNat 64 sp := by
    simpa only [show sp + 48 - 48 = sp by omega] using p.entry.stack
  have frame : ∀ x, ¬ stackFoot sp x → byte formatted x = byte c x := by
    intro x outside
    rw [byte_total, byte_total]
    have noStack : ¬ (sp + 48 - 1024 ≤ x ∧ x < sp + 48 - 48) := by
      unfold stackFoot at outside; omega
    have noBuffer : ¬ (sp + 16 ≤ x ∧ x < sp + 16 + 128) := by
      unfold stackFoot at outside; omega
    have same := vsnprintf_long_memory p.input q x noStack noBuffer
    change (formatted.σ.mem[x]?).getD 0 = (entered.σ.mem[x]?).getD 0 at same
    rw [same, p.memory, entry_frame R sp c.σ.mem x (by
      unfold stackFoot at outside
      omega)]
  have image : ExecutableImage formatted := image_local h.image q.good h.imageLive h.imageFrame
    (fun x out => by simpa only [byte_total, vsaModel] using frame x out)
  have leaf : LeafInput AllocSprintf.pro_call.link formatted :=
    ⟨q.good.good, image, q.good.good.minstret,
      library_gpr q.good (by decide) (by decide) (q.result.ra.trans ra), by decide, q.good.tick⟩
  let F := (vsaModel live).reg formatted
  have regs : GHolds formatted.σ (AllocSprintf.fits_input F) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
    all_goals exact library_gpr q.good (by decide) (by decide) rfl
  have length : F 10 = BitVec.ofNat 64 (decimalBytes (R 11)).length := q.result.length
  have metadata : NurseryMetadata domain young limit formatted := by
    have words : ∀ a, (∀ i, i < 8 → ¬ stackFoot sp (a + i)) → word formatted a = word c a := by
      intro a out
      exact Reloc.bytesT_congr (fun i hi => frame _ (out i hi))
    exact ⟨(words _ (h.metadataFrame _ (by simp))).trans h.metadata.domainValue,
      (words _ (h.metadataFrame _ (by simp))).trans h.metadata.youngValue,
      (words _ (h.metadataFrame _ (by simp))).trans h.metadata.limitValue⟩
  have buffer := decimal_buffer q.result
  have readonly : ROHolds (vsaModel live) formatted []
      (VsaIris.Memcpy.mText ++ VsaIris.Memcpy.srcText (sp + 16) (decimalBytes (R 11)).length (decimalImage (R 11) sp)) := by
    refine ⟨(fun _ member => nomatch member), ?_⟩
    intro pair member
    rcases List.mem_append.mp member with code | source
    · exact (show (vsaModel live).mem formatted pair.1 = (vsaModel live).mem c pair.1 by
        simpa only [byte_total, vsaModel] using frame _ (h.allocationCodeFrame pair code)).trans
        (h.allocationCode.2 pair code)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp source
      have hi' := List.mem_range.mp hi
      simpa only [decimalImage, Nat.add_sub_cancel_left, byte_total] using buffer.bytes i hi'
  have memory : InitializedString.Memory live AllocSprintf.copy_call.link (BitVec.ofNat 64 sp)
      (sp + 16) (decimalBytes (R 11)).length (decimalImage (R 11) sp) domain young limit formatted :=
    { toRequirements := { h.allocation with geometry := { h.allocation.geometry with small := decimal_nursery_small (R 11) } }
      metadata := metadata
      readOnly := readonly }
  have Fsp : F 2 = BitVec.ofNat 64 sp := q.result.sp.trans spreg
  have Fra : F 1 = AllocSprintf.pro_call.link := q.result.ra.trans ra
  have sourceAddress : (F 2 + 16#64).toNat = sp + 16 := by
    rw [Fsp, ofNat_add_ofNat, toNat_ofNat_lt (by omega)]
  have memory' : InitializedString.Memory live AllocSprintf.copy_call.link (F 2)
      (F 2 + 16#64).toNat (decimalBytes (R 11)).length (decimalImage (R 11) sp) domain young limit formatted := by
    rw [sourceAddress, Fsp]; exact memory
  apply (short_initialized formatted F (Fra.symm ▸ leaf) regs length q.good memory').weaken (fun _ eq => eq)
  intro allocated a
  rw [sourceAddress, Fsp] at a
  have bytes : ∀ i, i < (decimalBytes (R 11)).length →
      byte allocated ((result R young).toNat + i) = (decimalBytes (R 11)).getD i 0 := by
    intro i hi
    simpa only [result, sourceAddress, decimalImage, Nat.add_sub_cancel_left] using a.bytes i hi
  have footprint : ∀ x, OutL (initializedLog R sp domain young ++
      [((result R young).toNat, (decimalBytes (R 11)).length, 0)]) x → byte allocated x = byte formatted x := by
    simpa only [initializedLog, result, sourceAddress, Fsp] using a.footprint
  have observed : Vsa.Densify.MemEqv allocated.σ.mem
      (writeLog formatted.σ.mem (effectLog R sp domain young)) := by
    simpa only [effectLog, initializedLog, result, decimalImage, Nat.add_sub_cancel_left]
      using a.observed_log
  have effects : ∀ x, ¬ stackFoot sp x →
      byte allocated x = imgM (writeLog c.σ.mem (effectLog R sp domain young)) x := by
    intro x outside
    rw [byte_total]
    exact (observed x).trans (Vsa.Densify.writeLog_observed_at _ (by
      simpa only [byte_total] using frame x outside))
  have savedword : ∀ k value, k ∈ [168, 160, 144] →
      bytesT (writeLog c.σ.mem (entryLog R sp)) (sp + k) 8 = value →
      bytesVal .ld (read8 allocated.σ.mem (sp + k)) = value := by
    intro k value member original
    rw [read8_value]
    apply Eq.trans _ original
    apply Reloc.bytesT_congr
    intro i hi
    apply (footprint _ (outL_of_range (h.saveBankFrame k member) (by omega) (by omega))).trans
    rw [← p.memory]
    change byte formatted (sp + k + i) = byte entered (sp + k + i)
    simpa only [byte_total, vsaModel] using
      vsnprintf_long_memory p.input q (sp + k + i) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
  have words := entry_words R sp c.σ.mem
  have saves : SaveBank R sp allocated :=
    ⟨savedword 168 _ (by simp) words.ra, savedword 160 _ (by simp) words.s0,
      savedword 144 _ (by simp) words.s2⟩
  have valueAligned : (result R young).toNat % 8 = 0 := by
    change (nurseryHeader young (BitVec.ofNat 64 (decimalBytes (R 11)).length) + 8#64).toNat % 8 = 0
    rw [DoubleAllocation.field_address h.allocation.geometry.headerWrite]
    have aligned := h.allocation.geometry.headerWrite.aligned
    omega
  have vsnSame : GprsSame entered formatted abiClobbered := GprsSame.of_saved (by
    intro n member
    apply library_register_frame p.input.good q.good
      (by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at member; omega)
      (by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at member; omega)
    exact q.result.saved n (by
      simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at member; omega))
  have allocationSame : GprsSame formatted allocated StringCopy.copyWrites := ⟨a.registers⟩
  have same := (p.same.trans vsnSame).trans allocationSame
  refine ⟨a.toLeafInput, a.libraryGood, a.pc, ?_, a.result, valueAligned, a.shell, bytes, saves,
    a.output.trans (q.output.trans p.output), ?_, effects, ?_⟩
  · simpa only [Fsp] using a.stack
  · intro x outside
    exact (footprint x outside.2).trans (frame x outside.1)
  · intro n member
    apply same.same n (by omega) (by omega)
    simp only [StringCopy.copyWrites, abiClobbered, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]; omega

/-- Original native caller return, exact decimal payload and OCaml string
layout, with ABI and total-byte frames for a future C_CALL2 adapter. -/
structure NativePost (live : Nat → Prop) (R : Nat → BitVec 64) (sp : Nat)
    (domain young : BitVec 64) (before after : Config) : Prop
    extends LeafInput (R 1) after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some (R 1)
  stack : gpr after 2 = some (R 2)
  value : gpr after 10 = some (result R young)
  valueAligned : (result R young).toNat % 8 = 0
  shell : StringShell after (result R young).toNat (decimalBytes (R 11)).length
  bytes : ∀ i, i < (decimalBytes (R 11)).length →
    byte after ((result R young).toNat + i) = (decimalBytes (R 11)).getD i 0
  length : (decimalBytes (R 11)).length ≤ 20
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  memory : ∀ x, preserved R sp domain young x → byte after x = byte before x
  effects : ∀ x, ¬ stackFoot sp x →
    byte after x = imgM (writeLog before.σ.mem (effectLog R sp domain young)) x
  saved : GprsSame before after abiClobbered

/-- Execute the real epilogue at 0x80013f20, loading the original return,
s0 and s2 from the prologue's saved words. -/
theorem finish_return {live R sp domain young before} (c : Config)
    (p : BeforeReturn live R sp domain young before c)
    (original : GHolds before.σ (AllocSprintf.pro_input R))
    (stack : R 2 = BitVec.ofNat 64 (sp + 240)) (upper : sp + 240 ≤ 0x88000000)
    (aligned : (R 1).toNat % 4 = 0)
    (windows : ∀ k ∈ [168, 160, 144], ReadWindow (BitVec.ofNat 64 sp + BitVec.ofNat 64 k) 8) :
    FnSummary 0x80013f20#64 (fun d => d = c) (NativePost live R sp domain young before) := by
  let E : Nat → BitVec 64 := fun n => if n = 1 then AllocSprintf.copy_call.link
    else if n = 2 then BitVec.ofNat 64 sp else if n = 10 then result R young else 0
  have regs : GHolds c.σ (AllocSprintf.done_input E) := ⟨p.stack, p.value, True.intro⟩
  have addr : ∀ k, k ≤ 240 → (BitVec.ofNat 64 sp + BitVec.ofNat 64 k).toNat = sp + k := by
    intro k hk
    rw [ofNat_add_ofNat, toNat_ofNat_lt (by omega)]
  have savedRa : bytesVal .ld (read8 c.σ.mem (E 2 + 168#64).toNat) = R 1 := by
    change bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 sp + 168#64).toNat) = R 1
    rw [addr 168 (by decide)]; exact p.saves.ra
  apply (AllocSprintf.done_fast c (R 1) E p.toLeafInput regs
    (windows 168 (by simp)) (windows 160 (by simp)) (windows 144 (by simp)) savedRa aligned).weaken
    (fun _ eq => eq)
  intro after q
  have memory : after.σ.mem = c.σ.mem := by simpa only [writeLog, List.foldl_nil] using q.memory
  have regs' : GHolds after.σ [(2, R 2), (18, R 18), (8, R 8), (10, result R young), (1, R 1)] := by
    have eq : AllocSprintf.done_regs E (AllocSprintf.done_loads c.σ.mem E) =
        [(2, R 2), (18, R 18), (8, R 8), (10, result R young), (1, R 1)] := by
      simp only [AllocSprintf.done_regs, AllocSprintf.done_loads, List.getD_cons_zero,
        List.getD_cons_succ, E, ite_true, Nat.reduceEqDiff, ite_false]
      rw [addr 168 (by decide), addr 160 (by decide), addr 144 (by decide),
        p.saves.ra, p.saves.s0, p.saves.s2, stack, ofNat_add_ofNat]
    exact eq ▸ q.regs
  have shell : StringShell after (result R young).toNat (decimalBytes (R 11)).length := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [word, memory] using p.shell.header
    · simpa only [byte, memory] using p.shell.padding
    · intro i lo hi
      simpa only [byte, memory] using p.shell.zeroPad i lo hi
  have same := GprsSame.of_post q (by decide)
  have saved : GprsSame before after abiClobbered := GprsSame.of_saved (by
    intro n member
    simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at member
    by_cases n8 : n = 8
    · subst n
      exact (gholds_lookup _ regs' (n := 8) (v := R 8) rfl).trans
        (gholds_lookup _ original (n := 8) (v := R 8) rfl).symm
    by_cases n18 : n = 18
    · subst n
      exact (gholds_lookup _ regs' (n := 18) (v := R 18) rfl).trans
        (gholds_lookup _ original (n := 18) (v := R 18) rfl).symm
    exact (same.same n (by omega) (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans (p.saved n (by omega)))
  refine ⟨⟨q.good, q.image, q.minstret, gholds_lookup _ regs' (by simp [lookupG]), aligned, q.tick⟩,
    q.vsaOk p.libraryGood (by decide) (by simp [AllocSprintf.done_regs, keysG]), q.pc,
    gholds_lookup _ regs' (by simp [lookupG]), q.result, p.valueAligned, shell, ?_, intToString_length_le (R 11),
    ?_, ?_, ?_, saved⟩
  · intro i hi
    simpa only [byte, memory] using p.bytes i hi
  · change Vsa.Machine.output after.σ = _
    simp only [Vsa.Machine.output, q.output]
    exact p.output
  · intro x out
    simpa only [byte, memory] using p.memory x out
  · intro x out
    simpa only [byte, memory] using p.effects x out

/-- Entry-to-original-return native summary for precisely the plain signed
LONGINT decimal path. General formats and major allocation remain separate. -/
theorem native_return {live Dt DA R sp domain young limit} (c : Config)
    (h : NativeInput live Dt DA R sp domain young limit c) :
    FnSummary 0x80013ec4#64 (fun d => d = c) (NativePost live R sp domain young c) := by
  apply summary_bind (to_return c h) (fun _ p => p.pc)
  intro allocated p
  apply finish_return allocated p h.registers h.stack h.upper h.aligned
  intro k member
  have base : R 2 - 240#64 = BitVec.ofNat 64 sp := by rw [h.stack]; bv_omega
  rw [← base]
  exact (h.windows k (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)).read

/-- The selected owned blocks survive the same run when their bytes are
outside its explicit stack/allocation/copy footprint. -/
theorem NativePost.live {live R sp domain young before after H}
    (post : NativePost live R sp domain young before after)
    (bounds : ∀ e ∈ H, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧ e.1 + e.2 ≤ Vsa.Sim.DlHeap.heapEnd)
    (outside : ∀ x, x < Vsa.Sim.DlHeap.heapEnd → ¬ VsaIris.VsaHeap.vsaFoot H x → preserved R sp domain young x) :
    LiveFrame H before after := by
  apply LiveFrame.of_foot bounds
  intro x upper kept
  simpa only [byte_total] using post.memory x (outside x upper kept)

/-- Uint8 view of exactly the checked decimal bytes. -/
def decimalPayload (v : BitVec 64) : List UInt8 :=
  (decimalBytes v).map (fun b => UInt8.ofNat b.toNat)

/-- The returned word denotes a fully initialized OCaml byte-string with the
exact decimal bytes and canonical header/padding representation. -/
theorem NativePost.object {live R sp domain young before after pl cp}
    (post : NativePost live R sp domain young before after) :
    ObjAt after pl cp (result R young).toNat (.bytes (decimalPayload (R 11))) := by
  have len : (decimalPayload (R 11)).length = (decimalBytes (R 11)).length := List.length_map ..
  apply (len.symm ▸ post.shell).object
  intro i x hx
  simp only [decimalPayload, List.getElem?_map] at hx
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hi := (List.getElem?_eq_some_iff.mp hb).1
  rw [post.bytes i hi, List.getD_eq_getElem?_getD, hb]
  change b = BitVec.ofNat 8 (b.toNat % 256)
  rw [Nat.mod_eq_of_lt b.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end OCaml.Vm.Primitives.Format.AllocSprintfLong
