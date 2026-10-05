import OCaml.Vm.Sim.CcallnInput
import OCaml.Vm.Sim.CcallnPrefixSegment
import OCaml.Vm.Sim.CcallnPrefixPins
import OCaml.Vm.Sim.CcallnPrefixLayout

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- C_CALLN's generated five-store prefix establishes its stack-array ABI,
preserves the represented payload, and reaches the ELF-bound primitive. -/
theorem c_calln_setup {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high domain table nativeSp entry : Nat}
    {value env : BitVec 64} {index nargs : BitVec 32} {name : String}
    (stable : WindowStable L.runtimeOk (ccallnWindows sp domain nativeSp))
    (h : ArmInput L P s .C_CALLN c pl cp sp high)
    (countOperand : OperandAt P pl (s.pc + 1) nargs) (positive : 0 < nargs.toInt)
    (bound : nargs.toInt.toNat - 1 ≤ s.stack.length)
    (operand : OperandAt P pl (s.pc + 2) index) (nonnegative : 0 ≤ index.toInt)
    (primitive : P.prims[index.toInt.toNat]? = some name)
    (entryName : PrimitiveEntries.lookup name = some entry)
    (aligned : (BitVec.ofNat 64 entry).toNat % 4 = 0)
    (domainWord : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain)
    (tableWord : word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) = BitVec.ofNat 64 table)
    (targetRead : RamReadAt (table + 8 * index.toInt.toNat) 8)
    (accu : valWord pl s.accu = some value) (environment : valWord pl s.env = some env)
    (nativeReg : gpr c 2 = some (BitVec.ofNat 64 nativeSp))
    (space : CcallnWriteOk P s c pl cp sp domain nativeSp
      (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) env value)
    (dp : DispatchPost c .C_CALLN (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ n after, StepsN n d after ∧
      CcallnSetupPost L P s pl cp sp high nargs.toInt.toNat domain nativeSp entry env after := by
  have room8 : 8 ≤ sp := by have := space.room; omega
  have room16 : 16 ≤ sp := by have := space.room; omega
  have sp8Nat : (BitVec.ofNat 64 (sp - 8)).toNat = sp - 8 := Nat.mod_eq_of_lt (by have := space.stackNat; omega)
  have sp16Nat : (BitVec.ofNat 64 (sp - 16)).toNat = sp - 16 := Nat.mod_eq_of_lt (by have := space.stackNat; omega)
  have sp24Nat : (BitVec.ofNat 64 (sp - 24)).toNat = sp - 24 := Nat.mod_eq_of_lt (by have := space.stackNat; omega)
  have domainNat : (BitVec.ofNat 64 (domain + Layout.off_extern_sp)).toNat = domain + Layout.off_extern_sp :=
    Nat.mod_eq_of_lt space.domainNat
  have nativeNat : (BitVec.ofNat 64 (nativeSp + 88)).toNat = nativeSp + 88 := Nat.mod_eq_of_lt space.nativeNat
  have tableNat : (BitVec.ofNat 64 table).toNat = table := Nat.mod_eq_of_lt (by have := targetRead.upper; omega)
  have domainAddress : BitVec.ofNat 64 domain + BitVec.ofNat 64 Layout.off_extern_sp =
      BitVec.ofNat 64 (domain + Layout.off_extern_sp) := (BitVec.ofNat_add _ _).symm
  have nativeAddress : BitVec.ofNat 64 nativeSp + 88#64 = BitVec.ofNat 64 (nativeSp + 88) :=
    (BitVec.ofNat_add _ _).symm
  have entryAddress : BitVec.ofNat 64 table + BitVec.ofNat 64 (8 * index.toInt.toNat) =
      BitVec.ofNat 64 (table + 8 * index.toInt.toNat) := (BitVec.ofNat_add _ _).symm
  have nextPC := codePc_add pl s.pc 3
  obtain ⟨m1, hm1⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8), m = writeMap8 d.σ.mem (sp - 8) (sdData_val value) := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8), m = writeMap8 m1 (sp - 24) (sdData_val env) := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8), m = writeMap8 m2 (sp - 16)
      (sdData_val (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3)))) := ⟨_, rfl⟩
  obtain ⟨m4, hm4⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8), m = writeMap8 m3 (domain + Layout.off_extern_sp)
      (sdData_val (BitVec.ofNat 64 (sp - 24))) := ⟨_, rfl⟩
  obtain ⟨m5, hm5⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8), m = writeMap8 m4 (nativeSp + 88)
      (sdData_val (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3)))) := ⟨_, rfl⟩
  have memory3 : m3 = writeLog c.σ.mem [(sp - 8, 8, value), (sp - 24, 8, env),
      (sp - 16, 8, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3)))] := by
    rw [hm3, hm2, hm1, dp.memory]; rfl
  have memory4 : m4 = writeLog c.σ.mem [(sp - 8, 8, value), (sp - 24, 8, env),
      (sp - 16, 8, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))),
      (domain + Layout.off_extern_sp, 8, BitVec.ofNat 64 (sp - 24))] := by
    rw [hm4, hm3, hm2, hm1, dp.memory]; rfl
  have memory5 : m5 = writeLog c.σ.mem
      (ccallnLog sp domain nativeSp (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) env value) := by
    rw [hm5, hm4, hm3, hm2, hm1, dp.memory]; rfl
  have sub3 : [(sp - 8, 8, value), (sp - 24, 8, env),
      (sp - 16, 8, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3)))].Sublist
      (ccallnLog sp domain nativeSp (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) env value) := by simp [ccallnLog]
  have sub4 : [(sp - 8, 8, value), (sp - 24, 8, env),
      (sp - 16, 8, BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))),
      (domain + Layout.off_extern_sp, 8, BitVec.ofNat 64 (sp - 24))].Sublist
      (ccallnLog sp domain nativeSp (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) env value) := by simp [ccallnLog]
  have domainLoad := (word_read_writeLog_out (outLRange_sublist sub3 space.payload.domain) memory3).trans domainWord
  have tableLoad := (word_read_writeLog_out (outLRange_sublist sub4 space.bindings.contents) memory4).trans tableWord
  have boundTarget := h.primitives.get primitive entryName
  have targetWord : word c (table + 8 * index.toInt.toNat) = BitVec.ofNat 64 entry := by
    simpa only [primitiveTarget, tableWord, tableNat] using boundTarget
  have entryOutside := space.bindings.entries _ _ primitive
  simp only [tableWord, tableNat] at entryOutside
  have entryLoad := (word_read_writeLog_out (outLRange_sublist sub4 entryOutside) memory4).trans targetWord
  have countLoad : bytesT4 d.σ.mem (pl.codeBase + 4 * (s.pc + 1)) = nargs := by
    simpa only [bytesT_four_eq] using countOperand.read32 h.code dp.memory
  have operandLoad : bytesT4 m4 (pl.codeBase + 4 * (s.pc + 2)) = index := by
    have frame := bytesT_writeLog_out c.σ.mem (outLRange_sublist sub4 (space.payload.code _ _ operand.fetch))
    rw [bytesT_four_eq] at frame
    rw [memory4, frame]
    simpa only [bytesT_four_eq] using operand.read32 (d := c) h.code rfl
  have domainWindow : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have tableWindow : RamReadAt (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8 := ⟨by decide, by decide, by decide⟩
  have accuStore := writeWindow_nat space.accuWindow sp8Nat
  have envStore := writeWindow_nat space.envWindow sp24Nat
  have pcStore := writeWindow_nat space.pcWindow sp16Nat
  have externStore := writeWindow_nat space.externWindow domainNat
  have nativeStore := writeWindow_nat space.nativeWindow nativeNat
  have codeWindow (a : Nat) (w : BitVec 64)
      (member : (a, 8, w) ∈ ccallnLog sp domain nativeSp (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) env value) :
      a + 8 ≤ 0x80002e10 ∨ 0x80002e64 ≤ a :=
    image_entry_code space.image member (by decide) (by decide)
  have bp : SegSt (0x80002e10#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x9, BitVec.ofNat 64 sp⟩,
       ⟨Register.x21, value⟩, ⟨Register.x25, env⟩, ⟨Register.x2, BitVec.ofNat 64 nativeSp⟩]
      (fun σ => Vsa.Sim.Code.CamlCcallnPrefixLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x9 (by decide)).trans h.spReg,
      (dp.frame.frame Register.x21 (by decide)).trans (represented_register h.accu accu),
      (dp.frame.frame Register.x25 (by decide)).trans (represented_register h.env environment),
      (dp.frame.frame Register.x2 (by decide)).trans nativeReg, trivial⟩,
      dp.good.minstret, dp.tick, c_calln_prefix_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_c_calln_prefix (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp)
    value env (BitVec.ofNat 64 nativeSp) d.σ.mem d.σ
  simp only [ccalln_frame_address space.room, ccall1_frame_address room16, push_address room8,
    sp8Nat, sp16Nat, sp24Nat, c_calln_prefix_domain, c_calln_prefix_prim_contents,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) (0x00c#12) = 12#64 from by decide,
    show sign_extend (m := 64) (0x058#12) = 88#64 from by decide,
    show sign_extend (m := 64) (0x0a0#12) = BitVec.ofNat 64 Layout.off_extern_sp from by decide,
    BitVec.add_zero, domainWindow.toNat, tableWindow.toNat, nextPC, codePc_succ,
    codePc_add pl s.pc 2, countOperand.geometry.toNat, operand.geometry.toNat, nativeAddress, nativeNat] at run
  have first := run countOperand.geometry.lower countOperand.geometry.upper countOperand.geometry.htif
    (sign_extend (m := 64) nargs) (by rw [countLoad])
    accuStore.lower accuStore.upper accuStore.htif accuStore.aligned
    (codeWindow _ value (by simp [ccallnLog])) m1 hm1
    envStore.lower envStore.upper envStore.htif envStore.aligned
    (codeWindow _ env (by simp [ccallnLog])) m2 hm2
    pcStore.lower pcStore.upper pcStore.htif pcStore.aligned
    (codeWindow _ (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) (by simp [ccallnLog])) m3 hm3
    domainWindow.lower domainWindow.upper domainWindow.htif (BitVec.ofNat 64 domain) domainLoad.symm
  simp only [domainAddress, domainNat, index_word nargs (by omega)] at first
  simp only [ccalln_count_word nargs (by omega)] at first
  have second := first externStore.lower externStore.upper externStore.htif externStore.aligned
    (codeWindow _ (BitVec.ofNat 64 (sp - 24)) (by simp [ccallnLog])) m4 hm4
    operand.geometry.lower operand.geometry.upper operand.geometry.htif (sign_extend (m := 64) index)
    (by rw [operandLoad]) tableWindow.lower tableWindow.upper tableWindow.htif (BitVec.ofNat 64 table) tableLoad.symm
  simp only [index_word index nonnegative, entryAddress, targetRead.toNat] at second
  have last := second targetRead.lower targetRead.upper targetRead.htif (BitVec.ofNat 64 entry) entryLoad.symm
    nativeStore.lower nativeStore.upper nativeStore.htif nativeStore.aligned
    (codeWindow _ (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 3))) (by simp [ccallnLog])) m5 hm5
  have clear := ret_tgt (BitVec.ofNat 64 entry) aligned
  simp only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide, BitVec.add_zero] at clear
  simp only [clear] at last
  obtain ⟨n, after, _, steps, post⟩ := last aligned d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have written := memory.trans memory5
  have stored := space.stored written
  have image := image_of_writeLog h.dispatch.image space.image written
  have loop : LoopRegisters after := loopRegisters_frame (fun r hr =>
    (frame.frame r (by revert r; decide)).trans (dp.frame.frame r (by revert r; decide))) h.dispatch.loop
  refine ⟨n, after, steps, ?_⟩
  constructor
  · refine ⟨⟨post.good, image, post.good.minstret, PinsHold.get post.pins ⟨0, by simp⟩,
      by decide, post.tick⟩,
      (payload_of_repr h.toVmReprAt).frame_log space.payload written (frame.out.trans dp.frame.out),
      bindings_frame_log h.primitives space.bindings written,
      ccalln_runtime stable h.runtime space.room written, loop, by omega, bound,
      ccalln_array (payload_of_repr h.toVmReprAt) space accu written,
      PinsHold.get post.pins ⟨5, by simp⟩, PinsHold.get post.pins ⟨4, by simp⟩⟩
  · refine ⟨PinsHold.get post.pins ⟨6, by simp⟩, PinsHold.get post.pins ⟨1, by simp⟩,
      PinsHold.get post.pins ⟨11, by simp⟩,
      (frame.frame (gprReg Layout.reg_extra) (by decide)).trans ((dp.frame.frame (gprReg Layout.reg_extra) (by decide)).trans h.extra),
      environment, ?_, ?_, ?_, ?_, ?_, domainWindow.window, ?_, space.envWindow.read, ?_⟩
    · have obs := bytesT_writeLog_out c.σ.mem space.payload.domain
      simpa only [word, written, obs] using domainWord.symm
    · simpa only [domainAddress, domainNat] using stored.stack.symm
    · simpa only [sp24Nat] using stored.environment.symm
    · simpa only [nativeAddress, nativeNat] using stored.pc.symm
    · rw [← BitVec.ofNat_add]
      congr 1
      have room := space.room
      omega
    · simpa only [domainAddress] using space.externWindow.read
    · simpa only [nativeAddress] using space.nativeWindow.read
  · exact post.pcAt
  · exact h.geometry.frame_log rfl rfl space.payload.domain space.bindings.contents written
  · exact space.native h.native h.geometry h.stack domainWord nativeReg written
      ((frame.frame (gprReg 2) (by decide)).trans (dp.frame.frame (gprReg 2) (by decide)))

end OCaml.Vm.Sim
