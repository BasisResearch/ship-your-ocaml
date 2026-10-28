import OCaml.Vm.Boot.Startup.SeekOptionalLoop

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Bytes outside the actual optional-seek/lseek scratch, errno and fd-position stores. -/
def codeScanKeep (x : Nat) : Prop :=
  (x < seekStack.toNat - 64 ∨ parameterStack.toNat ≤ x) ∧ OutW errnoWindows x ∧
    (x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x)

theorem codeScanKeep_arena (x : Nat) (lo : heapStart ≤ x) (hi : x < heapEnd) : codeScanKeep x := by
  have stack : heapEnd + 128 ≤ parameterStack.toNat := by decide
  have addr : seekStack.toNat = parameterStack.toNat - 64 := by decide
  refine ⟨Or.inl ?_,?_,Or.inr ?_⟩
  · rw [addr]; omega
  · have bound : 0x80064d4c ≤ heapStart := by decide
    simp only [OutW,errnoWindows,and_true]; omega
  · have bound : Layout.sym_fds + 88 ≤ heapStart := by decide
    omega

theorem codeScanKeep_caller (x : Nat) (lo : parameterStack.toNat ≤ x) : codeScanKeep x := by
  refine ⟨Or.inr lo,?_,Or.inr ?_⟩
  · simp only [OutW,errnoWindows,and_true]
    have bound : 0x80064d4c ≤ parameterStack.toNat := by decide
    omega
  · have bound : Layout.sym_fds + 88 ≤ parameterStack.toNat := by decide
    omega

theorem seekSaveLog_inside (saved : Nat → BitVec 64) :
    LogInW [⟨nativeFrameBase parameterStack 64,parameterStack.toNat⟩] (seekSaveLog saved) :=
  log_in_append (seekHeadLog_inside saved) (seekTailLog_inside saved)

/-- Observe any word actually saved by the optional-section prologue. -/
theorem seek_saved_word (m : Std.ExtHashMap Nat (BitVec 8)) (saved : Nat → BitVec 64)
    (off : Nat) (value : BitVec 64) (hm : (off,value) ∈ seekRestoreSlots saved) :
    bytesT (writeLog m (seekSaveLog saved)) (seekStack.toNat + off) 8 = value := by
  have log : seekSaveLog saved = nativeWordLog parameterStack 64 (seekHeadSlots saved ++ seekTailSlots saved) := by
    simp only [seekSaveLog,seekHeadLog,seekTailLog,nativeWordLog,List.map_append]
  have bounds : ∀ off value, (off,value) ∈ seekHeadSlots saved ++ seekTailSlots saved → off + 8 ≤ 64 := by
    intro off value member
    simp only [seekHeadSlots,seekTailSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      Prod.mk.injEq] at member
    omega
  have separate : (seekHeadSlots saved ++ seekTailSlots saved).Pairwise
      (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by
    simp [seekHeadSlots,seekTailSlots,List.pairwise_cons]
  have member : (off,value) ∈ seekHeadSlots saved ++ seekTailSlots saved := by
    simp only [seekRestoreSlots,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm
    simp only [seekHeadSlots,seekTailSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
    rcases hm with h | h | h | h | h | h | h | h <;> rcases h with ⟨rfl,rfl⟩ <;> simp
  rw [log]
  exact seek_frame.word_log_read bounds separate m member

/-- Memory equality from the executed save log supplies the bounded source frame. -/
theorem code_scan_saved_frame {saved before after}
    (memory : after.σ.mem = writeLog before.σ.mem (seekSaveLog saved)) :
    MemSame before after codeScanKeep := by
  constructor
  intro x hx
  rw [memory,frameOn_writeLog _ _ _ (seekSaveLog_inside saved) x ⟨?_,trivial⟩]
  have h := hx.1
  change x < nativeFrameBase parameterStack 64 ∨ parameterStack.toNat ≤ x
  have eq : seekStack.toNat = nativeFrameBase parameterStack 64 := by decide
  rw [← eq]
  omega

/-- The existing lseek contract exposes both its bounded frame and the actual position store. -/
theorem code_scan_lseek_frame {H capacity blk before after}
    (L : LseekFile H capacity seekStack 0x80004c64#64 blk (0#64 - 9331#64) before after) :
    MemSame before after codeScanKeep := by
  constructor
  intro x hx
  rw [L.mem x (by rcases hx.1 with h | h; exact Or.inl h; exact Or.inr (by
    have bound : seekStack.toNat ≤ parameterStack.toNat := by decide
    omega)) hx.2.1,writeLog_out _ _ _ (by simp only [lseekLog,OutL,and_true]; exact hx.2.2)]

/-- Actual native completion, retaining the selected ledger, descriptor and fd/argv ABI. -/
structure CodeSeekDone (H : List (Nat × Nat)) (capacity : Nat) (blk node : BitVec 64)
    (before after : Config) : Prop where
  pc : PCAt 0x80004eb0#64 after
  length : gprGet after.σ 10 = some 764#64
  position : bytesT after.σ.mem (Layout.sym_fds + 80) 8 = 57#64
  ready : RuntimeReady H capacity parameterStack 0x80004ea8#64 after
  caller : LoadCaller after
  abi : GprsSame before after abiClobbered
  live : LiveFrame H before after
  frame : MemSame before after codeScanKeep
  descriptorOwned : (blk.toNat,56) ∈ H
  table : CodeScanTable blk after
  tablePointer : bytesT after.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk
  file : OpenFile after.σ.mem node
  embed : EmbedImage after

/-- Selected file records and the original owned filename survive the native write windows. -/
theorem CodeScanInput.file_frame {H capacity blk node before after}
    (I : CodeScanInput H capacity blk node before) (F : MemSame before after codeScanKeep) :
    OpenFile after.σ.mem node := by
  apply I.observed.file.transport
  intro x hx
  apply F.same x
  rcases hx with ⟨htif,pos⟩ | ⟨lo,hi⟩
  · have bounds := htif.bounds
    refine ⟨Or.inl ?_,htif.out_errno,pos⟩
    have upper : Layout.sym_files + 56*64 < seekStack.toNat - 64 := by decide
    omega
  · have bounds := I.ready.block_bounds I.filenameOwned
    exact codeScanKeep_arena x (by omega) (by omega)

/-- The actual selected embedded image survives scratch stores and lseek's position update. -/
theorem CodeScanInput.embed_frame {H capacity blk node before after}
    (I : CodeScanInput H capacity blk node before) (F : MemSame before after codeScanKeep) :
    EmbedImage after := by
  apply I.observed.embed.of_bytes
  intro x hx
  apply F.same x
  have stack := hx.stack_room
  have lower := hx.1
  refine ⟨Or.inl ?_,?_,Or.inr ?_⟩
  · have eq : seekStack.toNat = parameterStack.toNat - 64 := by decide
    rw [eq]; omega
  · simp only [OutW,errnoWindows,and_true]
    unfold heapEnd at lower
    omega
  · unfold heapEnd Layout.sym_fds at *; omega

/-- The actual trailer pointer is in the preserved native caller frame. -/
theorem CodeScanInput.table_frame {H capacity blk node before after}
    (I : CodeScanInput H capacity blk node before) (F : MemSame before after codeScanKeep) :
    bytesT after.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk := by
  rw [F.word (fun j _ => codeScanKeep_caller _ (by
    have base : parameterStack.toNat ≤ (WhileMinElfParse.trailSlot + 16#64).toNat := by decide
    omega))]
  exact I.observed.table

/-- The bounded native frame keeps every allocation on the selected input ledger. -/
theorem CodeScanInput.live_frame {H capacity blk node before after}
    (I : CodeScanInput H capacity blk node before) (F : MemSame before after codeScanKeep) :
    LiveFrame H before after :=
  LiveFrame.of_arena (fun e he => I.ready.block_bounds he)
    (fun x lo hi => F.same x (codeScanKeep_arena x lo hi))

/-- Current descriptor bytes are transported by selected ownership, independently of Steps. -/
theorem CodeScanInput.descriptor_frame {H capacity blk node before after}
    (I : CodeScanInput H capacity blk node before) (F : MemSame before after codeScanKeep) :
    CodeScanTable blk after := by
  have geometry := I.ready.block_bounds I.descriptorOwned
  refine ⟨geometry.1,geometry.2,fun k hk => ?_⟩
  rw [(I.live_frame F).byte _ I.descriptorOwned _ (by unfold InExt; dsimp only; omega)]
  exact I.observed.descriptor k hk

/-- Execute the real optional-section scan and lseek, restore its caller, then exclude missing CODE. -/
theorem code_seek_complete {H capacity blk node c} (I : CodeScanInput H capacity blk node c) :
    ∃ after, Steps c after ∧ CodeSeekDone H capacity blk node c after := by
  obtain ⟨a,runA,A⟩ := code_scan_start I
  obtain ⟨b,runB,B⟩ := code_scan_loop H capacity blk (vsaReg c) c a A
  obtain ⟨d,runD,D⟩ := code_scan_compare_call B
  obtain ⟨e,runE,E⟩ := (seek_optional_found d 0x80004c4c#64 D.ready.toLeafInput
    ⟨gholds_lookup (n := 9) _ D.regs rfl,D.regs.1,gholds_lookup (n := 18) _ D.regs rfl,
      gholds_lookup (n := 22) _ D.regs rfl,trivial⟩).run d ⟨D.pc,rfl⟩
  have gE := GprsSame.of_post E (by decide)
  have readyE := seek_readonly_ready D.ready E (by decide) (by decide)
    (gE.get (by decide) (by decide) (by decide) D.ready.stack)
    (gholds_lookup (n := 1) _ E.regs rfl) (by decide)
  have memoryE : e.σ.mem = writeLog c.σ.mem (seekSaveLog (vsaReg c)) := E.memory.trans D.memory
  have frameE := code_scan_saved_frame memoryE
  have fileE := I.file_frame frameE
  have cursor : seekCursor blk 6 = blk := by unfold seekCursor; simp only [Nat.sub_self,Nat.mul_zero,
    show BitVec.ofNat 64 0 = 0#64 from rfl,BitVec.add_zero]
  have fd8 : gprGet e.σ 8 = some blk := by
    rw [← cursor]
    exact gE.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ D.regs rfl)
  obtain ⟨f,runF,L⟩ := (lseek_file e H capacity seekStack 0x80004c64#64 blk (0#64 - 9331#64)
    readyE (by constructor <;> decide)
    ⟨readyE.stack,readyE.raReg,fd8,gholds_lookup (n := 10) _ E.regs rfl,
      gholds_lookup (n := 11) _ E.regs rfl,gholds_lookup (n := 12) _ E.regs rfl,trivial⟩
    fileE.words node fileE.slot fileE.kind fileE.nodeWord seek_code_seek_guards.1
    seek_code_seek_guards.2 (by rw [seek_code_arithmetic.1]; decide)).run e ⟨E.pc,rfl⟩
  have syscall := code_scan_lseek_frame L
  have frameF := frameE.chain syscall
  have tableF := I.descriptor_frame frameF
  have gL : GprsSame e f lseekWrites := ⟨L.kept⟩
  have callerF : CallerFrame seekStack e f := by
    constructor
    intro x hx
    rw [L.mem x (Or.inr hx) (by
      have lower : 0x80064d4c ≤ seekStack.toNat := by decide
      simp only [OutW,errnoWindows,and_true]; omega),
      writeLog_out _ _ _ (by
        have lower : Layout.sym_fds + 88 ≤ seekStack.toNat := by decide
        simp only [lseekLog,OutL,and_true]; exact Or.inr (by omega))]
  have savedF (off : Nat) (value : BitVec 64) (hm : (off,value) ∈ seekRestoreSlots (vsaReg c)) :
      bytesT f.σ.mem (seekStack.toNat + off) 8 = value := by
    rw [word_observed (m := e.σ.mem) _ fun j _ => callerF.byte _ (by omega),memoryE]
    exact seek_saved_word c.σ.mem (vsaReg c) off value hm
  have table0 : seekCursor blk 6 + 4#64 = blk + 4#64 := by rw [cursor]
  obtain ⟨g,runG,G⟩ := (seek_optional_return f blk (vsaReg c) L.ready.toLeafInput
    ⟨gL.get (by decide) (by decide) (by decide)
        (gE.get (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ D.regs rfl)),
      gL.get (by decide) (by decide) (by decide)
        (gE.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ D.regs rfl)),
      L.ready.stack,trivial⟩
    (I.table_frame frameF) (by simpa only [cursor] using tableF.window 6 4 4 (by decide) (by decide))
    (by simpa only [table0,seekLength,seekSectionLengths,Nat.sub_self,List.getElem!_cons_zero] using (tableF.length 6 (by decide)).2)
    savedF).run f ⟨L.pc,rfl⟩
  have readyG := L.ready.stack_log G (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ G.regs rfl) (gholds_lookup (n := 1) _ G.regs rfl) (by decide)
    seek_frame (by simp only [LogInW])
  obtain ⟨after,runP,P⟩ := (code_seek_present g 0x80004ea8#64 readyG.toLeafInput G.result).run g ⟨G.pc,rfl⟩
  have gP := GprsSame.of_post P (by decide)
  have readyP := seek_readonly_ready readyG P (by decide) (by decide)
    (gP.get (by decide) (by decide) (by decide) readyG.stack)
    (gP.get (by decide) (by decide) (by decide) readyG.raReg) (by decide)
  have tailMemory : after.σ.mem = f.σ.mem := P.memory.trans G.memory
  have frame := frameF.chain ((MemSame.of_eq tailMemory).mono (fun _ _ => trivial))
  have gAll := D.abi.trans (gE.trans (gL.trans ((GprsSame.of_post G (by decide)).trans gP)))
  have bank (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c.σ n = some (vsaReg c n) :=
    library_gpr I.ready.platform lo hi rfl
  have abi : GprsSame c after abiClobbered := by
    apply GprsSame.of_saved
    intro n hn
    simp only [abiSaved,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 8) _ G.regs rfl)).trans (I.caller.fd).symm
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 9) _ G.regs rfl)).trans (bank 9 (by decide) (by decide)).symm
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 18) _ G.regs rfl)).trans (bank 18 (by decide) (by decide)).symm
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 19) _ G.regs rfl)).trans (bank 19 (by decide) (by decide)).symm
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 20) _ G.regs rfl)).trans (bank 20 (by decide) (by decide)).symm
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 21) _ G.regs rfl)).trans (bank 21 (by decide) (by decide)).symm
    · exact (gP.get (by decide) (by decide) (by decide)
        (gholds_lookup (n := 22) _ G.regs rfl)).trans (bank 22 (by decide) (by decide)).symm
    · exact gAll.same _ (by decide) (by decide) (by decide)
    · exact gAll.same _ (by decide) (by decide) (by decide)
    · exact gAll.same _ (by decide) (by decide) (by decide)
    · exact gAll.same _ (by decide) (by decide) (by decide)
    · exact gAll.same _ (by decide) (by decide) (by decide)
  have posF : bytesT f.σ.mem (Layout.sym_fds + 80) 8 = 57#64 := by
    rw [word_observed (m := writeLog e.σ.mem (lseekLog (0#64 - 9331#64))) _ fun j hj => L.mem _
      (Or.inl (by
        have upper : Layout.sym_fds + 88 < seekStack.toNat - 64 := by decide
        omega))
      (by simp only [OutW,errnoWindows,and_true,Layout.sym_fds]; omega)]
    exact (word_writeLog e.σ.mem (Layout.sym_fds + 80) _).trans seek_code_arithmetic.1
  refine ⟨after,runA.trans (runB.trans (runD.trans (runE.trans (runF.trans (runG.trans runP))))),{
    pc := P.pc
    length := P.result
    position := by rw [tailMemory]; exact posF
    ready := readyP
    caller := I.caller.frame abi (by decide) (by decide)
    abi := abi
    live := I.live_frame frame
    frame := frame
    descriptorOwned := I.descriptorOwned
    table := I.descriptor_frame frame
    tablePointer := I.table_frame frame
    file := I.file_frame frame
    embed := I.embed_frame frame }⟩

end OCaml.Vm.Boot.Startup
