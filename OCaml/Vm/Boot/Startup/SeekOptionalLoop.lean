import OCaml.Vm.Boot.Startup.SeekOptionalData
import OCaml.Vm.Boot.Startup.IndexedLoop

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap LeanRV64DExecutable VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Link before the first comparison and on subsequent reverse-loop iterations. -/
def codeScanLink (k : Nat) : BitVec 64 := if k = 0 then 0x80004ea8#64 else 0x80004c4c#64

def codeScanWrites : List Nat := [1,2,8,9,10,11,12,14,15,18,19,20,21,22,28]

def codeScanRegs (blk : BitVec 64) (k : Nat) : GRegs :=
  [(8,seekCursor blk k),(9,BitVec.ofNat 64 (6-k)),(18,seekOffset k),
    (19,BitVec.ofNat 64 (8*(6-k))),(20,codeSectionName0),(21,WhileMinElfParse.trailSlot),
    (22,3#64),(2,seekStack)]

/-- Named reverse-scan invariant, retaining the actual saving effect and selected runtime. -/
structure CodeScanAt (H : List (Nat × Nat)) (capacity : Nat) (blk : BitVec 64)
    (saved : Nat → BitVec 64) (start : Config) (k : Nat) (c : Config) : Prop where
  bound : k ≤ 6
  pc : PCAt 0x80004c34#64 c
  regs : GHolds c.σ (codeScanRegs blk k)
  ready : RuntimeReady H capacity seekStack (codeScanLink k) c
  table : CodeScanTable blk c
  memory : c.σ.mem = writeLog start.σ.mem (seekSaveLog saved)
  abi : GprsSame start c codeScanWrites

/-- Result of the unsigned accumulation and the real strncmp call at one descriptor. -/
structure CodeScanCompared (H : List (Nat × Nat)) (capacity : Nat) (blk : BitVec 64)
    (saved : Nat → BitVec 64) (start : Config) (k : Nat) (c : Config) : Prop where
  bound : k ≤ 6
  pc : PCAt 0x80004c4c#64 c
  regs : GHolds c.σ [(10,codeScanResult k),(9,BitVec.ofNat 64 (6-k)),(18,seekOffset (k+1)),
    (19,BitVec.ofNat 64 (8*(6-k))),(8,seekCursor blk k),(20,codeSectionName0),
    (21,WhileMinElfParse.trailSlot),(22,3#64),(2,seekStack)]
  ready : RuntimeReady H capacity seekStack 0x80004c4c#64 c
  table : CodeScanTable blk c
  memory : c.σ.mem = writeLog start.σ.mem (seekSaveLog saved)
  abi : GprsSame start c codeScanWrites

/-- All input observations and allocations belong to the actual optional-section call. -/
structure CodeScanInput (H : List (Nat × Nat)) (capacity : Nat) (blk node : BitVec 64) (c : Config) : Prop where
  pc : PCAt 0x80004bcc#64 c
  regs : GHolds c.σ ((1,0x80004ea8#64) :: codeSeekArgs)
  ready : RuntimeReady H capacity parameterStack 0x80004ea8#64 c
  observed : WhileMinElfParse.CodeSeekSourceObserved blk node c
  descriptorOwned : (blk.toNat,56) ∈ H
  filenameOwned : (node.toNat,5) ∈ H
  caller : LoadCaller c

/-- Open the real optional-section frame, retaining the exact saved bank and current table. -/
theorem code_scan_start {H capacity blk node c} (I : CodeScanInput H capacity blk node c) :
    ∃ d, Steps c d ∧ CodeScanAt H capacity blk (vsaReg c) c 0 d := by
  let saved := vsaReg c
  have bank (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c.σ n = some (saved n) :=
    library_gpr I.ready.platform lo hi rfl
  obtain ⟨a,runA,A⟩ := (seek_optional_entry c saved I.ready.toLeafInput
    ⟨I.ready.stack,bank 9 (by decide) (by decide),I.ready.raReg,bank 18 (by decide) (by decide),
      gholds_lookup (n := 11) _ I.regs rfl,gholds_lookup (n := 10) _ I.regs rfl,trivial⟩
    I.observed.count).run c ⟨I.pc,rfl⟩
  have gA := GprsSame.of_post A (by decide)
  have readyA := I.ready.stack_log A (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ A.regs rfl) (gholds_lookup (n := 1) _ A.regs rfl) (by decide)
    seek_frame (seekHeadLog_inside saved)
  have tableA : bytesT a.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk := by
    rw [word_observed (m := c.σ.mem) _ fun j hj => by
      rw [A.memory,frameOn_writeLog _ _ _ (seekHeadLog_inside saved) _ ⟨Or.inr (by
        change parameterStack.toNat ≤ (WhileMinElfParse.trailSlot + 16#64).toNat + j
        have base : parameterStack.toNat ≤ (WhileMinElfParse.trailSlot + 16#64).toNat := by decide
        omega),trivial⟩]]
    exact I.observed.table
  obtain ⟨d,runD,D⟩ := (seek_optional_setup a saved blk readyA.toLeafInput
    ⟨gA.get (by decide) (by decide) (by decide) (bank 19 (by decide) (by decide)),readyA.stack,
      gA.get (by decide) (by decide) (by decide) (bank 20 (by decide) (by decide)),
      gA.get (by decide) (by decide) (by decide) (bank 21 (by decide) (by decide)),
      gA.get (by decide) (by decide) (by decide) (bank 22 (by decide) (by decide)),
      gA.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ I.regs rfl),
      gholds_lookup (n := 11) _ A.regs rfl,gholds_lookup (n := 18) _ A.regs rfl,
      gholds_lookup (n := 9) _ A.regs rfl,
      gA.get (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ I.regs rfl),A.result,trivial⟩
    tableA).run a ⟨A.pc,rfl⟩
  have gD := GprsSame.of_post D (by decide)
  have readyD := readyA.stack_log D (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ D.regs rfl)
    (gD.get (by decide) (by decide) (by decide) readyA.raReg) (by decide)
    seek_frame (seekTailLog_inside saved)
  have liveA : LiveFrame H c a := LiveFrame.of_stack A.memory (seekHeadLog_inside saved) seek_frame
    (fun e he => (I.ready.block_bounds he).2)
  have liveD : LiveFrame H a d := LiveFrame.of_stack D.memory (seekTailLog_inside saved) seek_frame
    (fun e he => (I.ready.block_bounds he).2)
  have live := liveA.trans liveD
  have geometry := I.ready.block_bounds I.descriptorOwned
  refine ⟨d,runA.trans runD,{
    bound := by decide
    pc := D.pc
    regs := ⟨gholds_lookup (n := 8) _ D.regs rfl,gholds_lookup (n := 9) _ D.regs rfl,
      gholds_lookup (n := 18) _ D.regs rfl,gholds_lookup (n := 19) _ D.regs rfl,
      gholds_lookup (n := 20) _ D.regs rfl,gholds_lookup (n := 21) _ D.regs rfl,
      gholds_lookup (n := 22) _ D.regs rfl,readyD.stack,trivial⟩
    ready := readyD
    table := ⟨geometry.1,geometry.2,fun j hj => by
      rw [live.byte _ I.descriptorOwned _ (by unfold InExt; dsimp only; omega)]
      exact I.observed.descriptor j hj⟩
    memory := (write_post_seq A D).memory
    abi := (gA.trans gD).mono (by decide) }⟩

/-- Compare one actual current descriptor, retaining the full native frame. -/
theorem code_scan_compare_call {H capacity blk saved start k c}
    (S : CodeScanAt H capacity blk saved start k c) :
    ∃ d, Steps c d ∧ CodeScanCompared H capacity blk saved start k d := by
  obtain ⟨a,runA,A⟩ := (seek_optional_compare c (codeScanLink k) (seekCursor blk k)
    (seekOffset k) (seekLength k) (seekOffset (k+1)) S.ready.toLeafInput
    ⟨gholds_lookup (n := 8) _ S.regs rfl,gholds_lookup (n := 18) _ S.regs rfl,
      gholds_lookup (n := 20) _ S.regs rfl,trivial⟩
    (S.table.window k 4 4 S.bound (by decide)) (S.table.length k S.bound).1
    (seek_section_modular_step ⟨k,by have := S.bound; omega⟩)).run c ⟨S.pc,rfl⟩
  have gA := GprsSame.of_post A (by decide)
  have readyA := seek_readonly_ready S.ready A (by decide) (by decide)
    (gA.get (by decide) (by decide) (by decide) S.ready.stack)
    (gholds_lookup (n := 1) _ A.regs rfl) (by decide)
  have tableA : CodeScanTable blk a := ⟨S.table.lower,S.table.upper,
    fun j hj => by rw [show a.σ.mem = c.σ.mem from A.memory]; exact S.table.byte j hj⟩
  obtain ⟨d,runD,D⟩ := (code_scan_name a blk 0x80004c4c#64 k S.bound readyA.toLeafInput tableA
    (codeSection_name_0 readyA.image)
    ⟨gholds_lookup (n := 10) _ A.regs rfl,gholds_lookup (n := 11) _ A.regs rfl,
      gholds_lookup (n := 12) _ A.regs rfl,trivial⟩).run a ⟨A.pc,rfl⟩
  have gD := GprsSame.of_post D (by decide)
  have g := gA.trans gD
  have mem : d.σ.mem = c.σ.mem := D.memory.trans A.memory
  refine ⟨d,runA.trans runD,{
    bound := S.bound
    pc := D.pc
    regs := ⟨D.result,
      g.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ S.regs rfl),
      gD.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ A.regs rfl),
      g.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ S.regs rfl),
      g.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ S.regs rfl),
      g.get (by decide) (by decide) (by decide) (gholds_lookup (n := 20) _ S.regs rfl),
      g.get (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ S.regs rfl),
      g.get (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ S.regs rfl),
      g.get (by decide) (by decide) (by decide) S.ready.stack,trivial⟩
    ready := seek_readonly_ready readyA D (by decide) (by decide)
      (gD.get (by decide) (by decide) (by decide) readyA.stack)
      (gholds_lookup (n := 1) _ D.regs rfl) (by decide)
    table := ⟨S.table.lower,S.table.upper,fun j hj => by rw [mem]; exact S.table.byte j hj⟩
    memory := mem.trans S.memory
    abi := (S.abi.trans g).mono (by decide) }⟩

/-- The signed ADDIW countdown observation on the six actual back edges. -/
theorem code_scan_countdown (k : Nat) (hk : k < 6) :
    seekCountDown (BitVec.ofNat 64 (6-k)) =
        BitVec.ofNat 64 (6-(k+1)) := by
  have checked : ∀ i : Fin 6,
    seekCountDown (BitVec.ofNat 64 (6 - i.val)) =
        BitVec.ofNat 64 (6-(i.val+1)) := by decide
  exact checked ⟨k,hk⟩

/-- Natural descriptor displacement agrees with the native eight-byte decrement. -/
theorem code_scan_backoffset (k : Nat) (hk : k < 6) :
    BitVec.ofNat 64 (8*(6-k)) + (-8#64) = BitVec.ofNat 64 (8*(6-(k+1))) := by
  have checked : ∀ i : Fin 6,
    BitVec.ofNat 64 (8*(6 - i.val)) + (-8#64) = BitVec.ofNat 64 (8*(6-(i.val+1))) := by decide
  exact checked ⟨k,hk⟩

/-- One real reverse-scan back edge after a non-CODE descriptor. -/
theorem code_scan_iteration {H capacity blk saved start k c}
    (S : CodeScanAt H capacity blk saved start k c) (hk : k < 6) :
    ∃ d, Steps c d ∧ CodeScanAt H capacity blk saved start (k+1) d := by
  obtain ⟨a,runA,A⟩ := code_scan_compare_call S
  obtain ⟨d,runD,D⟩ := (seek_optional_next a (seekCursor blk k) (BitVec.ofNat 64 (8*(6-k)))
    (BitVec.ofNat 64 (6-k)) (codeScanResult k) 0x80004c4c#64 A.ready.toLeafInput
    ⟨gholds_lookup (n := 9) _ A.regs rfl,A.regs.1,
      gholds_lookup (n := 19) _ A.regs rfl,gholds_lookup (n := 8) _ A.regs rfl,trivial⟩
    (codeScanResult_nonzero k hk) (by
      rw [code_scan_countdown k hk]
      have checked : ∀ i : Fin 6, guardB bop.BLT (BitVec.ofNat 64 (6-(i.val+1))) 0#64 = false := by decide
      exact checked ⟨k,hk⟩)).run a ⟨A.pc,rfl⟩
  have gD := GprsSame.of_post D (by decide)
  have cursor : seekCursor blk k + (-8#64) = seekCursor blk (k+1) := by
    unfold seekCursor
    rw [BitVec.add_assoc,code_scan_backoffset k hk]
  have ready := seek_readonly_ready A.ready D (by decide) (by decide)
    (gD.get (by decide) (by decide) (by decide) A.ready.stack)
    (gD.get (by decide) (by decide) (by decide) A.ready.raReg) (by decide)
  refine ⟨d,runA.trans runD,{
    bound := by omega
    pc := D.pc
    regs := ⟨gholds_lookup_eq D.regs rfl cursor,
      gholds_lookup_eq D.regs rfl (code_scan_countdown k hk),
      gD.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ A.regs rfl),
      gholds_lookup_eq D.regs rfl (code_scan_backoffset k hk),
      gD.get (by decide) (by decide) (by decide) (gholds_lookup (n := 20) _ A.regs rfl),
      gD.get (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ A.regs rfl),
      gD.get (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ A.regs rfl),
      ready.stack,trivial⟩
    ready := by simpa only [codeScanLink,show k+1 ≠ 0 by omega,ite_false] using ready
    table := ⟨A.table.lower,A.table.upper,
      fun j hj => by rw [show d.σ.mem = a.σ.mem from D.memory]; exact A.table.byte j hj⟩
    memory := D.memory.trans A.memory
    abi := (A.abi.trans gD).mono (by decide) }⟩

/-- The loop's observed index is derived from its actual signed countdown register. -/
def codeScanIndex (c : Config) : Nat := 6 - ((gprGet c.σ 9).getD 0).toNat

theorem CodeScanAt.index {H capacity blk saved start k c}
    (S : CodeScanAt H capacity blk saved start k c) : codeScanIndex c = k := by
  have bound := S.bound
  simp only [codeScanIndex,gholds_lookup (n := 9) _ S.regs rfl,Option.getD_some,BitVec.toNat_ofNat]
  omega

/-- Fold the six real non-CODE iterations using the native countdown index. -/
theorem code_scan_loop (H : List (Nat × Nat)) (capacity : Nat) (blk : BitVec 64)
    (saved : Nat → BitVec 64) (start : Config) :
    Triple (CodeScanAt H capacity blk saved start 0) (CodeScanAt H capacity blk saved start 6) :=
  indexed_loop codeScanIndex 6 0 _ (fun _ _ h => h.bound) (fun _ _ h => h.index)
    (fun _ _ h hk => code_scan_iteration h hk)

end OCaml.Vm.Boot.Startup
