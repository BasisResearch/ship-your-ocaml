import OCaml.Vm.Sim.GrabInitInput
import OCaml.Vm.Sim.GrabInitArithmetic
import OCaml.Vm.Sim.GrabAllocInitSegment
import OCaml.Vm.Sim.GrabAllocInitPins
import OCaml.Vm.Sim.GrabAllocInitLayout

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- GRAB initializes the reserved closure header and environment, and prepares
its actual source-cursor loop without an execution premise. -/
theorem grab_initialize {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit : Nat} {env : BitVec 64}
    (h : ArmInput L P s .GRAB c pl cp sp high) (environment : valWord pl s.env = some env)
    (nursery : GrabNurseryInput s.extra a domain limit c)
    (space : GrabInitInput sp s.extra a domain env c)
    (front : GrabReserved c s.extra a domain d) :
    ∃ nb after, StepsN nb d after ∧ GrabCopyStart c sp s.extra a domain env after := by
  have domainRead : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have headerNat := nursery.headerWrite.read.toNat
  have youngRead := nursery.youngWrite.read
  have envNat := space.envWrite.read.toNat
  have youngAddress : BitVec.ofNat 64 domain + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (domain + Layout.off_young_ptr) := by rw [BitVec.ofNat_add]; rfl
  have valueAddress : BitVec.ofNat 64 (a - 8) + sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 a := by
    change BitVec.ofNat 64 (a - 8) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]; congr 1; have room := nursery.room; omega
  have envAddress : BitVec.ofNat 64 a + sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 (a + 16) := by
    rw [BitVec.ofNat_add]; rfl
  have copyAddress : BitVec.ofNat 64 (a - 8) + sign_extend (m := 64) (0x020#12) = BitVec.ofNat 64 (a + 24) := by
    change BitVec.ofNat 64 (a - 8) + BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_add]; congr 1; have room := nursery.room; omega
  have headerValue : Sail.shift_bits_left (BitVec.ofNat 64 (s.extra + 4)) (Sail.BitVec.extractLsb (0x0a#6) 5 0) +
      sign_extend (m := 64) (0x0f7#12) = blockHeader (s.extra + 4) closureTag := rfl
  obtain ⟨headerMemory, headerWritten⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (a - 8) (sdData_val (blockHeader (s.extra + 4) closureTag)) := ⟨_, rfl⟩
  have headerLog : headerMemory = writeLog c.σ.mem
      (grabReserveLog domain a ++ [(a - 8, 8, blockHeader (s.extra + 4) closureTag)]) := by
    rw [headerWritten, front.memory, writeLog_append]; rfl
  have domainValue := (word_read_writeLog_out space.domainOutside headerLog).trans nursery.domainValue
  have youngWord : bytesT headerMemory (domain + Layout.off_young_ptr) 8 = BitVec.ofNat 64 (a - 8) := by
    rw [headerLog]
    exact word_writeLog_at c.σ.mem _ 0 _ _ rfl space.youngOutside
  have youngValue : sign_extend (m := 64) (bytesT8 headerMemory (domain + Layout.off_young_ptr)) =
      BitVec.ofNat 64 (a - 8) := by
    simpa only [bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using youngWord
  obtain ⟨nextMemory, written⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 headerMemory (a + 16) (sdData_val env) := ⟨_, rfl⟩
  have bp : SegSt (0x800036c0#64)
      [⟨Register.x10, BitVec.ofNat 64 (s.extra + 4)⟩, ⟨Register.x15, BitVec.ofNat 64 (a - 8)⟩,
       ⟨Register.x25, env⟩, ⟨Register.x18, BitVec.ofNat 64 s.extra⟩,
       ⟨Register.x23, BitVec.ofNat 64 s.extra⟩, ⟨Register.x9, BitVec.ofNat 64 sp⟩]
      (fun σ => Vsa.Sim.Code.CamlGrabAllocInitLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨front.good, front.pc, ⟨front.count, front.header,
      (front.frame.frame Register.x25 (by decide)).trans (represented_register h.env environment),
      (front.frame.frame Register.x18 (by decide)).trans h.extra, front.savedExtra,
      (front.frame.frame Register.x9 (by decide)).trans h.spReg, trivial⟩,
      front.good.minstret, front.tick, grab_alloc_init_loaded front.image, rfl, rfl⟩
  have run := tr_grab_alloc_init (BitVec.ofNat 64 (s.extra + 4)) (BitVec.ofNat 64 (a - 8)) env
    (BitVec.ofNat 64 s.extra) (BitVec.ofNat 64 s.extra) (BitVec.ofNat 64 sp) d.σ.mem d.σ
  simp only [grab_alloc_init_domain, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, headerNat, domainRead.toNat, headerValue] at run
  have first := run nursery.headerWrite.lower nursery.headerWrite.upper nursery.headerWrite.htif nursery.headerWrite.aligned
    (image_entry_code space.image (by exact List.mem_cons_self) (by decide) (by decide)) headerMemory headerWritten
    domainRead.lower domainRead.upper domainRead.htif (BitVec.ofNat 64 domain) domainValue.symm
  simp only [youngAddress, youngRead.toNat] at first
  have second := first youngRead.lower youngRead.upper youngRead.htif (BitVec.ofNat 64 (a - 8)) youngValue.symm
  simp only [valueAddress, envAddress, envNat, copyAddress, grab_source_end] at second
  obtain ⟨nb, after, _, steps, post⟩ := second space.envWrite.lower space.envWrite.upper space.envWrite.htif space.envWrite.aligned
    (image_entry_code space.image (List.mem_cons_of_mem _ List.mem_cons_self : (a + 16, 8, env) ∈ grabInitLog a s.extra env)
      (by decide) (by decide)) nextMemory written (grab_copy_nonempty s.extra (by have small := nursery.small; omega)) d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked (allowed := grabInitWrites) (by decide)
  have initMemory : after.σ.mem = writeLog d.σ.mem (grabInitLog a s.extra env) := by
    rw [memory, written, headerWritten]; rfl
  have fullMemory : after.σ.mem = writeLog c.σ.mem (grabSetupLog domain a s.extra env) := by
    rw [initMemory, front.memory, grabSetupLog, writeLog_append]
  have image := image_of_writeLog front.image space.image initMemory
  refine ⟨nb, after, steps, ?_⟩
  constructor
  · have length : (stackWords c sp (1 + s.extra)).length = 1 + s.extra := by simp [stackWords]
    refine ⟨post.good, post.tick, image, Nat.zero_le _, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · simp only [length, show 0 < 1 + s.extra by omega, ite_true]; exact post.pcAt
    · simp only [Nat.mul_zero, Nat.add_zero]; exact PinsHold.get post.pins ⟨1, by simp⟩
    · simp only [Nat.mul_zero, Nat.add_zero]; exact PinsHold.get post.pins ⟨0, by simp⟩
    · rw [length]; exact PinsHold.get post.pins ⟨2, by simp⟩
    · exact (StepFrameOut.refl after.σ).widenChecked (allowed := cursorCopyWrites) (by decide)
  · exact PinsHold.get post.pins ⟨5, by simp⟩
  · exact PinsHold.get post.pins ⟨3, by simp⟩
  · exact PinsHold.get post.pins ⟨4, by simp⟩
  · exact (frame.frame Register.x16 (by decide)).trans front.bytes
  · exact fullMemory
  · exact (front.frame.trans frame).widenChecked (allowed := grabSetupWrites) (by decide)

end OCaml.Vm.Sim
