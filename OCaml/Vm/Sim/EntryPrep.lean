import OCaml.Vm.Sim.EntrySave
import OCaml.Vm.Sim.InterpEntryPrepSegment
import OCaml.Vm.Sim.InterpEntryPrepPins

/-!
# caml_interprete's entry, part 2: runtime saves and the setjmp call

`entry_prep` runs `tr_interp_entry_prep`: it stores `prog`, increments
`caml_callback_depth`, saves `stack_high`, `local_roots`, `extern_sp` and
`external_raise` into the native frame, and jumps to `setjmp` with
`a0 = &raise_buf`. Every load is read back from the pre-state: the stores
before it lie in the native frame (above `heapEnd`) or at
`caml_callback_depth` (below `heapStart`), and `Caml_state` lies between.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `caml_callback_depth + 1`, as the native ADDIW/SW computes it. -/
def entryDepth (c : Config) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb
    (sign_extend (m := 64) (bytesT4 c.σ.mem Layout.sym_caml_callback_depth) + sign_extend (m := 64) (0x001#12)) 31 0)

/-- A `Caml_state` field of `c`. -/
def domainField (c : Config) (off : Nat) : BitVec 64 :=
  word c ((word c Layout.sym_Caml_state).toNat + off)

/-- A `Caml_state` field reads back through any log that misses it. -/
theorem domainField_read {c : Config} {log : List WEntry} {off : Nat}
    (h : OutLRange log ((word c Layout.sym_Caml_state).toNat + off) 8) :
    domainField c off = sign_extend (m := 64)
      (bytesT8 (writeLog c.σ.mem log) ((word c Layout.sym_Caml_state).toNat + off)) := by
  rw [← bytesT_eight_eq, bytesT_writeLog_out _ h]
  simp only [domainField, word, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- The prep stores, in program order. -/
def entryPrepLog (sp : Nat) (a0 : BitVec 64) (c : Config) : List WEntry :=
  [(sp - Layout.interpFrameBytes + 16, 8, a0), (Layout.sym_caml_callback_depth, 4, entryDepth c),
   (sp - Layout.interpFrameBytes, 8, domainField c Layout.off_stack_high),
   (sp - Layout.interpFrameBytes + 200, 8, domainField c Layout.off_local_roots),
   (sp - Layout.interpFrameBytes + 8, 8, domainField c Layout.off_extern_sp),
   (sp - Layout.interpFrameBytes + 24, 8, domainField c Layout.off_external_raise)]

/-- `Caml_state`'s record lies in the allocator arena. -/
structure DomainWindow (d : Nat) : Prop where
  low : Vsa.Sim.DlHeap.heapStart ≤ d
  high : d + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  aligned : d % 8 = 0

theorem DomainWindow.nat {d : Nat} (h : DomainWindow d) :
    0x8007d140 ≤ d ∧ d + 928 ≤ 0x86800000 ∧ d % 8 = 0 :=
  ⟨h.low, h.high, h.aligned⟩

theorem entryPrep_image {sp : Nat} {a0 : BitVec 64} {c : Config} (b1 : 0x86800210 ≤ sp)
    (b2 : sp + 112 ≤ 0x88000000) : ImageOutside (entryPrepLog sp a0 c) := by
  constructor <;>
    simp only [OutLRange, entryPrepLog, Layout.interpFrameBytes, Layout.sym_caml_callback_depth,
      Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize, and_true] <;> omega

structure EntryPrepInput (c : Config) (sp : Nat) (a0 : BitVec 64) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  pc : pcOf c = some 0x80001e38#64
  stack : gpr c 2 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))
  arg : gpr c 10 = some a0
  frame : EntryFrame sp
  domain : DomainWindow (word c Layout.sym_Caml_state).toNat

structure EntryPrepPost (before : Config) (sp : Nat) (a0 : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x80042c4c#64
  ra : gpr after 1 = some 0x80001e80#64
  buffer : gpr after 10 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes + 208))
  stack : gpr after 2 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))
  preserved : ∀ r ∈ Layout.interpSavedRegs.tail, gpr after r = gpr before r
  memory : after.σ.mem = writeLog before.σ.mem (entryPrepLog sp a0 before)
  output : after.σ.sailOutput = before.σ.sailOutput
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  gprs : OCaml.Vm.Boot.Startup.GprPresent before.σ → OCaml.Vm.Boot.Startup.GprPresent after.σ

theorem entry_prep {c : Config} {sp : Nat} {a0 : BitVec 64} (h : EntryPrepInput c sp a0) :
    ∃ n after, StepsN n c after ∧ EntryPrepPost c sp a0 after := by
  obtain ⟨b1, b2, b3⟩ := h.frame.nat
  obtain ⟨d1, d2, d3⟩ := h.domain.nat
  have sym1 : ((0x80001e38#64) + (sign_extend (m := 64) ((0x00063#20) +++ 0x000#12))) +
      sign_extend (m := 64) (0xe00#12) = BitVec.ofNat 64 Layout.sym_caml_callback_depth := by decide
  have sym2 : ((0x80001e40#64) + (sign_extend (m := 64) ((0x00063#20) +++ 0x000#12))) +
      sign_extend (m := 64) (0xec8#12) = BitVec.ofNat 64 Layout.sym_Caml_state := by decide
  have sym3 : ((0x80001e50#64) + (sign_extend (m := 64) ((0x00063#20) +++ 0x000#12))) +
      sign_extend (m := 64) (0xde8#12) = BitVec.ofNat 64 Layout.sym_caml_callback_depth := by decide
  have hb : (BitVec.ofNat 64 (sp - Layout.interpFrameBytes)).toNat = sp - 528 :=
    Nat.mod_eq_of_lt (by simp only [Layout.interpFrameBytes]; omega)
  have domainRead : word c Layout.sym_Caml_state =
      sign_extend (m := 64) (bytesT8 c.σ.mem Layout.sym_Caml_state) := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have bp : SegSt (0x80001e38#64) [⟨Register.x2, BitVec.ofNat 64 (sp - Layout.interpFrameBytes)⟩, ⟨Register.x10, a0⟩]
      (fun σ => Vsa.Sim.Code.CamlInterpEntryPrepLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.stack, h.arg, trivial⟩, h.good.minstret, h.tick,
      interp_entry_prep_loaded h.image, rfl, rfl⟩
  have run := tr_interp_entry_prep (BitVec.ofNat 64 (sp - Layout.interpFrameBytes)) a0 c.σ.mem c.σ
  have m1 : Layout.sym_caml_callback_depth % 18446744073709551616 = Layout.sym_caml_callback_depth := by decide
  have m2 : Layout.sym_Caml_state % 18446744073709551616 = Layout.sym_Caml_state := by decide
  simp only [sym1, sym2, sym3, BitVec.toNat_ofNat, Nat.reducePow, m1, m2] at run
  simp (disch := decide) only [addr_pos _ _ hb (by omega), BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at run
  have run := run (by slot_tac) (by slot_tac) (by slot_tac) _ rfl
    (by slot_tac) (by slot_tac) (by slot_tac) (word c Layout.sym_Caml_state) domainRead
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac)
    (writeLog c.σ.mem [(sp - 528 + 16, 8, a0)]) rfl
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac)
    (writeLog c.σ.mem [(sp - 528 + 16, 8, a0), (Layout.sym_caml_callback_depth, 4, entryDepth c)]) rfl
  have hd : (word c Layout.sym_Caml_state).toNat = (word c Layout.sym_Caml_state).toNat := rfl
  simp (disch := decide) only [addr_pos _ _ hd (by omega), BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at run
  obtain ⟨n, after, _, steps, post⟩ := run
    (by slot_tac) (by slot_tac) (by slot_tac) (domainField c Layout.off_stack_high) (domainField_read (by out_tac))
    (by slot_tac) (by slot_tac) (by slot_tac) (domainField c Layout.off_local_roots) (domainField_read (by out_tac))
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (writeLog c.σ.mem [(sp - 528 + 16, 8, a0), (Layout.sym_caml_callback_depth, 4, entryDepth c), (sp - 528 + 0, 8, domainField c Layout.off_stack_high)]) rfl
    (by slot_tac) (by slot_tac) (by slot_tac) (domainField c Layout.off_extern_sp) (domainField_read (by out_tac))
    (by slot_tac) (by slot_tac) (by slot_tac) (domainField c Layout.off_external_raise) (domainField_read (by out_tac))
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (writeLog c.σ.mem [(sp - 528 + 16, 8, a0), (Layout.sym_caml_callback_depth, 4, entryDepth c), (sp - 528 + 0, 8, domainField c Layout.off_stack_high), (sp - 528 + 200, 8, domainField c Layout.off_local_roots)]) rfl
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (writeLog c.σ.mem [(sp - 528 + 16, 8, a0), (Layout.sym_caml_callback_depth, 4, entryDepth c), (sp - 528 + 0, 8, domainField c Layout.off_stack_high), (sp - 528 + 200, 8, domainField c Layout.off_local_roots), (sp - 528 + 8, 8, domainField c Layout.off_extern_sp)]) rfl
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (writeLog c.σ.mem [(sp - 528 + 16, 8, a0), (Layout.sym_caml_callback_depth, 4, entryDepth c), (sp - 528 + 0, 8, domainField c Layout.off_stack_high), (sp - 528 + 200, 8, domainField c Layout.off_local_roots), (sp - 528 + 8, 8, domainField c Layout.off_extern_sp), (sp - 528 + 24, 8, domainField c Layout.off_external_raise)]) rfl c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have memLog : after.σ.mem = writeLog c.σ.mem (entryPrepLog sp a0 c) := by
    rw [memory]; simp only [entryPrepLog, Layout.interpFrameBytes, Nat.add_zero]
  have buf : BitVec.ofNat 64 (sp - Layout.interpFrameBytes) + sign_extend (m := 64) (0x0d0#12) =
      BitVec.ofNat 64 (sp - Layout.interpFrameBytes + 208) := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_pos _ _ hb (by omega) _ (by decide), BitVec.toNat_ofNat]
    simp only [Layout.interpFrameBytes]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  refine ⟨n, after, steps, post.good, image_of_writeLog h.image (entryPrep_image b1 b2) memLog,
    post.tick, post.pcAt, PinsHold.get post.pins ⟨0, by simp⟩, ?_, PinsHold.get post.pins ⟨6, by simp⟩,
    frame.gpr_list (by decide +kernel), memLog, frame.out, frame.frame _ (by decide +kernel),
    fun p => p.of_stepFrame frame (writes := [1, 15, 14, 10, 13, 12]) (by decide) (by decide +kernel)
      (written_of_pins post.pins (by simp [gprReg]))⟩
  have x10 : gpr after 10 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes) +
      sign_extend (m := 64) (0x0d0#12)) := PinsHold.get post.pins ⟨3, by simp⟩
  rw [buf] at x10
  exact x10

end OCaml.Vm.Sim
