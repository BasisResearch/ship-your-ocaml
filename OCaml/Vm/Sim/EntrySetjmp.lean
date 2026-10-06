import OCaml.Vm.Sim.EntryFrame
import OCaml.Vm.Sim.SetjmpSegment
import OCaml.Vm.Sim.SetjmpPins

/-!
# caml_interprete's entry, part 3: newlib `setjmp`

`entry_setjmp` runs the generated `tr_setjmp` from the prep call: it stores
ra, s0–s11 and sp into `raise_buf` and returns 0 to caml_interprete.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The jump-buffer stores, in program order (ra, s0, s1, s2–s11, sp). -/
def setjmpLog (buf : Nat) (regs : Nat → BitVec 64) (sp : BitVec 64) : List WEntry :=
  [(buf + 0, 8, 0x80001e80#64), (buf + 8, 8, regs 8), (buf + 16, 8, regs 9), (buf + 24, 8, regs 18),
   (buf + 32, 8, regs 19), (buf + 40, 8, regs 20), (buf + 48, 8, regs 21), (buf + 56, 8, regs 22),
   (buf + 64, 8, regs 23), (buf + 72, 8, regs 24), (buf + 80, 8, regs 25), (buf + 88, 8, regs 26),
   (buf + 96, 8, regs 27), (buf + 104, 8, sp)]

/-- The callee-saved registers setjmp saves (besides ra and sp). -/
def setjmpRegs : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

structure EntrySetjmpInput (c : Config) (buf : Nat) (regs : Nat → BitVec 64) (sp : BitVec 64) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  pc : pcOf c = some 0x80042c4c#64
  buffer : gpr c 10 = some (BitVec.ofNat 64 buf)
  ra : gpr c 1 = some 0x80001e80#64
  saved : ∀ r ∈ setjmpRegs, gpr c r = some (regs r)
  stack : gpr c 2 = some sp
  low : Vsa.Sim.DlHeap.heapEnd ≤ buf
  high : buf + Layout.jumpBufferBytes ≤ Layout.sym_stack_top
  aligned : buf % 8 = 0

structure EntrySetjmpPost (before : Config) (buf : Nat) (regs : Nat → BitVec 64) (sp : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x80001e80#64
  result : gpr after 10 = some 0#64
  ra : gpr after 1 = some 0x80001e80#64
  saved : ∀ r ∈ setjmpRegs, gpr after r = some (regs r)
  stack : gpr after 2 = some sp
  memory : after.σ.mem = writeLog before.σ.mem (setjmpLog buf regs sp)
  output : after.σ.sailOutput = before.σ.sailOutput
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  gprs : OCaml.Vm.Boot.Startup.GprPresent before.σ → OCaml.Vm.Boot.Startup.GprPresent after.σ
  /-- the global pointer is untouched (the loop's `LoopRegisters.gp`) -/
  gp : gpr after 3 = gpr before 3

theorem setjmpLog_above {buf : Nat} {regs : Nat → BitVec 64} {sp : BitVec 64}
    (low : Vsa.Sim.DlHeap.heapEnd ≤ buf) : ∀ e ∈ setjmpLog buf regs sp, Vsa.Sim.DlHeap.heapEnd ≤ e.1 := by
  intro e he
  simp only [setjmpLog, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Nat.le_trans low (Nat.le_add_right _ _)

theorem entry_setjmp {c : Config} {buf : Nat} {regs : Nat → BitVec 64} {sp : BitVec 64}
    (h : EntrySetjmpInput c buf regs sp) :
    ∃ n after, StepsN n c after ∧ EntrySetjmpPost c buf regs sp after := by
  have bl : 0x86800000 ≤ buf := h.low
  have bh : buf + 112 ≤ 0x88000000 := h.high
  have ba := h.aligned
  have hb : (BitVec.ofNat 64 buf).toNat = buf := Nat.mod_eq_of_lt (by omega)
  have r (k : Nat) (hk : k ∈ setjmpRegs) := h.saved k hk
  have bp : SegSt (0x80042c4c#64) [⟨Register.x10, BitVec.ofNat 64 buf⟩, ⟨Register.x1, 0x80001e80#64⟩,
      ⟨Register.x8, regs 8⟩, ⟨Register.x9, regs 9⟩, ⟨Register.x18, regs 18⟩, ⟨Register.x19, regs 19⟩,
      ⟨Register.x20, regs 20⟩, ⟨Register.x21, regs 21⟩, ⟨Register.x22, regs 22⟩, ⟨Register.x23, regs 23⟩,
      ⟨Register.x24, regs 24⟩, ⟨Register.x25, regs 25⟩, ⟨Register.x26, regs 26⟩, ⟨Register.x27, regs 27⟩,
      ⟨Register.x2, sp⟩]
      (fun σ => Vsa.Sim.Code.CamlSetjmpLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.buffer, h.ra, r 8 (by decide), r 9 (by decide), r 18 (by decide),
      r 19 (by decide), r 20 (by decide), r 21 (by decide), r 22 (by decide), r 23 (by decide),
      r 24 (by decide), r 25 (by decide), r 26 (by decide), r 27 (by decide), h.stack, trivial⟩,
      h.good.minstret, h.tick, setjmp_loaded h.image, rfl, rfl⟩
  have run := tr_setjmp (BitVec.ofNat 64 buf) 0x80001e80#64 (regs 8) (regs 9) (regs 18) (regs 19)
    (regs 20) (regs 21) (regs 22) (regs 23) (regs 24) (regs 25) (regs 26) (regs 27) sp c.σ.mem c.σ
  simp (disch := decide) only [addr_pos _ _ hb (by omega), BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at run
  have ret : BitVec.update ((0x80001e80#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1 =
      0x80001e80#64 := by decide
  rw [ret] at run
  obtain ⟨n, after, _, steps, post⟩ := run (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) _ rfl (by decide) c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have memLog : after.σ.mem = writeLog c.σ.mem (setjmpLog buf regs sp) := by
    rw [memory]; rfl
  have zero : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) = 0#64 := by decide
  have x10 : gpr after 10 = some ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) :=
    PinsHold.get post.pins ⟨0, by simp⟩
  rw [zero] at x10
  refine ⟨n, after, steps, post.good,
    image_of_writeLog h.image (image_outside_of_above (setjmpLog_above h.low)) memLog,
    post.tick, post.pcAt, x10, PinsHold.get post.pins ⟨1, by simp⟩, ?_,
    PinsHold.get post.pins ⟨14, by simp⟩, memLog, frame.out, frame.frame _ (by decide),
    fun p => p.of_stepFrame frame (writes := [10, 1]) (by decide) (by decide +kernel)
      (written_of_pins post.pins (by simp [gprReg])), frame.frame Register.x3 (by decide)⟩
  intro k hk
  exact (frame.gpr_list (L := setjmpRegs) (by decide +kernel) k hk).trans (h.saved k hk)

end OCaml.Vm.Sim
