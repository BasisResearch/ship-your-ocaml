import OCaml.Refinement
import OCaml.Vm.Sim.EntrySetjmp
import OCaml.Vm.Sim.EntryResume
import OCaml.Vm.Sim.LoopSetup
import OCaml.Vm.Gc.Readback

/-!
# caml_interprete's entry as one native run

`entry_native` chains the prologue saves, the runtime saves and setjmp call,
newlib setjmp, the zero-result resume and LOOP_SETUP. It ends at the loop
head with the dispatch registers, the initial VM registers read from the
start state (pc = `prog`, sp = `extern_sp`, accu = `Val_int 0`, env =
`Atom(0)`, extra = 0) and one write log relative to the start state.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `&raise_buf`, the jump buffer in the interpreter frame. -/
abbrev entryBuffer (sp : Nat) : Nat := sp - Layout.interpFrameBytes + 208

/-- Every store entry makes, relative to the start state. -/
def entryLog (sp : Nat) (regs : Nat → BitVec 64) (a0 : BitVec 64) (c : Config) : List WEntry :=
  entrySaveLog sp regs ++ entryPrepLog sp a0 c ++
    setjmpLog (entryBuffer sp) regs (BitVec.ofNat 64 (sp - Layout.interpFrameBytes)) ++ entryResumeLog sp c

structure EntryNativeInput (c : Config) (sp : Nat) (regs : Nat → BitVec 64) (a0 : BitVec 64) : Prop
    extends EntrySaveInput c sp regs a0 where
  domain : DomainWindow (word c Layout.sym_Caml_state).toNat
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = some 0#4

structure EntryNativePost (before : Config) (sp : Nat) (regs : Nat → BitVec 64) (a0 : BitVec 64)
    (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  head : pcOf after = some (BitVec.ofNat 64 Layout.loopHead)
  loop : LoopRegisters after
  vmPc : gpr after 8 = some a0
  vmSp : gpr after 9 = some (domainField before Layout.off_extern_sp)
  accu : gpr after 21 = some 1#64
  extra : gpr after 18 = some 0#64
  env : gpr after 25 = some (word before Layout.sym_caml_atom_table + 8#64)
  stack : gpr after 2 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))
  memory : after.σ.mem = writeLog before.σ.mem (entryLog sp regs a0 before)
  output : after.σ.sailOutput = before.σ.sailOutput
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

/-- A word outside a write log reads the same before and after it. -/
theorem word_of_log {c c' : Config} {log : List WEntry} {a : Nat}
    (memory : c'.σ.mem = writeLog c.σ.mem log) (h : OutLRange log a 8) : word c' a = word c a := by
  rw [word, memory, bytesT_writeLog_out _ h]; rfl

/-- Close an `OutLRange` goal over the explicit entry logs. -/
macro "entry_out" : tactic =>
  `(tactic| (simp only [Vsa.Sim.OutLRange, entrySaveLog, entryPrepLog, setjmpLog, OCaml.Vm.Layout.interpSavedRegs,
      List.map, OCaml.Vm.Layout.interpSaveOffset, OCaml.Vm.Layout.interpFrameBytes,
      OCaml.Vm.Layout.sym_caml_callback_depth, OCaml.Vm.Layout.sym_caml_atom_table,
      OCaml.Vm.Layout.off_stack_high, OCaml.Vm.Layout.off_local_roots, OCaml.Vm.Layout.off_extern_sp,
      OCaml.Vm.Layout.off_external_raise, entryBuffer, List.drop_succ_cons, List.drop_zero, and_true]; omega))

theorem entry_native {c : Config} {sp : Nat} {regs : Nat → BitVec 64} {a0 : BitVec 64}
    (h : EntryNativeInput c sp regs a0) :
    ∃ n after, StepsN n c after ∧ EntryNativePost c sp regs a0 after := by
  obtain ⟨b1, b2, b3⟩ := h.frame.nat
  obtain ⟨d1, d2, d3⟩ := h.domain.nat
  have symD : Layout.sym_Caml_state = 0x80064d08 := rfl
  -- prologue saves
  obtain ⟨n1, c1, s1, p1⟩ := entry_save h.toEntrySaveInput
  have dom1 : word c1 Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    word_of_log p1.memory (by rw [symD]; entry_out)
  have field1 (off : Nat) (ho : off + 8 ≤ Layout.domainStateBytes) :
      domainField c1 off = domainField c off := by
    simp only [domainField, dom1]
    exact word_of_log p1.memory (by simp only [Layout.domainStateBytes] at ho; entry_out)
  -- runtime saves and the setjmp call
  obtain ⟨n2, c2, s2, p2⟩ := entry_prep ⟨p1.good, p1.image, p1.tick, p1.pc, p1.stack, p1.arg, h.frame,
    by rw [dom1]; exact h.domain⟩
  have dom2 : word c2 Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    (word_of_log p2.memory (by rw [symD]; entry_out)).trans dom1
  have prog2 : word c2 (sp - Layout.interpFrameBytes + 16) = a0 := by
    rw [word, p2.memory]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 0 _ a0 rfl (by entry_out)
  have tail : Layout.interpSavedRegs.tail = setjmpRegs := rfl
  -- newlib setjmp
  obtain ⟨n3, c3, s3, p3⟩ := entry_setjmp (buf := entryBuffer sp) (regs := regs)
    (sp := BitVec.ofNat 64 (sp - Layout.interpFrameBytes)) ⟨p2.good, p2.image, p2.tick, p2.pc, p2.buffer, p2.ra,
    fun r hr => (p2.preserved r (tail ▸ hr)).trans (p1.saved r (List.mem_of_mem_tail (tail ▸ hr))),
    p2.stack, by simp only [entryBuffer, Layout.interpFrameBytes, Vsa.Sim.DlHeap.heapEnd]; omega,
    by simp only [entryBuffer, Layout.interpFrameBytes, Layout.jumpBufferBytes, Layout.sym_stack_top]; omega,
    by simp only [entryBuffer, Layout.interpFrameBytes]; omega⟩
  have dom3 : word c3 Layout.sym_Caml_state = word c Layout.sym_Caml_state :=
    (word_of_log p3.memory (by rw [symD]; entry_out)).trans dom2
  -- every word the three logs miss reads as in `c`
  have w3 (a : Nat) (o1 : OutLRange (entrySaveLog sp regs) a 8) (o2 : OutLRange (entryPrepLog sp a0 c1) a 8)
      (o3 : OutLRange (setjmpLog (entryBuffer sp) regs (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))) a 8) :
      word c3 a = word c a :=
    ((word_of_log p3.memory o3).trans (word_of_log p2.memory o2)).trans (word_of_log p1.memory o1)
  have prog3 : word c3 (sp - Layout.interpFrameBytes + 16) = a0 :=
    (word_of_log p3.memory (by entry_out)).trans prog2
  -- zero-result resume
  obtain ⟨n4, c4, s4, p4⟩ := entry_resume ⟨p3.good, p3.image, p3.tick, p3.pc, p3.result, p3.stack, h.frame,
    by rw [dom3]; exact h.domain⟩
  -- loop registers
  obtain ⟨n5, c5, s5, p5⟩ := loop_setup ⟨p4.good, p4.image, p4.tick, p4.pc,
    p4.htif.trans (p3.htif.trans (p2.htif.trans (p1.htif.trans h.htifIdle)))⟩
  have keep : ∀ n ∈ [8, 9, 18, 21, 25, 2], gprGet c5.σ n = gprGet c4.σ n :=
    p5.frame.gpr_list (by decide +kernel)
  have depth1 : entryDepth c1 = entryDepth c := by
    simp only [entryDepth, ← bytesT_four_eq, p1.memory]
    rw [bytesT_writeLog_out _ (by entry_out)]
  have prepEq : entryPrepLog sp a0 c1 = entryPrepLog sp a0 c := by
    simp (disch := decide) only [entryPrepLog, depth1, field1]
  have resumeEq : entryResumeLog sp c3 = entryResumeLog sp c := by
    simp only [entryResumeLog, dom3]
  refine ⟨n1 + n2 + n3 + n4 + n5, c5, ((((s1.append s2).append s3).append s4).append s5), p5.good,
    p5.image, p5.tick, p5.head, p5.loop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (keep 8 (by decide)).trans (p4.vmPc.trans (by rw [prog3]))
  · refine (keep 9 (by decide)).trans (p4.vmSp.trans ?_)
    simp only [domainField, dom3]
    rw [w3 _ (by entry_out) (by entry_out) (by entry_out)]
  · exact (keep 21 (by decide)).trans p4.accu
  · exact (keep 18 (by decide)).trans p4.extra
  · refine (keep 25 (by decide)).trans (p4.env.trans ?_)
    rw [w3 _ (by entry_out) (by entry_out) (by entry_out)]
  · exact (keep 2 (by decide)).trans p4.stack
  · rw [p5.memory, p4.memory, p3.memory, p2.memory, p1.memory, resumeEq, prepEq, entryLog,
      writeLog_append, writeLog_append, writeLog_append]
  · exact p5.frame.out.trans (p4.output.trans (p3.output.trans (p2.output.trans p1.output)))
  · exact (p5.frame.frame _ (by decide)).trans (p4.htif.trans (p3.htif.trans (p2.htif.trans p1.htif)))

end OCaml.Vm.Sim
