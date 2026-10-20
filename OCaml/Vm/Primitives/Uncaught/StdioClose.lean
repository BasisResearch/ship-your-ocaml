import OCaml.Vm.Primitives.Uncaught.Close
import OCaml.Vm.Primitives.Uncaught.CloseR
import OCaml.Vm.Primitives.Uncaught.Sclose
import OCaml.Vm.Primitives.Named.NamedHash
import OCaml.Vm.Primitives.Console.Flush
import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Boot.Startup.NativeNested

/-!
# `_close` on a console descriptor, and its callers `_close_r` and `__sclose`

The runtime's file layer (`c/src`) keeps a table `fds` of 24-byte slots; a
console descriptor's slot has a nonzero kind other than 4 (a file). `_close`
clears the kind and returns 0 (`close_console`), `_close_r` clears `errno`
around it, and `__sclose` passes the `FILE`'s descriptor (`sclose_console`).
-/

namespace OCaml.Vm.Primitives.Uncaught.StdioClose
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some)
open OCaml.Vm.Boot.Startup (NativeFrame)

/-- The `fds` slot of descriptor `fd`. -/
def fdSlot (fd : BitVec 64) : BitVec 64 := 2147896728#64 + (fd <<< 1 + fd) <<< 3


theorem fdSlot_toNat {fd : BitVec 64} (small : fd.toNat < 32) : (fdSlot fd).toNat = 2147896728 + 24 * fd.toNat := by
  unfold fdSlot
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The slot lies in RAM, aligned, below the heap. -/
theorem fdSlot_read {fd : BitVec 64} (small : fd.toNat < 32) : ReadWindow (fdSlot fd) 8 := by
  have e := fdSlot_toNat small
  exact ⟨by omega, by omega, Or.inr (by rw [e]; simp only [Layout.sym_tohost]; omega)⟩

theorem fdSlot_write {fd : BitVec 64} (small : fd.toNat < 32) : WriteWindow (fdSlot fd) 4 := by
  have e := fdSlot_toNat small
  exact ⟨by omega, by omega, by rw [e]; simp only [Layout.sym_tohost]; omega, by omega⟩

/-- A native frame's slot `sp - k + off`, as a natural. -/
theorem frame_nat {sp : BitVec 64} {size k off : Nat} (h : NativeFrame sp size) (hk : k ≤ size) (ho : off ≤ k) :
    (sp - BitVec.ofNat 64 k + BitVec.ofNat 64 off).toNat = sp.toNat - k + off := by
  have lo := h.lower
  have hi := h.upper
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo hi
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A doubleword slot of a native frame is a write window. -/
theorem frame_word {sp : BitVec 64} {size k off : Nat} (h : NativeFrame sp size) (hk : k ≤ size)
    (ho : off + 8 ≤ k) (ak : k % 8 = 0) (ao : off % 8 = 0) :
    WriteWindow (sp - BitVec.ofNat 64 k + BitVec.ofNat 64 off) 8 := by
  have e := frame_nat h hk (by omega : off ≤ k)
  have lo := h.lower
  have hi := h.upper
  have al := h.aligned
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo hi
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> (try simp only [Layout.sym_tohost]) <;> omega

/-- A native frame's stores miss the image. -/
theorem frame_outside {sp : BitVec 64} {size k off w : Nat} {v : BitVec 64} (h : NativeFrame sp size)
    (hk : k ≤ size) (ho : off + w ≤ k) :
    ImageOutside [((sp - BitVec.ofNat 64 k + BitVec.ofNat 64 off).toNat, w, v)] := by
  have e := frame_nat h hk (by omega : off ≤ k)
  have lo := h.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  refine ⟨⟨?_, trivial⟩, ⟨?_, trivial⟩⟩ <;> rw [e] <;>
    simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega

/-- `_close`'s two stores: the saved `ra`, then the slot's kind. -/
def closeLog (sp ra fd : BitVec 64) : List WEntry :=
  [((sp - 32#64 + 24#64).toNat, 8, ra), ((fdSlot fd).toNat, 4, 0#64)]

/-- **`_close(fd)` on a console descriptor**: the slot's kind cleared, `0`
returned to `ra`. -/
theorem close_console {ra sp fd : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (a0 : gprGet c.σ 10 = some fd) (frame : NativeFrame sp 32)
    (ready : bytesVal .lw (read8 c.σ.mem (0x80064918#64).toNat) ≠ 0#64)
    (small : fd.toNat < 32)
    (live : bytesVal .lw (read8 c.σ.mem (fdSlot fd).toNat) ≠ 0#64)
    (notFile : bytesVal .lw (read8 c.σ.mem (fdSlot fd).toNat) ≠ 4#64) :
    FnSummary 0x80000b28#64 (fun d => d = c)
      (WriteRegistersPost [2, 13, 15, 15, 11, 12, 14, 15, 10, 10, 12, 15, 1, 2] (closeLog sp ra fd) c ra 0#64
        [(2, sp), (1, ra)]) := by
  have slotNat := frame_nat (k := 32) (off := 24) frame (by decide) (by decide)
  have fdNat := fdSlot_toNat small
  have lo := frame.lower
  simp only [Vsa.Sim.DlHeap.heapEnd] at lo
  have slotW : WriteWindow (sp + 18446744073709551584#64 + 24#64) 8 := by
    rw [show sp + 18446744073709551584#64 = sp - 32#64 by rw [BitVec.sub_eq_add_neg]; rfl]
    exact frame_word (k := 32) (off := 24) frame (by decide) (by decide) (by decide) (by decide)
  have kindR : ReadWindow (fdSlot fd) 4 := by
    have r := fdSlot_read small
    exact ⟨r.lower, by have := r.upper; omega, Or.inr (by rw [fdNat]; simp only [Layout.sym_tohost]; omega)⟩
  have kindW := fdSlot_write small
  have apart : OutLRange [((sp - 32#64 + 24#64).toNat, 8, ra)] (fdSlot fd).toNat 8 :=
    ⟨Or.inl (by rw [slotNat, fdNat]; omega), trivial⟩
  have outside : ImageOutside (closeLog sp ra fd) := by
    have fr := frame_outside (k := 32) (off := 24) (w := 8) (v := ra) frame (by decide) (by decide)
    exact ⟨⟨fr.1.1, Or.inl (by rw [fdNat]; simp only [Image.textBase, Image.textSize]; omega), trivial⟩,
      ⟨fr.2.1, Or.inl (by rw [fdNat]; simp only [Image.rodataBase, Image.rodataSize]; omega), trivial⟩⟩
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have r10 := regsAt_of a0
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h
  have spE : sp + 18446744073709551584#64 = sp - 32#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  obtain ⟨outRa, outKind⟩ : ImageOutside [((sp - 32#64 + 24#64).toNat, 8, ra)] ∧
      ImageOutside [((fdSlot fd).toNat, 4, 0#64)] :=
    ⟨⟨⟨outside.1.1, trivial⟩, ⟨outside.2.1, trivial⟩⟩, ⟨⟨outside.1.2.1, trivial⟩, ⟨outside.2.2.1, trivial⟩⟩⟩
  -- prologue: save ra; `fs_ready` is set
  apply summary_bind (Close.pro_fast c (regsAt c) l0
    (by simp only [Close.pro_input, GHolds, r1, r2, r10]; exact ⟨h.raReg, sp0, a0, trivial⟩)
    (by rw [r2]; exact slotW)
    (by simp only [Close.proLog, r1, r2]; exact outRa)
    (by simp only [Close.pro_loads, List.getD_cons_zero, guardB]; simpa using ready)) (fun _ p => p.pc)
  intro c1 p1
  have o1 := p1.regs
  simp only [Close.pro_regs, Close.pro_loads, r1, r2, r10, GHolds] at o1
  obtain ⟨g13, g2, -, g1, g10, -⟩ := o1
  have m1 : c1.σ.mem = writeLog c.σ.mem [((sp - 32#64 + 24#64).toNat, 8, ra)] := by
    rw [p1.memory]; simp only [Close.proLog, r1, r2]
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of g1]; exact ⟨p1.good, p1.image, p1.minstret, g1, h.aligned, p1.tick⟩
  -- `fd < 32`
  apply summary_bind (Close.range_fast c1 (regsAt c1) l1
    (by simp only [Close.range_input, GHolds, regsAt_of g10, regsAt_of g13]; exact ⟨g10, g13, trivial⟩)
    (by rw [regsAt_of g13]; unfold guardB Functions.zopz0zI_u; simp [Sail.BitVec.toNatInt]; omega)) (fun _ p => p.pc)
  intro c2 p2
  have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15]) : gprGet c2.σ n = gprGet c1.σ n :=
    p2.gpr_frame (by decide) n lo hi out
  have l2 : LeafInput (regsAt c2 1) c2 := by
    have e := (k2 1 (by decide) (by decide) (by decide)).trans g1
    rw [regsAt_of e]; exact ⟨p2.good, p2.image, p2.minstret, e, h.aligned, p2.tick⟩
  have f13 : gprGet c2.σ 13 = some fd := (k2 13 (by decide) (by decide) (by decide)).trans g13
  have f10 : gprGet c2.σ 10 = some fd := (k2 10 (by decide) (by decide) (by decide)).trans g10
  have m2 : c2.σ.mem = c1.σ.mem := by rw [p2.memory]; rfl
  have slotRead : read8 c2.σ.mem (fdSlot fd).toNat = read8 c.σ.mem (fdSlot fd).toNat := by
    rw [m2, m1]
    have ap := apart
    simp only [OutLRange] at ap
    have ap1 := ap.1
    exact ConsoleWrite.read8_same fun i hi => by
      rw [writeLog_out _ _ _ (show OutL [((sp - 32#64 + 24#64).toNat, 8, ra)] ((fdSlot fd).toNat + i) by
        simp only [OutL]; exact ⟨by omega, trivial⟩)]
  -- the slot's kind: neither free nor a file
  apply summary_bind (Close.kind_fast c2 (regsAt c2) l2
    (by simp only [Close.kind_input, GHolds, regsAt_of f10, regsAt_of f13]; exact ⟨f10, f13, trivial⟩)
    (by rw [regsAt_of f13]; exact kindR)
    (by simp only [Close.kind_loads, List.getD_cons_zero, regsAt_of f13, guardB]
        rw [show 2147896728#64 + (fd <<< 1 + fd) <<< 3 = fdSlot fd from rfl, slotRead]; simpa using live))
    (fun _ p => p.pc)
  intro c3 p3
  have o3 := p3.regs
  simp only [Close.kind_regs, Close.kind_loads, regsAt_of f10, regsAt_of f13, GHolds, List.getD_cons_zero] at o3
  obtain ⟨g11, -, g12, g15, h10, h13, -⟩ := o3
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [11, 12, 14, 15]) : gprGet c3.σ n = gprGet c2.σ n :=
    p3.gpr_frame (by decide) n lo hi out
  have e1c3 : gprGet c3.σ 1 = some ra :=
    (k3 1 (by decide) (by decide) (by decide)).trans ((k2 1 (by decide) (by decide) (by decide)).trans g1)
  have l3 : LeafInput (regsAt c3 1) c3 := by
    rw [regsAt_of e1c3]; exact ⟨p3.good, p3.image, p3.minstret, e1c3, h.aligned, p3.tick⟩
  have kindVal : bytesVal .lw (read8 c2.σ.mem (2147896728#64 + (fd <<< 1 + fd) <<< 3).toNat) =
      bytesVal .lw (read8 c.σ.mem (fdSlot fd).toNat) := by
    rw [show 2147896728#64 + (fd <<< 1 + fd) <<< 3 = fdSlot fd from rfl, slotRead]
  rw [kindVal] at g11
  -- not a file
  apply summary_bind (Close.file_fast c3 (regsAt c3) l3
    (by simp only [Close.file_input, GHolds, regsAt_of h10, regsAt_of g11]; exact ⟨h10, g11, trivial⟩)
    (by rw [regsAt_of g11]; simp only [guardB]; simpa using notFile)) (fun _ p => p.pc)
  intro c4 p4
  have k4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10]) : gprGet c4.σ n = gprGet c3.σ n :=
    p4.gpr_frame (by decide) n lo hi out
  have o4 := p4.regs
  simp only [Close.file_regs, GHolds] at o4
  obtain ⟨i10, -⟩ := o4
  have i12 : gprGet c4.σ 12 = some 2147896728#64 := (k4 12 (by decide) (by decide) (by decide)).trans g12
  have i13 : gprGet c4.σ 13 = some fd := (k4 13 (by decide) (by decide) (by decide)).trans h13
  have i15 : gprGet c4.σ 15 = some (fd <<< 1) := (k4 15 (by decide) (by decide) (by decide)).trans g15
  have e1c4 : gprGet c4.σ 1 = some ra := (k4 1 (by decide) (by decide) (by decide)).trans e1c3
  have l4 : LeafInput (regsAt c4 1) c4 := by
    rw [regsAt_of e1c4]; exact ⟨p4.good, p4.image, p4.minstret, e1c4, h.aligned, p4.tick⟩
  -- clear the kind, return 0
  apply summary_bind (Close.clear_fast c4 (regsAt c4) l4
    (by simp only [Close.clear_input, GHolds, regsAt_of i10, regsAt_of i12, regsAt_of i13, regsAt_of i15]
        exact ⟨i10, i12, i13, i15, trivial⟩)
    (by rw [regsAt_of i12, regsAt_of i13, regsAt_of i15]; exact kindW)
    (by simp only [Close.clearLog, regsAt_of i12, regsAt_of i13, regsAt_of i15]; exact outKind)) (fun _ p => p.pc)
  intro c5 p5
  have k5 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 12, 15]) : gprGet c5.σ n = gprGet c4.σ n :=
    p5.gpr_frame (by decide) n lo hi out
  have o5 := p5.regs
  simp only [Close.clear_regs, GHolds] at o5
  obtain ⟨j10, -⟩ := o5
  have m5 : c5.σ.mem = writeLog c.σ.mem (closeLog sp ra fd) := by
    rw [p5.memory, p4.memory, Named.NamedValue.wl_nil, p3.memory, Named.NamedValue.wl_nil, m2, m1, closeLog,
      show ([((sp - 32#64 + 24#64).toNat, 8, ra), ((fdSlot fd).toNat, 4, 0#64)] : List WEntry) =
        [((sp - 32#64 + 24#64).toNat, 8, ra)] ++ [((fdSlot fd).toNat, 4, 0#64)] from rfl, writeLog_append]
    simp only [Close.clearLog, regsAt_of i12, regsAt_of i13, regsAt_of i15]
    rfl
  have j2 : gprGet c5.σ 2 = some (sp + 18446744073709551584#64) :=
    (k5 2 (by decide) (by decide) (by decide)).trans ((k4 2 (by decide) (by decide) (by decide)).trans
      ((k3 2 (by decide) (by decide) (by decide)).trans ((k2 2 (by decide) (by decide) (by decide)).trans g2)))
  have e1c5 : gprGet c5.σ 1 = some ra := (k5 1 (by decide) (by decide) (by decide)).trans e1c4
  have l5 : LeafInput (regsAt c5 1) c5 := by
    rw [regsAt_of e1c5]; exact ⟨p5.good, p5.image, p5.minstret, e1c5, h.aligned, p5.tick⟩
  have saved : bytesVal .ld (read8 c5.σ.mem (sp + 18446744073709551584#64 + 24#64).toNat) = ra := by
    have ap := apart
    simp only [OutLRange] at ap
    have ap1 := ap.1
    rw [read8_value, m5, spE]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl (by simp only [closeLog, List.drop, OutLRange]; exact ⟨by omega, trivial⟩)
  apply (Close.leave_fast c5 ra (regsAt c5) l5
    (by simp only [Close.leave_input, GHolds, regsAt_of j2, regsAt_of j10]; exact ⟨j2, j10, trivial⟩)
    (by rw [regsAt_of j2]; exact slotW.read) (by rw [regsAt_of j2]; exact saved) h.aligned).weaken (fun _ e => e)
  intro d p6
  have e := ((((p1.toEffectPost.trans p2.toEffectPost).trans p3.toEffectPost).trans p4.toEffectPost).trans
    p5.toEffectPost).trans p6.toEffectPost
  have o6 := p6.regs
  simp only [Close.leave_regs, regsAt_of j2, GHolds] at o6
  have eff : WritePost [2, 13, 15, 15, 11, 12, 14, 15, 10, 10, 12, 15, 1, 2] (closeLog sp ra fd) c ra 0#64 d :=
    { e with
      result := by have := p6.result; simp only [regsAt_of j10] at this ⊢; exact this
      memory := by rw [p6.memory, Named.NamedValue.wl_nil, m5] }
  have spBack : gprGet d.σ 2 = some sp := by rw [o6.1, BitVec.add_assoc]; simp
  have raBack : gprGet d.σ 1 = some ra := by
    rw [o6.2.1]; simp only [Close.leave_loads, List.getD_cons_zero, regsAt_of j2]; rw [saved]
  exact ⟨eff, spBack, raBack, trivial⟩

/-- A native frame's callee frame, `front` bytes down. -/
theorem frame_callee {sp : BitVec 64} {front size : Nat} (frame : NativeFrame sp (front + size)) (fa : front % 16 = 0)
    (lit : BitVec 64) (e : -BitVec.ofNat 64 front = lit) : NativeFrame (sp + lit) size := by
  have n := frame.nested fa
  unfold OCaml.Vm.Boot.Startup.nativeStack at n
  rwa [e] at n

/-- `_close_r`'s stores (`s0`, `errno`, `ra`), then `_close`'s. -/
def scloseLog (sp ra s0 fd : BitVec 64) : List WEntry :=
  [((sp - 16#64).toNat, 8, s0), ((0x80064d48#64).toNat, 4, 0#64), ((sp - 16#64 + 8#64).toNat, 8, ra)] ++
    closeLog (sp + 18446744073709551600#64) 0x800421a8#64 fd

/-- The low words `_close` reads: `fs_ready` and the descriptor's slot. -/
structure FdLive (m : Std.ExtHashMap Nat (BitVec 8)) (fd : BitVec 64) : Prop where
  small : fd.toNat < 32
  ready : bytesVal .lw (read8 m (0x80064918#64).toNat) ≠ 0#64
  live : bytesVal .lw (read8 m (fdSlot fd).toNat) ≠ 0#64
  notFile : bytesVal .lw (read8 m (fdSlot fd).toNat) ≠ 4#64

/-- **`__sclose(reent, fp)` on a console stream**: `_close_r(reent, fp->_file)`
clears `errno` and closes the descriptor; `0` returned. -/
theorem sclose_console {ra sp s0 reent fp : BitVec 64} {c : Config} (h : LeafInput ra c)
    (sp0 : gprGet c.σ 2 = some sp) (s0r : gprGet c.σ 8 = some s0) (a0 : gprGet c.σ 10 = some reent)
    (a1 : gprGet c.σ 11 = some fp) (frame : NativeFrame sp 48) (fileR : ReadWindow (fp + 18#64) 2)
    (fdOk : FdLive c.σ.mem (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) :
    FnSummary 0x80040184#64 (fun d => d = c)
      (WriteRegistersPost ([11] ++ [2, 8, 10, 15] ++ [1] ++ [2, 13, 15, 15, 11, 12, 14, 15, 10, 10, 12, 15, 1, 2] ++
        [15] ++ [1, 2, 8]) (scloseLog sp ra s0 (bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat))) c ra 0#64
        [(2, sp), (8, s0)]) := by
  generalize hfd : bytesVal .lh (read8 c.σ.mem (fp + 18#64).toNat) = fd at fdOk ⊢
  have r1 := regsAt_of h.raReg
  have r2 := regsAt_of sp0
  have r8 := regsAt_of s0r
  have r10 := regsAt_of a0
  have r11 := regsAt_of a1
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h
  have sp16 : sp + 18446744073709551600#64 = sp - 16#64 := by rw [BitVec.sub_eq_add_neg]; rfl
  have lo := frame.lower
  have hiS := frame.upper
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo hiS
  have n0 : (sp - 16#64).toNat = sp.toNat - 16 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have n8 : (sp - 16#64 + 8#64).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_add, n0, BitVec.toNat_ofNat]; omega
  have fdNat := fdSlot_toNat fdOk.small
  -- `__sclose`: the descriptor, then `j _close_r`
  apply summary_bind (Sclose.enter_fast c (regsAt c) l0
    (by simp only [Sclose.enter_input, GHolds, r10, r11]; exact ⟨a0, a1, trivial⟩)
    (by rw [r11]; exact fileR)) (fun _ p => p.pc)
  intro c1 p1
  have o1 := p1.regs
  simp only [Sclose.enter_regs, Sclose.enter_loads, r11, r10, GHolds, List.getD_cons_zero, hfd] at o1
  obtain ⟨f11, f10, -⟩ := o1
  have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [11]) : gprGet c1.σ n = gprGet c.σ n :=
    p1.gpr_frame (by decide) n lo hi out
  have m1 : c1.σ.mem = c.σ.mem := by rw [p1.memory]; rfl
  have e1 : gprGet c1.σ 1 = some ra := (k1 1 (by decide) (by decide) (by decide)).trans h.raReg
  have e2 : gprGet c1.σ 2 = some sp := (k1 2 (by decide) (by decide) (by decide)).trans sp0
  have e8 : gprGet c1.σ 8 = some s0 := (k1 8 (by decide) (by decide) (by decide)).trans s0r
  have l1 : LeafInput (regsAt c1 1) c1 := by
    rw [regsAt_of e1]; exact ⟨p1.good, p1.image, p1.minstret, e1, h.aligned, p1.tick⟩
  -- `_close_r`: save `s0`, `ra`; `errno = 0`; call `_close(fd)`
  have prolog : CloseR.proLog (regsAt c1) (CloseR.pro_loads c1.σ.mem (regsAt c1)) =
      [((sp - 16#64).toNat, 8, s0), ((0x80064d48#64).toNat, 4, 0#64), ((sp - 16#64 + 8#64).toNat, 8, ra)] := by
    simp only [CloseR.proLog, regsAt_of e1, regsAt_of e2, regsAt_of e8]
  apply summary_bind (CloseR.pro_fast c1 (regsAt c1) l1
    (by simp only [CloseR.pro_input, GHolds, regsAt_of e1, regsAt_of e2, regsAt_of e8, regsAt_of f10, regsAt_of f11]
        exact ⟨e1, e2, e8, f10, f11, trivial⟩)
    (by rw [regsAt_of e2, sp16]
        have w := frame_word (k := 16) (off := 0) frame (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at w)
    (by rw [regsAt_of e2, sp16]; exact frame_word (k := 16) (off := 8) frame (by decide) (by decide) (by decide) (by decide))
    (by
      rw [prolog]
      refine ⟨⟨Or.inl (by rw [n0]; simp only [Image.textBase, Image.textSize]; omega), Or.inl (by decide),
        Or.inl (by rw [n8]; simp only [Image.textBase, Image.textSize]; omega), trivial⟩,
        ⟨Or.inl (by rw [n0]; simp only [Image.rodataBase, Image.rodataSize]; omega), Or.inl (by decide),
        Or.inl (by rw [n8]; simp only [Image.rodataBase, Image.rodataSize]; omega), trivial⟩⟩)) (fun _ p => p.pc)
  intro c2 p2
  have o2 := p2.regs
  simp only [CloseR.pro_regs, regsAt_of e1, regsAt_of e2, regsAt_of e8, regsAt_of f10,
    regsAt_of f11, GHolds] at o2
  obtain ⟨-, g10, -, g2, -, -⟩ := o2
  have m2 : c2.σ.mem = writeLog c.σ.mem
      [((sp - 16#64).toNat, 8, s0), ((0x80064d48#64).toNat, 4, 0#64), ((sp - 16#64 + 8#64).toNat, 8, ra)] := by
    rw [p2.memory, prolog, m1]
  -- the words `_close` reads survive the prologue's stores
  have lowSame (a : Nat) (ha : a + 8 ≤ 0x80064d48 ∨ 0x80064d48 + 4 ≤ a) (hb : a + 8 ≤ sp.toNat - 16) :
      read8 c2.σ.mem a = read8 c.σ.mem a := by
    rw [m2]
    exact ConsoleWrite.read8_same fun i hi => by
      rw [writeLog_out _ _ _ (show OutL [((sp - 16#64).toNat, 8, s0), ((0x80064d48#64).toNat, 4, 0#64),
          ((sp - 16#64 + 8#64).toNat, 8, ra)] (a + i) by
        simp only [OutL, n0, n8]; exact ⟨by omega, by simp only [BitVec.toNat_ofNat]; omega, by omega, trivial⟩)]
  have readyAt : read8 c2.σ.mem (0x80064918#64).toNat = read8 c.σ.mem (0x80064918#64).toNat :=
    lowSame _ (Or.inl (by decide)) (by simp only [BitVec.toNat_ofNat]; omega)
  have slotAt : read8 c2.σ.mem (fdSlot fd).toNat = read8 c.σ.mem (fdSlot fd).toNat :=
    lowSame _ (Or.inr (by rw [fdNat]; omega)) (by have sm := fdOk.small; rw [fdNat]; omega)
  apply summary_bind (call_registers_summary CloseR.pro_call_shape CloseR.pro_call_decode c2
    (CloseR.pro_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(10, fd), (2, sp + 18446744073709551600#64)] ⟨g10, g2, trivial⟩
    (by change KeysOK [10, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl) (fun _ q => q.pc)
  intro c3 q3
  have m3 : c3.σ.mem = c2.σ.mem := q3.memory
  have leaf3 : LeafInput 0x800421a8#64 c3 :=
    ⟨q3.good, q3.image, q3.minstret, gholds_lookup (n := 1) _ q3.regs rfl, by decide, q3.tick⟩
  -- `_close(fd)`
  have frame' : NativeFrame (sp + 18446744073709551600#64) 32 :=
    frame_callee (front := 16) (size := 32) frame (by decide) _ (by decide)
  apply summary_bind (close_console leaf3 (gholds_lookup (n := 2) _ q3.regs rfl)
    (gholds_lookup (n := 10) _ q3.regs rfl) frame'
    (by rw [m3, readyAt]; exact fdOk.ready) fdOk.small (by rw [m3, slotAt]; exact fdOk.live)
    (by rw [m3, slotAt]; exact fdOk.notFile)) (fun _ p => p.pc)
  intro c4 p4
  have c4a0 : gprGet c4.σ 10 = some 0#64 := p4.result
  have c4sp : gprGet c4.σ 2 = some (sp + 18446744073709551600#64) := gholds_lookup (n := 2) _ p4.regs rfl
  have k4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [2, 13, 15, 15, 11, 12, 14, 15, 10, 10, 12, 15, 1, 2]) :
      gprGet c4.σ n = gprGet c3.σ n := p4.gpr_frame (by decide) n lo hi out
  have c4ra : gprGet c4.σ 1 = some 0x800421a8#64 := gholds_lookup (n := 1) _ p4.regs rfl
  have l4 : LeafInput (regsAt c4 1) c4 := by
    rw [regsAt_of c4ra]; exact ⟨p4.good, p4.image, p4.minstret, c4ra, by decide, p4.tick⟩
  have m4 : c4.σ.mem = writeLog c.σ.mem (scloseLog sp ra s0 fd) := by
    rw [p4.memory, m3, m2, scloseLog, writeLog_append]
  -- `_close` returned 0, not -1
  apply summary_bind (CloseR.back_fast c4 (regsAt c4) l4
    (by simp only [CloseR.back_input, GHolds, regsAt_of c4a0]; exact ⟨c4a0, trivial⟩)
    (by rw [regsAt_of c4a0]; decide)) (fun _ p => p.pc)
  intro c5 p5
  have k5 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15]) : gprGet c5.σ n = gprGet c4.σ n :=
    p5.gpr_frame (by decide) n lo hi out
  have c5sp := (k5 2 (by decide) (by decide) (by decide)).trans c4sp
  have c5a0 := (k5 10 (by decide) (by decide) (by decide)).trans c4a0
  have c5ra := (k5 1 (by decide) (by decide) (by decide)).trans c4ra
  have l5 : LeafInput (regsAt c5 1) c5 := by
    rw [regsAt_of c5ra]; exact ⟨p5.good, p5.image, p5.minstret, c5ra, by decide, p5.tick⟩
  have m5 : c5.σ.mem = writeLog c.σ.mem (scloseLog sp ra s0 fd) := by rw [p5.memory, Named.NamedValue.wl_nil, m4]
  have closeAt : ((sp + 18446744073709551600#64) - 32#64 + 24#64).toNat = sp.toNat - 24 := by
    rw [sp16, BitVec.toNat_add, BitVec.toNat_sub, n0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have sm := fdOk.small
  have savedRa : bytesVal .ld (read8 c5.σ.mem (sp + 18446744073709551600#64 + 8#64).toNat) = ra := by
    rw [read8_value, m5, sp16]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 2 _ _ rfl (by
      simp only [scloseLog, closeLog, List.drop, List.cons_append, List.nil_append, OutLRange, closeAt, fdNat, n8]
      exact ⟨Or.inr (by omega), Or.inr (by omega), trivial⟩)
  have savedS0 : bytesVal .ld (read8 c5.σ.mem (sp + 18446744073709551600#64).toNat) = s0 := by
    rw [read8_value, m5, sp16]
    exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [scloseLog, closeLog, List.drop, List.cons_append, List.nil_append, OutLRange, closeAt, fdNat, n8, n0,
        BitVec.toNat_ofNat]
      exact ⟨Or.inr (by omega), Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩)
  -- restore `s0` and `ra`, return
  apply (CloseR.leave_fast c5 ra (regsAt c5) l5
    (by simp only [CloseR.leave_input, GHolds, regsAt_of c5sp, regsAt_of c5a0]; exact ⟨c5sp, c5a0, trivial⟩)
    (by rw [regsAt_of c5sp, sp16]; exact (frame_word (k := 16) (off := 8) frame (by decide) (by decide) (by decide)
      (by decide)).read)
    (by rw [regsAt_of c5sp, sp16]
        have w := frame_word (k := 16) (off := 0) frame (by decide) (by decide) (by decide) (by decide)
        rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at w
        exact w.read)
    (by rw [regsAt_of c5sp]; exact savedRa) h.aligned).weaken (fun _ e => e)
  intro d p6
  have o6 := p6.regs
  simp only [CloseR.leave_regs, CloseR.leave_loads, regsAt_of c5sp, regsAt_of c5a0, GHolds, List.getD_cons_zero,
    List.getD_cons_succ] at o6
  have e := ((((p1.toEffectPost.trans p2.toEffectPost).trans q3.toEffectPost).trans p4.toEffectPost).trans
    p5.toEffectPost).trans p6.toEffectPost
  have eff : WritePost ([11] ++ [2, 8, 10, 15] ++ [1] ++ [2, 13, 15, 15, 11, 12, 14, 15, 10, 10, 12, 15, 1, 2] ++
      [15] ++ [1, 2, 8]) (scloseLog sp ra s0 fd) c ra 0#64 d :=
    { e with
      result := by have := p6.result; rw [regsAt_of c5a0] at this; exact this
      memory := by rw [p6.memory, Named.NamedValue.wl_nil, m5] }
  have spBack : gprGet d.σ 2 = some sp := by rw [o6.1, BitVec.add_assoc]; simp
  have s0Back : gprGet d.σ 8 = some s0 := by rw [o6.2.1, savedS0]
  exact ⟨eff, spBack, s0Back, trivial⟩

end OCaml.Vm.Primitives.Uncaught.StdioClose
