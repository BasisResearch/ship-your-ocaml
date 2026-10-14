import OCaml.Vm.Primitives.Uncaught.FormatCopy

/-!
# `caml_format_exception` on a constant exception: the buffer filled

`memmove(data, name, len)` (`memmove_leaf`), `buf.ptr = data + len`, the
terminator, and the call `caml_stat_alloc_noexc(len + 1)`. `FilledMem`
describes the memory at that call: the buffer holds the name and its
terminator, `buf.ptr` the end, and every other byte is as the prologue left it.
-/

namespace OCaml.Vm.Primitives.Uncaught.FormatException
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gpr_some gpr_some_of NameAt gprReg_ne_htif)

/-- The callee-saved registers `caml_format_exception` never writes (s3, s6–s11). -/
abbrev formatCallee : List Nat := [19, 22, 23, 24, 25, 26, 27]

/-- The buffer's first byte, as a natural. -/
abbrev dataNat (sp : BitVec 64) : Nat := sp.toNat - 336

/-- **The memory at `caml_stat_alloc_noexc`**: the name and its terminator in
the buffer, `buf.ptr` at the end, everything else as after the prologue. -/
structure FilledMem (m prologue : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) (name : List (BitVec 8)) : Prop where
  buffer : ∀ i (hi : i < name.length), (m[dataNat sp + i]?).getD 0 = name[i]
  term : (m[dataNat sp + name.length]?).getD 0 = 0#8
  ptr : bytesT m (sp.toNat - 352) 8 = bufData sp + BitVec.ofNat 64 name.length
  rest : ∀ x, (x < dataNat sp ∨ dataNat sp + name.length < x) → (x < sp.toNat - 352 ∨ sp.toNat - 344 ≤ x) →
    (m[x]?).getD 0 = (prologue[x]?).getD 0

/-- At `caml_stat_alloc_noexc(len + 1)`, the buffer filled. -/
structure Filled (c0 : Config) (sp : BitVec 64) (name : List (BitVec 8)) (base c : Config) : Prop where
  leaf : LeafInput 0x8000ddd8#64 c
  ready : LibraryReady c
  pc : PCAt 0x8000ab2c#64 c
  size : gprGet c.σ 10 = some (BitVec.ofNat 64 (name.length + 1))
  sizeSaved : gprGet c.σ 8 = some (BitVec.ofNat 64 (name.length + 1))
  data : gprGet c.σ 20 = some (bufData sp)
  stack : gprGet c.σ 2 = some (sp + 18446744073709551184#64)
  memory : FilledMem c.σ.mem base.σ.mem sp name
  callee : ∀ k ∈ formatCallee, gprGet c.σ k = gprGet base.σ k
  output : Vsa.Machine.output c.σ = Vsa.Machine.output base.σ

theorem stdioFoot_high {a : Nat} (h : VsaIris.Stdio.stdioFoot a) : a < Layout.sym_bss_end := by
  simp only [VsaIris.Stdio.stdioFoot, VsaIris.Stdio.InRange, Layout.sym_bss_end] at h ⊢
  omega

theorem data_eq {sp : BitVec 64} (frame : NativeFrame sp 432) : bufData sp = BitVec.ofNat 64 (dataNat sp) := by
  apply BitVec.eq_of_toNat_eq
  rw [frame_ptr frame 336 (by decide) (by decide), BitVec.toNat_ofNat]
  have := frame.upper; simp only [Layout.sym_stack_top, dataNat] at this ⊢
  omega

/-- After the copy into the buffer: back at `buf.ptr = data + len`. -/
structure Copied (c0 : Config) (sp np : BitVec 64) (name : List (BitVec 8)) (base c : Config) : Prop where
  leaf : LeafInput 0x8000ddbc#64 c
  ready : LibraryReady c
  pc : PCAt 0x8000ddbc#64 c
  cursor : gprGet c.σ 8 = some (bufData sp + BitVec.ofNat 64 name.length)
  data : gprGet c.σ 20 = some (bufData sp)
  stack : gprGet c.σ 2 = some (sp + 18446744073709551184#64)
  buffer : ∀ i (hi : i < name.length), (c.σ.mem[dataNat sp + i]?).getD 0 = name[i]
  rest : ∀ x, (x < dataNat sp ∨ dataNat sp + name.length ≤ x) → (c.σ.mem[x]?).getD 0 = (base.σ.mem[x]?).getD 0
  callee : ∀ k ∈ formatCallee, gprGet c.σ k = gprGet base.σ k
  output : Vsa.Machine.output c.σ = Vsa.Machine.output base.σ

/-- **`memmove(data, name, len)`.** -/
theorem format_copy {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c0 c d : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c0) (p : ProDone c0 ra sp exn np s0 s1 s2 s4 s5 c)
    (m : Measured c sp np s0 name.length d) :
    ∃ e, Steps d e ∧ Copied c0 sp np name c e := by
  have l0 : LeafInput (regsAt d 1) d := by rw [regsAt_of m.leaf.raReg]; exact m.leaf
  obtain ⟨e1, run1, p1⟩ := (copy_fast d (regsAt d) l0 (by
      simp only [copy_input, GHolds, regsAt_of m.leaf.raReg, regsAt_of m.length, regsAt_of m.data, regsAt_of m.name]
      exact ⟨m.leaf.raReg, m.length, m.data, m.name, trivial⟩)).run d ⟨m.pc, rfl⟩
  have o1 := p1.regs
  simp only [copy_regs, regsAt_of m.length, regsAt_of m.data, regsAt_of m.name, GHolds] at o1
  obtain ⟨a10, a11, a12, -, -, -, -⟩ := o1
  have k1 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 11, 12] → gprGet e1.σ n = gprGet d.σ n :=
    fun n lo hi out => p1.gpr_frame (by decide) n lo hi out
  have c8 := (k1 8 (by decide) (by decide) (by decide)).trans m.cursor
  have c20 := (k1 20 (by decide) (by decide) (by decide)).trans m.data
  have c2' := (k1 2 (by decide) (by decide) (by decide)).trans m.stack
  obtain ⟨e2, run2, p2⟩ := (call_registers_summary copy_call_shape copy_call_decode e1 (copy_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret
    [(10, bufData sp), (11, np), (12, BitVec.ofNat 64 name.length), (8, bufData sp + BitVec.ofNat 64 name.length),
     (20, bufData sp), (2, sp + 18446744073709551184#64)]
    ⟨a10, a11, a12, c8, c20, c2', trivial⟩ (by change KeysOK [10, 11, 12, 8, 20, 2]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl).run e1 ⟨p1.pc, rfl⟩
  have ready2 := (m.ready.carry p1.kept (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p2.kept
    (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
  have leaf2 : LeafInput 0x8000ddbc#64 e2 :=
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
  have npLo := h.nameLow
  have npHi := h.nameHigh
  have lo := h.frame.lower
  have up := h.frame.upper
  have fitsLen := h.fits
  simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at npLo npHi lo up
  obtain ⟨e3, run3, p3⟩ := (memmove_leaf (d := dataNat sp) (src := np.toNat) (len := name.length) e2 leaf2 ready2
    ⟨by unfold dataNat; omega, ⟨Nat.le_refl _, Nat.le_refl _⟩, by unfold dataNat; omega, by omega, by omega,
      Or.inr (by omega), Or.inl (by unfold dataNat; omega)⟩
    (fun a lo' hi' foot => by have := stdioFoot_high foot; simp only [Layout.sym_bss_end] at this; omega)
    (by rw [← data_eq h.frame]; exact gholds_lookup (n := 10) _ p2.regs rfl)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gholds_lookup (n := 11) _ p2.regs rfl)
    (gholds_lookup (n := 12) _ p2.regs rfl)).run e2
    ⟨by have := p2.pc; rw [copy_call_target] at this; exact this, rfl⟩
  have k3 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ memmoveScratch → n ∉ [10] → gprGet e3.σ n = gprGet e2.σ n := p3.registers
  have m2 : ∀ x : Nat, (e2.σ.mem[x]?).getD (0 : BitVec 8) = (c.σ.mem[x]?).getD 0 := fun x => by
    rw [p2.memory, p1.memory, wl_nil]; simpa only [Std.ExtHashMap.get?_eq_getElem?] using m.memory x
  refine ⟨e3, run1.trans (run2.trans run3), ?_⟩
  exact
    { leaf := p3.toLeafInput
      ready := ⟨p3.libraryGood.gpr, (k3 3 (by decide) (by decide) (by decide) (by decide)).trans ready2.gp,
        p3.libraryGood.htifIdle⟩
      pc := p3.pc
      cursor := (k3 8 (by decide) (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ p2.regs rfl)
      data := (k3 20 (by decide) (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 20) _ p2.regs rfl)
      stack := (k3 2 (by decide) (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ p2.regs rfl)
      buffer := fun i hi => by
        have cp := p3.copied i hi
        rw [byte_total, byte_total] at cp
        rw [cp, m2, p.memory, writeLog_out _ _ _ (outL_of_range (arena_out h.frame (a := np.toNat) (n := name.length + 1)
          (by have := h.nameHigh; omega)) (by omega) (by omega)), ← h.named.byte_nat h.nameHigh (by omega)]
        exact h.named.bytes i hi
      rest := fun x out => by
        have kp := p3.kept x out
        rw [byte_total, byte_total] at kp
        rw [kp, m2]
      callee := fun k hk => by
        simp only [formatCallee, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact (k3 _ (by decide) (by decide) (by decide) (by decide)).trans
            ((p2.gpr_frame (by decide) _ (by decide) (by decide) (by decide)).trans
              ((k1 _ (by decide) (by decide) (by decide)).trans (m.frame _ (by decide) (by decide) (by decide))))
      output := by
        have o3 := p3.output
        rw [o3]
        simp only [Vsa.Machine.output] at m ⊢
        rw [p2.output, p1.output]
        exact m.output }

/-- A zero byte store reads back as zero. -/
theorem getD_writeLog_zero_byte (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    ((writeLog m [(a, 1, 0#64)])[a]?).getD 0 = 0#8 := by
  simp only [writeLog, List.foldl_cons, List.foldl_nil, applyW, Std.ExtHashMap.getElem?_insert_self,
    Option.getD_some]
  rfl

/-- A byte in the frame is a writable byte. -/
theorem frame_byte {sp : BitVec 64} (frame : NativeFrame sp 432) {k : Nat} (hk : k < 432) :
    WriteWindow (BitVec.ofNat 64 (nativeFrameBase sp 432 + k)) 1 := by
  have lower := frame.lower
  have upper := frame.upper
  constructor <;> rw [frame.slot_nat (by omega)]
  all_goals simp only [nativeFrameBase, Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top, Layout.sym_tohost] at *
  all_goals omega

/-- **`buf.ptr = data + len`, the terminator, and the call
`caml_stat_alloc_noexc(len + 1)`.** -/
theorem format_terminate {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c0 c e : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c0) (cp : Copied c0 sp np name c e) :
    ∃ f, Steps e f ∧ Filled c0 sp name c f := by
  have r2 := regsAt_of cp.stack
  have r8 := regsAt_of cp.cursor
  have r20 := regsAt_of cp.data
  have a10 := gpr_some (cp.ready.gprs 10 (by decide) (by decide))
  have l0 : LeafInput (regsAt e 1) e := by rw [regsAt_of cp.leaf.raReg]; exact cp.leaf
  have slot80 : sp + 18446744073709551184#64 + 80#64 = BitVec.ofNat 64 (nativeFrameBase sp 432 + 80) :=
    frame_slot h.frame 80 (by decide)
  have t80 : (sp + 18446744073709551184#64 + 80#64).toNat = sp.toNat - 352 := by
    rw [slot80, h.frame.slot_nat (by decide)]; unfold nativeFrameBase; have := h.frame.lower
    simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  have recLog : recordLog (regsAt e) (record_loads e.σ.mem (regsAt e)) =
      [((sp + 18446744073709551184#64 + 80#64).toNat, 8, bufData sp + BitVec.ofNat 64 name.length)] := by
    simp only [recordLog, r2, r8]
  obtain ⟨e1, run1, p1⟩ := (record_fast e (regsAt e) l0 (by
      simp only [record_input, GHolds, r2, r8]; exact ⟨cp.stack, cp.cursor, a10, trivial⟩)
    (by rw [r2, slot80]; exact h.frame.word (by decide) (by decide))
    (by rw [recLog, slot80]; exact h.frame.image_outside (by
      simp only [LogInW, InsideW]; rw [h.frame.slot_nat (by decide)]
      have := h.frame.lower; unfold nativeFrameBase
      simp only [Vsa.Sim.DlHeap.heapEnd] at this
      exact ⟨Or.inl ⟨by omega, by omega⟩, trivial⟩))).run e ⟨cp.pc, rfl⟩
  have k1 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet e1.σ n = gprGet e.σ n :=
    fun n lo hi => p1.gpr_frame (by decide) n lo hi (by simp)
  have e1_1 := (k1 1 (by decide) (by decide)).trans cp.leaf.raReg
  have e1_2 := (k1 2 (by decide) (by decide)).trans cp.stack
  have e1_8 := (k1 8 (by decide) (by decide)).trans cp.cursor
  have e1_20 := (k1 20 (by decide) (by decide)).trans cp.data
  have e1_10 := (k1 10 (by decide) (by decide)).trans a10
  have l1 : LeafInput (regsAt e1 1) e1 := by
    rw [regsAt_of e1_1]; exact ⟨p1.good, p1.image, p1.minstret, e1_1, by decide, p1.tick⟩
  have lo := h.frame.lower
  have up := h.frame.upper
  have fitsLen := h.fits
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at lo up
  have endAddr : bufData sp + BitVec.ofNat 64 name.length = BitVec.ofNat 64 (nativeFrameBase sp 432 + (96 + name.length)) := by
    apply BitVec.eq_of_toNat_eq
    rw [data_eq h.frame, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h.frame.slot_nat (by omega)]
    unfold dataNat nativeFrameBase; omega
  have tEnd : (bufData sp + BitVec.ofNat 64 name.length).toNat = dataNat sp + name.length := by
    rw [endAddr, h.frame.slot_nat (by omega)]; unfold dataNat nativeFrameBase; omega
  have m1 : e1.σ.mem = writeLog e.σ.mem [((sp + 18446744073709551184#64 + 80#64).toNat, 8,
      bufData sp + BitVec.ofNat 64 name.length)] := by rw [p1.memory, recLog]
  have word80 : bytesVal .ld (read8 e1.σ.mem (sp + 18446744073709551184#64 + 80#64).toNat) =
      bufData sp + BitVec.ofNat 64 name.length := by
    rw [read8_value, m1]; exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl trivial
  have termLog : terminateLog (regsAt e1) (terminate_loads e1.σ.mem (regsAt e1)) =
      [((bufData sp + BitVec.ofNat 64 name.length).toNat, 1, 0#64)] := by
    simp only [terminateLog, regsAt_of e1_8]
  obtain ⟨e2, run2, p2⟩ := (terminate_fast e1 (regsAt e1) l1 (by
      simp only [terminate_input, GHolds, regsAt_of e1_1, regsAt_of e1_2, regsAt_of e1_8, regsAt_of e1_20]
      exact ⟨e1_1, e1_2, e1_8, gpr_some (gpr_some_of e1_10), e1_20, trivial⟩)
    (by rw [regsAt_of e1_8, endAddr]; exact frame_byte h.frame (by omega))
    (by rw [regsAt_of e1_2, slot80]; exact (h.frame.word (by decide) (by decide)).read)
    (by
      rw [termLog, regsAt_of e1_2, t80, tEnd]
      simp only [List.take, OutLRange]; unfold dataNat; exact ⟨Or.inl (by omega), trivial⟩)
    (by rw [termLog, endAddr]; exact h.frame.image_outside (by
      simp only [LogInW, InsideW]; rw [h.frame.slot_nat (by omega)]
      unfold nativeFrameBase; exact ⟨Or.inl ⟨by omega, by omega⟩, trivial⟩))).run e1 ⟨p1.pc, rfl⟩
  have sizeEq : bufData sp + BitVec.ofNat 64 name.length + (-bufData sp + 1#64) = BitVec.ofNat 64 (name.length + 1) := by
    rw [BitVec.ofNat_add]; bv_omega
  have o2 := p2.regs
  simp only [terminate_regs, terminate_loads, List.getD_cons_zero, regsAt_of e1_2, regsAt_of e1_20, word80, sizeEq,
    GHolds] at o2
  obtain ⟨g10, g8, g1, g2, g20, -⟩ := o2
  obtain ⟨f, run3, p3⟩ := (call_registers_summary terminate_call_shape terminate_call_decode e2
    (terminate_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
    [(10, BitVec.ofNat 64 (name.length + 1)), (8, BitVec.ofNat 64 (name.length + 1)), (20, bufData sp),
     (2, sp + 18446744073709551184#64)]
    ⟨g10, g8, g20, g2, trivial⟩ (by change KeysOK [10, 8, 20, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run e2
    ⟨p2.pc, rfl⟩
  have mf : f.σ.mem = writeLog (writeLog e.σ.mem [((sp + 18446744073709551184#64 + 80#64).toNat, 8,
      bufData sp + BitVec.ofNat 64 name.length)]) [((bufData sp + BitVec.ofNat 64 name.length).toNat, 1, 0#64)] := by
    rw [p3.memory, p2.memory, termLog, m1]
  have mf' : f.σ.mem = writeLog (writeLog e.σ.mem [(sp.toNat - 352, 8, bufData sp + BitVec.ofNat 64 name.length)])
      [(dataNat sp + name.length, 1, 0#64)] := by rw [mf, tEnd, t80]
  refine ⟨f, run1.trans (run2.trans run3), ?_⟩
  exact
    { leaf := ⟨p3.good, p3.image, p3.minstret, gholds_lookup (n := 1) _ p3.regs rfl, by decide, p3.tick⟩
      ready := ((cp.ready.carry p1.kept (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p2.kept
        (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p3.kept
        (p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
      pc := by have := p3.pc; rw [terminate_call_target] at this; exact this
      size := gholds_lookup (n := 10) _ p3.regs rfl
      sizeSaved := gholds_lookup (n := 8) _ p3.regs rfl
      data := gholds_lookup (n := 20) _ p3.regs rfl
      stack := gholds_lookup (n := 2) _ p3.regs rfl
      memory :=
        { buffer := fun i hi => by
            have o1 : OutL [(dataNat sp + name.length, 1, 0#64)] (dataNat sp + i) := by
              simp only [OutL]; exact ⟨Or.inl (by omega), trivial⟩
            have o2 : OutL [(sp.toNat - 352, 8, bufData sp + BitVec.ofNat 64 name.length)] (dataNat sp + i) := by
              simp only [OutL]; unfold dataNat; exact ⟨Or.inr (by omega), trivial⟩
            rw [mf', writeLog_out _ _ _ o1, writeLog_out _ _ _ o2]
            exact cp.buffer i hi
          term := by rw [mf']; exact getD_writeLog_zero_byte _ _
          ptr := by
            have outP : OutLRange [(dataNat sp + name.length, 1, 0#64)] (sp.toNat - 352) 8 := by
              simp only [OutLRange]; unfold dataNat; exact ⟨Or.inl (by omega), trivial⟩
            rw [mf', OCaml.Vm.Primitives.bytesT_writeLog_out _ outP]
            exact OCaml.Vm.Sim.word_writeLog_at _ _ 0 _ _ rfl trivial
          rest := fun x out slot => by
            have o1 : OutL [(dataNat sp + name.length, 1, 0#64)] x := by
              simp only [OutL]; exact ⟨by omega, trivial⟩
            have o2 : OutL [(sp.toNat - 352, 8, bufData sp + BitVec.ofNat 64 name.length)] x := by
              refine ⟨?_, trivial⟩
              rcases slot with hs | hs
              · exact Or.inl hs
              · right; show sp.toNat - 352 + 8 ≤ x; omega
            rw [mf', writeLog_out _ _ _ o1, writeLog_out _ _ _ o2]
            exact cp.rest x (out.elim Or.inl (fun hx => Or.inr (Nat.le_of_lt hx))) }
      callee := fun k hk => by
        have mem := hk
        simp only [formatCallee, List.mem_cons, List.not_mem_nil, or_false] at mem
        have out (l : List Nat) (hl : l = [1] ∨ l = [8, 10]) : k ∉ l := fun hm => by
          rcases hl with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
        exact (p3.gpr_frame (by decide) k (by omega) (by omega) (out _ (.inl rfl))).trans
          ((p2.gpr_frame (by decide) k (by omega) (by omega) (out _ (.inr rfl))).trans
            ((k1 k (by omega) (by omega)).trans (cp.callee k hk)))
      output := by
        have o := cp.output
        simp only [Vsa.Machine.output] at o ⊢
        rw [p3.output, p2.output, p1.output]; exact o }

end OCaml.Vm.Primitives.Uncaught.FormatException
