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
      output := by
        have o3 := p3.output
        rw [o3]
        simp only [Vsa.Machine.output] at m ⊢
        rw [p2.output, p1.output]
        exact m.output }

end OCaml.Vm.Primitives.Uncaught.FormatException
