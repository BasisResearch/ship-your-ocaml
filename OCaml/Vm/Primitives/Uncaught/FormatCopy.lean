import OCaml.Vm.Primitives.Uncaught.FormatFront

/-!
# `caml_format_exception` on a constant exception: the name into the buffer

After the prologue: `strlen(name)` (`strlen_ready`), the name fits the
255-byte buffer and is nonempty, `memmove(data, name, len)`
(`memmove_leaf`). Library calls need `LibraryReady`, carried from the entry
by `GprsKept` and the HTIF frame.
-/

namespace OCaml.Vm.Primitives.Uncaught.FormatException
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gpr_some gpr_some_of NameAt gprReg_ne_htif)

/-- `LibraryReady` along a run that keeps register presence, `gp` and the HTIF word. -/
theorem _root_.OCaml.Vm.Primitives.LibraryReady.carry {c d : Config} (r : LibraryReady c) (k : GprsKept c d)
    (idle : d.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes) :
    LibraryReady d :=
  ⟨fun n lo hi => k.present n lo hi (r.gprs n lo hi), k.gp.trans r.gp, idle.trans r.htifIdle⟩

/-- The name's byte `i`, at the natural address. -/
theorem _root_.OCaml.Vm.Primitives.Named.NamedValue.NameAt.byte_nat {m : Std.ExtHashMap Nat (BitVec 8)} {np : BitVec 64} {name : List (BitVec 8)}
    (h : NameAt m np name) (high : np.toNat + name.length + 8 ≤ Vsa.Sim.DlHeap.heapEnd) {i : Nat} (hi : i ≤ name.length) :
    (np + BitVec.ofNat 64 i).toNat = np.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Vsa.Sim.DlHeap.heapEnd] at high
  omega

/-- The buffer's `data` and `end` pointers. -/
abbrev bufData (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551280#64
abbrev bufEnd (sp : BitVec 64) : BitVec 64 := sp + 18446744073709551535#64

/-- The name measured and found to fit: at the copy block. -/
structure Measured (base : Config) (sp np s0 : BitVec 64) (len : Nat) (c : Config) : Prop where
  leaf : LeafInput 0x8000dd9c#64 c
  ready : LibraryReady c
  pc : PCAt 0x8000ddac#64 c
  length : gprGet c.σ 10 = some (BitVec.ofNat 64 len)
  cursor : gprGet c.σ 8 = some (bufData sp + BitVec.ofNat 64 len)
  data : gprGet c.σ 20 = some (bufData sp)
  name : gprGet c.σ 21 = some np
  stack : gprGet c.σ 2 = some (sp + 18446744073709551184#64)
  memory : Vsa.Densify.MemEqv c.σ.mem base.σ.mem
  output : Vsa.Machine.output c.σ = Vsa.Machine.output base.σ
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 8, 10, 11, 12, 13, 14, 15] → gprGet c.σ n = gprGet base.σ n
  htif : c.σ.regs.get? Register.htif_payload_writes = base.σ.regs.get? Register.htif_payload_writes

theorem frame_ptr {sp : BitVec 64} (frame : NativeFrame sp 432) (k : Nat) (hk : 0 < k) (bound : k ≤ 432) :
    (sp + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = sp.toNat - k := by
  have := frame.lower; have := frame.upper
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.sym_stack_top] at *
  omega

theorem bgeu_of_le {x y : BitVec 64} (h : y.toNat ≤ x.toNat) : guardB .BGEU x y = true := by
  simp [guardB, Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, h]

theorem bne_of_ne {x y : BitVec 64} (h : x ≠ y) : guardB .BNE x y = true := by
  simp [guardB, h]

theorem gpr_frame_of {c d : Config} {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {pc v : BitVec 64}
    (p : EffectPost writes mem c pc v d) (keys : KeysOK writes) (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31)
    (out : n ∉ writes) : gprGet d.σ n = gprGet c.σ n :=
  p.gpr_frame keys n lo hi out

/-- **`strlen(name)`, the fit and the nonempty test**, from the prologue. -/
theorem format_measure {ra sp exn np s0 s1 s2 s4 s5 : BitVec 64} {name : List (BitVec 8)} {c0 c : Config}
    (h : FormatInput ra sp exn np s0 s1 s2 s4 s5 name c0) (p : ProDone c0 ra sp exn np s0 s1 s2 s4 s5 c) :
    ∃ d, Steps c d ∧ Measured c sp np s0 name.length d := by
  have ready := h.ready.carry p.kept p.htif
  have l0 : LeafInput (regsAt c 1) c := by rw [regsAt_of p.leaf.raReg]; exact p.leaf
  obtain ⟨c1, run1, p1⟩ := (nameLen_fast c (regsAt c) l0 (by
      simp only [nameLen_input, GHolds, regsAt_of p.leaf.raReg, regsAt_of p.arg, regsAt_of p.name]
      exact ⟨p.leaf.raReg, p.arg, p.name, trivial⟩)).run c ⟨p.pc, rfl⟩
  have o1 := p1.regs
  simp only [nameLen_regs, regsAt_of p.name, regsAt_of p.leaf.raReg, GHolds] at o1
  obtain ⟨a1, -, -, -⟩ := o1
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary nameLen_call_shape nameLen_call_decode c1 (nameLen_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret [(10, np)] ⟨a1, trivial⟩ (by change KeysOK [10]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl).run c1 ⟨p1.pc, rfl⟩
  have m2 : c2.σ.mem = c.σ.mem := by rw [p2.memory, p1.memory, wl_nil]
  have ready2 := ready.carry (p1.kept.trans p2.kept) (by
    rw [p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)])
  have leaf2 : LeafInput 0x8000dd9c#64 c2 :=
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
  -- the name's bytes, unchanged by the frame's stores
  have nameMem : ∀ i, i ≤ name.length →
      (c2.σ.mem[np.toNat + i]?).getD 0 = (c0.σ.mem[(np + BitVec.ofNat 64 i).toNat]?).getD 0 := by
    intro i hi
    rw [m2, p.memory, h.named.byte_nat h.nameHigh hi]
    rw [writeLog_out _ _ _ (outL_of_range (arena_out h.frame (a := np.toNat) (n := name.length + 1)
      (by have := h.nameHigh; omega)) (by omega) (by omega))]
  have npLo := h.nameLow
  have npHi := h.nameHigh
  simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at npLo npHi
  obtain ⟨d3, run3, p3⟩ := (strlen_ready (a := np.toNat) (len := name.length) c2 leaf2 ready2
    (fun i hi => by rw [nameMem i (by omega), h.named.bytes i hi]; exact h.named.nonzero i hi)
    (by rw [nameMem _ (Nat.le_refl _)]; exact h.named.nul)
    (by omega) (by omega) (Or.inr (by omega))
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gholds_lookup (n := 10) _ p2.regs rfl)).run c2
    ⟨by have := p2.pc; rw [nameLen_call_target] at this; exact this, rfl⟩
  -- the fit and the nonempty test
  have k3 : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 11, 12, 13, 14, 15] → gprGet d3.σ n = gprGet c2.σ n := p3.registers
  have k2 : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 1 → n ≠ 10 → gprGet c2.σ n = gprGet c.σ n := fun n lo hi n1 n10 =>
    (p2.gpr_frame (by decide) n lo hi (by simpa using n1)).trans (p1.gpr_frame (by decide) n lo hi (by simpa using n10))
  have keep : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 10, 11, 12, 13, 14, 15] → gprGet d3.σ n = gprGet c.σ n := by
    intro n lo hi out
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    exact (k3 n lo hi (by simp; omega)).trans (k2 n lo hi out.1 out.2.1)
  have e18 := (keep 18 (by decide) (by decide) (by decide)).trans p.bufEnd
  have e20 := (keep 20 (by decide) (by decide) (by decide)).trans p.bufData
  have l3 : LeafInput (regsAt d3 1) d3 := by rw [regsAt_of p3.raReg]; exact p3.toLeafInput
  have tEnd : (bufEnd sp).toNat = sp.toNat - 81 := frame_ptr h.frame 81 (by decide) (by decide)
  have tData : (bufData sp).toNat = sp.toNat - 336 := frame_ptr h.frame 336 (by decide) (by decide)
  have fitsLen := h.fits
  obtain ⟨d4, run4, p4⟩ := (fits_fast d3 (regsAt d3) l3 (by
      simp only [fits_input, GHolds, regsAt_of p3.result, regsAt_of e18, regsAt_of e20]
      exact ⟨p3.result, e18, e20, trivial⟩)
    (by
      rw [regsAt_of p3.result, regsAt_of e18, regsAt_of e20]
      apply bgeu_of_le
      have lo := h.frame.lower
      simp only [Vsa.Sim.DlHeap.heapEnd] at lo
      rw [BitVec.toNat_add, tData, tEnd, BitVec.toNat_ofNat]
      omega)).run d3 ⟨p3.pc, rfl⟩
  have o4 := p4.regs
  simp only [fits_regs, regsAt_of p3.result, regsAt_of e20, GHolds] at o4
  obtain ⟨g8, g10, -, -, -⟩ := o4
  have k4 : ∀ n, n ≠ 8 → 1 ≤ n → n ≤ 31 → gprGet d4.σ n = gprGet d3.σ n :=
    fun n ne lo hi => p4.gpr_frame (by decide) n lo hi (by simpa using ne)
  have ra4 := (k4 1 (by decide) (by decide) (by decide)).trans p3.raReg
  have l4 : LeafInput (regsAt d4 1) d4 := by
    rw [regsAt_of ra4]; exact ⟨p4.good, p4.image, p4.minstret, ra4, by decide, p4.tick⟩
  have nzLen : BitVec.ofNat 64 name.length ≠ 0#64 := by
    intro e; have t := congrArg BitVec.toNat e; have := h.fits; have := h.nonempty
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h.fits (by decide))] at t
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at t; omega
  obtain ⟨d5, run5, p5⟩ := (nonempty_fast d4 (regsAt d4) l4 (by
      simp only [nonempty_input, GHolds, regsAt_of g10]; exact ⟨g10, trivial⟩)
    (by rw [regsAt_of g10]; exact bne_of_ne nzLen)).run d4 ⟨p4.pc, rfl⟩
  have k5 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet d5.σ n = gprGet d4.σ n :=
    fun n lo hi => p5.gpr_frame (by decide) n lo hi (by simp)
  have gp3 : gpr d3 3 = some VsaIris.MallocFast.gpV :=
    (k3 3 (by decide) (by decide) (by decide)).trans ready2.gp
  have ready3 : LibraryReady d3 := ⟨p3.libraryGood.gpr, gp3, p3.libraryGood.htifIdle⟩
  refine ⟨d5, run1.trans (run2.trans (run3.trans (run4.trans run5))), ?_⟩
  exact
    { leaf := ⟨p5.good, p5.image, p5.minstret, (k5 1 (by decide) (by decide)).trans ra4, by decide, p5.tick⟩
      ready := (ready3.carry p4.kept (p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p5.kept
        (p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
      pc := p5.pc
      length := (k5 10 (by decide) (by decide)).trans g10
      cursor := (k5 8 (by decide) (by decide)).trans g8
      data := (k5 20 (by decide) (by decide)).trans ((k4 20 (by decide) (by decide) (by decide)).trans e20)
      name := (k5 21 (by decide) (by decide)).trans ((k4 21 (by decide) (by decide) (by decide)).trans
        (keep 21 (by decide) (by decide) (by decide)))|>.trans p.name
      stack := (k5 2 (by decide) (by decide)).trans ((k4 2 (by decide) (by decide) (by decide)).trans
        ((keep 2 (by decide) (by decide) (by decide)).trans p.stack))
      memory := fun x => by rw [p5.memory, wl_nil, p4.memory, wl_nil, p3.memory x, m2]
      output := by
        have o3 := p3.output
        simp only [Vsa.Machine.output] at o3 ⊢
        rw [p5.output, p4.output, o3, p2.output, p1.output]
      frame := fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (k5 n lo hi).trans ((k4 n out.2.1 lo hi).trans (keep n lo hi (by simp; omega)))
      htif := by
        rw [p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide)]
        exact p3.libraryGood.htifIdle.trans ready.htifIdle.symm }

end OCaml.Vm.Primitives.Uncaught.FormatException
