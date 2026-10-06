import OCaml.Vm.Gc.Generated.BarrierYoung
import OCaml.Vm.Gc.Generated.BarrierAbove
import OCaml.Vm.Gc.Generated.BarrierBelow
import OCaml.Vm.Gc.Generated.BarrierOldImm
import OCaml.Vm.Gc.Generated.BarrierOldHigh
import OCaml.Vm.Gc.Generated.BarrierOldLow
import OCaml.Vm.Gc.Generated.BarrierOldYoung
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Boot.Startup.GprPresence
import OCaml.Vm.Gc.Generated.BarrierValImm
import OCaml.Vm.Gc.Generated.BarrierValHigh
import OCaml.Vm.Gc.Generated.BarrierValLow
import OCaml.Vm.Gc.Generated.BarrierInsert
import OCaml.Vm.Gc.Generated.BarrierFull
import OCaml.Vm.Gc.Generated.BarrierReturn
import OCaml.Vm.Primitives.Word32Access
import Vsa.Sim.SegToTripleFramed
import OCaml.Vm.Primitives.LibraryEffects

/-!
# `caml_modify` at the machine level

The generated segments (`Gc/Generated/Barrier*.lean`) composed into the
write barrier's runs. This file: the entry facts (`Entry`) and the slot
classification, which either finishes a young slot (`young_run`) or reaches
the major-slot body at `a9cc` (`major_head`).
-/

namespace OCaml.Vm.Gc.Barrier
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives VsaIris.Inst LeanRV64DExecutable
open OCaml.Vm.Boot.Startup (GprPresent)

/-- The major-slot stores: `ra` into the native frame, then the slot. -/
def majorLog (sp ra slot v : BitVec 64) : List WEntry :=
  [(((sp + -32#64) + BitVec.ofNat 64 24).toNat, 8, ra), (((slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0).toNat, 8, v)]

/-- A slot address lies in the minor heap `(young_start, young_end)`. -/
def YoungIn (ys ye x : BitVec 64) : Prop := ys.toNat < x.toNat ∧ x.toNat < ye.toNat

/-- `caml_modify(slot, v)` at its entry: the registers, the domain's
`young_start`/`young_end`, and the windows of the slot and the domain words. -/
structure Entry (slot v ra sp dom ys ye old : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  code : Code.Caml_modifyLoaded c.σ.mem
  slotReg : gprGet c.σ 10 = some slot
  valueReg : gprGet c.σ 11 = some v
  raReg : gprGet c.σ 1 = some ra
  stackReg : gprGet c.σ 2 = some sp
  raAligned : ra.toNat % 4 = 0
  domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = dom
  youngStart : bytesT c.σ.mem (dom + BitVec.ofNat 64 32).toNat 8 = ys
  youngEnd : bytesT c.σ.mem (dom + BitVec.ofNat 64 40).toNat 8 = ye
  startRead : ReadWindow (dom + BitVec.ofNat 64 32) 8
  endRead : ReadWindow (dom + BitVec.ofNat 64 40) 8
  slotWrite : WriteWindow (slot + BitVec.ofNat 64 0) 8
  /-- the slot's old value -/
  oldWord : bytesT c.σ.mem (slot + BitVec.ofNat 64 0).toNat 8 = old
  /-- the native frame's saved `ra` slot -/
  frameWrite : WriteWindow ((sp + -32#64) + BitVec.ofNat 64 24) 8
  /-- the collector is idle (`Phase_idle`): no darkening -/
  idle : bytesT c.σ.mem Layout.sym_caml_gc_phase 4 = 3#32
  /-- the slot is apart from the frame slot -/
  slotFrame : (slot + BitVec.ofNat 64 0).toNat + 8 ≤ ((sp + -32#64) + BitVec.ofNat 64 24).toNat ∨
    ((sp + -32#64) + BitVec.ofNat 64 24).toNat + 8 ≤ (slot + BitVec.ofNat 64 0).toNat
  /-- the major-slot stores lie above `caml_modify`'s code -/
  aboveCode : ∀ e ∈ majorLog sp ra slot v, 0x8000aa98 ≤ e.1
  /-- the words read after the major-slot stores lie apart from them -/
  readsApart : ∀ x ∈ [Layout.sym_Caml_state, (dom + BitVec.ofNat 64 32).toNat, (dom + BitVec.ofNat 64 40).toNat,
    Layout.sym_caml_gc_phase], ∀ e ∈ majorLog sp ra slot v, x + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ x

theorem caml_state_read : ReadWindow (0x80064d08#64) 8 := by constructor <;> decide

theorem dom_value {m : Std.ExtHashMap Nat (BitVec 8)} {dom : BitVec 64}
    (h : bytesT m Layout.sym_Caml_state 8 = dom) : bytesVal .ld (Primitives.read8 m Layout.sym_Caml_state) = dom := by
  rw [read8_value]; exact h

theorem cs_nat : (0x80064d08#64 : BitVec 64).toNat = Layout.sym_Caml_state := by decide

/-- The loads of the slot classification. -/
def headLoads (m : Std.ExtHashMap Nat (BitVec 8)) (dom : BitVec 64) : List (List (BitVec 8)) :=
  [Primitives.read8 m Layout.sym_Caml_state, Primitives.read8 m (dom + BitVec.ofNat 64 40).toNat,
   Primitives.read8 m (dom + BitVec.ofNat 64 32).toNat]

/-- The young-slot store. -/
def youngLog (slot v : BitVec 64) : List WEntry := [((slot + BitVec.ofNat 64 0).toNat, 8, v)]

/-- After the young-slot path: returned with the slot written. -/
structure YoungDone (ra : BitVec 64) (slot v : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some ra
  memory : after.σ.mem = writeLog before.σ.mem (youngLog slot v)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ wrChain BarrierYoung.blocks, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

/-- **A slot in the minor heap**: store and return. -/
theorem young_run {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c)
    (young : YoungIn ys ye slot) :
    FnSummary BarrierYoung.pc (fun d => d = c) (YoungDone ra slot v c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have b1 := dom_value e.domain
  have input : BarrierYoung.Input slot v ra (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat) d :=
    { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
      registers := ⟨e.slotReg, e.valueReg, e.raReg, trivial⟩
      route := {
        read1 := caml_state_read
        pins1 := by change LPins8 d.σ.mem _ _; rw [cs_nat]; exact read8_pins _ _
        read2 := by rw [b1]; exact e.endRead
        pins2 := by change LPins8 d.σ.mem _ _; rw [b1]; exact read8_pins _ _
        control0 := by rw [read8_value, e.youngEnd]; exact young.2
        read3 := by rw [b1]; exact e.startRead
        pins3 := by change LPins8 d.σ.mem _ _; rw [b1]; exact read8_pins _ _
        control1 := by rw [read8_value, e.youngStart]; exact young.1
        write1 := e.slotWrite
        control2 := e.raAligned } }
  obtain ⟨d', run, post⟩ := (BarrierYoung.run input).run d ⟨pc, rfl⟩
  refine ⟨d', run, ⟨post.good, post.tick, post.minstret, ?_, ?_, post.output, post.frame, fun p => BarrierYoung.gpr_present post p⟩⟩
  · rw [post.pc, BarrierYoung.endpoint _ _ _ _ _ _ e.raAligned]
  · rw [post.memory, BarrierYoung.log]; rfl

/-- A generated chain's register frame, for one GPR outside its writes. -/
theorem keep_gpr {bs entry L loads before after} (post : BlockPost bs entry L loads before after)
    {writes : List Nat} (keys : KeysOK writes) (subset : ∀ n ∈ wrChain bs, n ∈ writes) (n : Nat)
    (lower : 1 ≤ n) (upper : n ≤ 31) (outside : n ∉ writes) : gprGet after.σ n = gprGet before.σ n := by
  apply gprGet_of_frame n lower upper (gpr_avoids_noise n (by omega) lower)
  · intro m hm
    have bounds := keys m (subset m hm)
    exact gprReg_beq_false m (by omega) n (by omega) bounds.1 lower (fun e => outside (e ▸ subset m hm))
  · exact post.frame

/-- At the major-slot body (`a9cc`), memory unchanged. -/
structure AtMajor (slot v ra sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some 0x8000a9cc#64
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  regs : GHolds after.σ [(10, slot), (11, v), (1, ra), (2, sp), (13, 0x80064d08#64)]
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [13, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

/-- **A major (or static) slot**: classify it and reach the body. -/
theorem major_head {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c)
    (major : ¬ YoungIn ys ye slot) :
    FnSummary BarrierAbove.pc (fun d => d = c) (AtMajor slot v ra sp c) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have b1 := dom_value e.domain
  by_cases above : ye.toNat ≤ slot.toNat
  · have input : BarrierAbove.Input slot (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
        (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) d :=
      { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
        registers := ⟨e.slotReg, trivial⟩
        route := {
          read1 := caml_state_read
          pins1 := by change LPins8 d.σ.mem _ _; rw [cs_nat]; exact read8_pins _ _
          read2 := by rw [b1]; exact e.endRead
          pins2 := by change LPins8 d.σ.mem _ _; rw [b1]; exact read8_pins _ _
          control0 := by rw [read8_value, e.youngEnd]; exact above } }
    obtain ⟨d', run, post⟩ := (BarrierAbove.run input).run d ⟨pc, rfl⟩
    have r := post.regs
    rw [BarrierAbove.registers] at r
    have keep := keep_gpr post (by decide) BarrierAbove.written
    obtain ⟨-, -, h13, h10, -⟩ := r
    refine ⟨d', run, ⟨post.good, post.tick, post.minstret, by rw [post.pc]; rfl, ?_, post.output,
      ⟨h10, (keep 11 (by decide) (by decide) (by decide)).trans e.valueReg,
       (keep 1 (by decide) (by decide) (by decide)).trans e.raReg,
       (keep 2 (by decide) (by decide) (by decide)).trans e.stackReg, h13, trivial⟩,
      fun q noise out => post.frame q noise fun n hn => out n (BarrierAbove.written n hn), fun p => BarrierAbove.gpr_present post p⟩⟩
    rw [post.memory, BarrierAbove.log]; rfl
  · have below : slot.toNat < ye.toNat ∧ slot.toNat ≤ ys.toNat := by
      unfold YoungIn at major; omega
    have input : BarrierBelow.Input slot (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
        (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat) d :=
      { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
        registers := ⟨e.slotReg, trivial⟩
        route := {
          read1 := caml_state_read
          pins1 := by change LPins8 d.σ.mem _ _; rw [cs_nat]; exact read8_pins _ _
          read2 := by rw [b1]; exact e.endRead
          pins2 := by change LPins8 d.σ.mem _ _; rw [b1]; exact read8_pins _ _
          control0 := by rw [read8_value, e.youngEnd]; exact below.1
          read3 := by rw [b1]; exact e.startRead
          pins3 := by change LPins8 d.σ.mem _ _; rw [b1]; exact read8_pins _ _
          control1 := by rw [read8_value, e.youngStart]; exact below.2 } }
    obtain ⟨d', run, post⟩ := (BarrierBelow.run input).run d ⟨pc, rfl⟩
    have r := post.regs
    rw [BarrierBelow.registers] at r
    have keep := keep_gpr post (by decide) BarrierBelow.written
    obtain ⟨-, -, h13, h10, -⟩ := r
    refine ⟨d', run, ⟨post.good, post.tick, post.minstret, by rw [post.pc]; rfl, ?_, post.output,
      ⟨h10, (keep 11 (by decide) (by decide) (by decide)).trans e.valueReg,
       (keep 1 (by decide) (by decide) (by decide)).trans e.raReg,
       (keep 2 (by decide) (by decide) (by decide)).trans e.stackReg, h13, trivial⟩,
      fun q noise out => post.frame q noise fun n hn => out n (BarrierBelow.written n hn), fun p => BarrierBelow.gpr_present post p⟩⟩
    rw [post.memory, BarrierBelow.log]; rfl

/-- The old value is a young block: the slot is already remembered. -/
def OldYoung (ys ye old : BitVec 64) : Prop := old &&& 1#64 = 0#64 ∧ YoungIn ys ye old

/-- At the new-value classification (`aa0c`), after the major-slot stores. -/
structure AtBody (slot v ra sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some 0x8000aa0c#64
  memory : after.σ.mem = writeLog before.σ.mem (majorLog sp ra slot v)
  output : after.σ.sailOutput = before.σ.sailOutput
  regs : GHolds after.σ [(14, v), (15, slot), (13, 0x80064d08#64), (2, sp + -32#64), (1, ra)]
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [2, 10, 11, 12, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

/-- At the return (`aa44`), after the major-slot stores. -/
structure AtReturn (slot v ra sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some 0x8000aa44#64
  memory : after.σ.mem = writeLog before.σ.mem (majorLog sp ra slot v)
  output : after.σ.sailOutput = before.σ.sailOutput
  regs : GHolds after.σ [(2, sp + -32#64)]
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [2, 10, 11, 12, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

/-- The old-value classification's outcome. -/
def OldPost (slot v ra sp ys ye old : BitVec 64) (before after : Config) : Prop :=
  (OldYoung ys ye old ∧ AtReturn slot v ra sp before after) ∨
    (¬ OldYoung ys ye old ∧ AtBody slot v ra sp before after)

theorem slot_exact {slot : BitVec 64} :
    (slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0 = slot + BitVec.ofNat 64 0 := by simp

/-- A word read after the major-slot stores, apart from them. -/
theorem stored_pins {m : Std.ExtHashMap Nat (BitVec 8)} {sp ra slot v : BitVec 64} {x : Nat}
    (apart : ∀ e ∈ majorLog sp ra slot v, x + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ x) :
    LPins8 (writeLog m (majorLog sp ra slot v)) x (Primitives.read8 m x) :=
  lpins8_writeLog (read8_pins _ _) (outLRange_of_forall apart)

theorem stored_pins4 {m : Std.ExtHashMap Nat (BitVec 8)} {sp ra slot v : BitVec 64} {x : Nat}
    (apart : ∀ e ∈ majorLog sp ra slot v, x + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ x) :
    LPins4 (writeLog m (majorLog sp ra slot v)) x (read4 m x) :=
  lpins4_writeLog (read4_pins _ _) (outLRange_of_forall fun e he => by have := apart e he; omega)

theorem idle_nonzero {m : Std.ExtHashMap Nat (BitVec 8)} (idle : bytesT m Layout.sym_caml_gc_phase 4 = 3#32) :
    bytesVal .lw (read4 m Layout.sym_caml_gc_phase) ≠ 0x0#64 := by
  rw [read4_value, idle]; decide

theorem phase_nat : (0x80064ac0#64 : BitVec 64).toNat = Layout.sym_caml_gc_phase := by decide

theorem cs_zero_nat : (0x80064d08#64 + BitVec.ofNat 64 0).toNat = Layout.sym_Caml_state := by decide

/-- The entry facts at the major-slot body: memory is unchanged. -/
theorem Entry.atMajor {slot v ra sp dom ys ye old} {c d : Config} (e : Entry slot v ra sp dom ys ye old c)
    (m : AtMajor slot v ra sp c d) : Entry slot v ra sp dom ys ye old d := by
  obtain ⟨h10, h11, h1, h2, -, -⟩ := m.regs
  have mem := m.memory
  exact { good := m.good, tick := m.tick, minstret := m.minstret, code := by rw [mem]; exact e.code
          slotReg := h10, valueReg := h11, raReg := h1, stackReg := h2, raAligned := e.raAligned
          domain := by rw [mem]; exact e.domain, youngStart := by rw [mem]; exact e.youngStart
          youngEnd := by rw [mem]; exact e.youngEnd, startRead := e.startRead, endRead := e.endRead
          slotWrite := e.slotWrite, oldWord := by rw [mem]; exact e.oldWord, frameWrite := e.frameWrite
          idle := by rw [mem]; exact e.idle, slotFrame := e.slotFrame, aboveCode := e.aboveCode
          readsApart := e.readsApart }

theorem Entry.oldV {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    bytesVal .ld (Primitives.read8 c.σ.mem (slot + BitVec.ofNat 64 0).toNat) = old := by rw [read8_value]; exact e.oldWord
theorem Entry.domV {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    bytesVal .ld (Primitives.read8 c.σ.mem Layout.sym_Caml_state) = dom := dom_value e.domain
theorem Entry.endV {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    bytesVal .ld (Primitives.read8 c.σ.mem (dom + BitVec.ofNat 64 40).toNat) = ye := by rw [read8_value]; exact e.youngEnd
theorem Entry.startV {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    bytesVal .ld (Primitives.read8 c.σ.mem (dom + BitVec.ofNat 64 32).toNat) = ys := by rw [read8_value]; exact e.youngStart
theorem Entry.slotW {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    WriteWindow ((slot + BitVec.ofNat 64 0) + BitVec.ofNat 64 0) 8 := by rw [slot_exact]; exact e.slotWrite
theorem Entry.aCs {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    ∀ x ∈ majorLog sp ra slot v, Layout.sym_Caml_state + 8 ≤ x.1 ∨ x.1 + x.2.1 ≤ Layout.sym_Caml_state :=
  e.readsApart _ (List.mem_cons_self ..)
theorem Entry.aStart {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    ∀ x ∈ majorLog sp ra slot v, (dom + BitVec.ofNat 64 32).toNat + 8 ≤ x.1 ∨ x.1 + x.2.1 ≤ (dom + BitVec.ofNat 64 32).toNat :=
  e.readsApart _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem Entry.aEnd {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    ∀ x ∈ majorLog sp ra slot v, (dom + BitVec.ofNat 64 40).toNat + 8 ≤ x.1 ∨ x.1 + x.2.1 ≤ (dom + BitVec.ofNat 64 40).toNat :=
  e.readsApart _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem Entry.aPhase {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    ∀ x ∈ majorLog sp ra slot v, Layout.sym_caml_gc_phase + 8 ≤ x.1 ∨ x.1 + x.2.1 ≤ Layout.sym_caml_gc_phase :=
  e.readsApart _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- An old block at or above `young_end`. -/
theorem old_high {slot v ra sp dom ys ye old} {d : Config} (e : Entry slot v ra sp dom ys ye old d)
    (h13 : gprGet d.σ 13 = some 0x80064d08#64) (pc : PCAt BarrierOldHigh.pc d)
    (imm : old &&& 1#64 = 0#64) (above : ye.toNat ≤ old.toNat) :
    ∃ d1, Steps d d1 ∧ AtBody slot v ra sp d d1 := by
  have input : BarrierOldHigh.Input sp ra slot v (0x80064d08#64) (Primitives.read8 d.σ.mem (slot + BitVec.ofNat 64 0).toNat)
      (Primitives.read8 d.σ.mem Layout.sym_Caml_state) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat)
      (read4 d.σ.mem Layout.sym_caml_gc_phase) d :=
    { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
      registers := ⟨e.stackReg, e.raReg, e.slotReg, e.valueReg, h13, trivial⟩
      route := {
        write1 := e.frameWrite, read1 := e.slotWrite.read, pins1 := read8_pins _ _, apart1_1 := e.slotFrame
        write2 := e.slotW
        control0 := by rw [e.oldV]; exact imm
        read2 := caml_state_read
        pins2 := by
          rw [cs_zero_nat]; dsimp only [BarrierOldHigh.mem1, BarrierOldHigh.mem0]; exact stored_pins e.aCs
        read3 := by rw [e.domV]; exact e.endRead
        pins3 := by rw [e.domV]; dsimp only [BarrierOldHigh.mem1, BarrierOldHigh.mem0]; exact stored_pins e.aEnd
        control1 := by rw [e.endV, e.oldV]; exact above
        read4 := by constructor <;> decide
        pins4 := by
          rw [phase_nat]; dsimp only [BarrierOldHigh.mem2, BarrierOldHigh.mem1, BarrierOldHigh.mem0]
          exact stored_pins4 e.aPhase
        control2 := idle_nonzero e.idle } }
  obtain ⟨d1, run, post⟩ := (BarrierOldHigh.run input).run d ⟨pc, rfl⟩
  have r := post.regs
  rw [BarrierOldHigh.registers] at r
  obtain ⟨-, -, r14, -, r15, r2, r1, r13, -⟩ := r
  exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
    by rw [post.memory, BarrierOldHigh.log]; rfl, post.output, ⟨r14, r15, r13, r2, r1, trivial⟩,
    fun q noise out => post.frame q noise fun n hn => out n (BarrierOldHigh.written n hn), fun p => BarrierOldHigh.gpr_present post p⟩

/-- An old block at or below `young_start`. -/
theorem old_low {slot v ra sp dom ys ye old} {d : Config} (e : Entry slot v ra sp dom ys ye old d)
    (h13 : gprGet d.σ 13 = some 0x80064d08#64) (pc : PCAt BarrierOldLow.pc d)
    (imm : old &&& 1#64 = 0#64) (below : old.toNat < ye.toNat) (low : old.toNat ≤ ys.toNat) :
    ∃ d1, Steps d d1 ∧ AtBody slot v ra sp d d1 := by
  have input : BarrierOldLow.Input sp ra slot v 0x80064d08#64
      (Primitives.read8 d.σ.mem (slot + BitVec.ofNat 64 0).toNat) (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat)
      (read4 d.σ.mem Layout.sym_caml_gc_phase) d :=
    { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
      registers := ⟨e.stackReg, e.raReg, e.slotReg, e.valueReg, h13, trivial⟩
      route := {
        write1 := e.frameWrite, read1 := e.slotWrite.read, pins1 := read8_pins _ _, apart1_1 := e.slotFrame
        write2 := e.slotW
        control0 := by rw [e.oldV]; exact imm
        read2 := caml_state_read
        pins2 := by
          rw [cs_zero_nat]; dsimp only [BarrierOldLow.mem1, BarrierOldLow.mem0]; exact stored_pins e.aCs
        read3 := by rw [e.domV]; exact e.endRead
        pins3 := by rw [e.domV]; dsimp only [BarrierOldLow.mem1, BarrierOldLow.mem0]; exact stored_pins e.aEnd
        control1 := by rw [e.endV, e.oldV]; exact below
        read4 := by rw [e.domV]; exact e.startRead
        pins4 := by
          rw [e.domV]; dsimp only [BarrierOldLow.mem2, BarrierOldLow.mem1, BarrierOldLow.mem0]
          exact stored_pins e.aStart
        control2 := by rw [e.startV, e.oldV]; exact low
        read5 := by constructor <;> decide
        pins5 := by
          rw [phase_nat]; dsimp only [BarrierOldLow.mem3, BarrierOldLow.mem2, BarrierOldLow.mem1, BarrierOldLow.mem0]
          exact stored_pins4 e.aPhase
        control3 := idle_nonzero e.idle } }
  obtain ⟨d1, run, post⟩ := (BarrierOldLow.run input).run d ⟨pc, rfl⟩
  have r := post.regs
  rw [BarrierOldLow.registers] at r
  obtain ⟨-, -, r14, -, r15, r2, r1, r13, -⟩ := r
  exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
    by rw [post.memory, BarrierOldLow.log]; rfl, post.output, ⟨r14, r15, r13, r2, r1, trivial⟩,
    fun q noise out => post.frame q noise fun n hn => out n (BarrierOldLow.written n hn), fun p => BarrierOldLow.gpr_present post p⟩

/-- A young old value: the slot is already remembered. -/
theorem old_young {slot v ra sp dom ys ye old} {d : Config} (e : Entry slot v ra sp dom ys ye old d)
    (h13 : gprGet d.σ 13 = some 0x80064d08#64) (pc : PCAt BarrierOldYoung.pc d)
    (young : OldYoung ys ye old) : ∃ d1, Steps d d1 ∧ AtReturn slot v ra sp d d1 := by
  have input : BarrierOldYoung.Input sp ra slot v 0x80064d08#64
      (Primitives.read8 d.σ.mem (slot + BitVec.ofNat 64 0).toNat) (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat) d :=
    { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
      registers := ⟨e.stackReg, e.raReg, e.slotReg, e.valueReg, h13, trivial⟩
      route := {
        write1 := e.frameWrite, read1 := e.slotWrite.read, pins1 := read8_pins _ _, apart1_1 := e.slotFrame
        write2 := e.slotW
        control0 := by rw [e.oldV]; exact young.1
        read2 := caml_state_read
        pins2 := by
          rw [cs_zero_nat]; dsimp only [BarrierOldYoung.mem1, BarrierOldYoung.mem0]; exact stored_pins e.aCs
        read3 := by rw [e.domV]; exact e.endRead
        pins3 := by rw [e.domV]; dsimp only [BarrierOldYoung.mem1, BarrierOldYoung.mem0]; exact stored_pins e.aEnd
        control1 := by rw [e.endV, e.oldV]; exact young.2.2
        read4 := by rw [e.domV]; exact e.startRead
        pins4 := by
          rw [e.domV]; dsimp only [BarrierOldYoung.mem2, BarrierOldYoung.mem1, BarrierOldYoung.mem0]
          exact stored_pins e.aStart
        control2 := by rw [e.startV, e.oldV]; exact young.2.1 } }
  obtain ⟨d1, run, post⟩ := (BarrierOldYoung.run input).run d ⟨pc, rfl⟩
  have r := post.regs
  rw [BarrierOldYoung.registers] at r
  obtain ⟨-, -, -, -, -, r2, -⟩ := r
  exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
    by rw [post.memory, BarrierOldYoung.log]; rfl, post.output, ⟨r2, trivial⟩,
    fun q noise out => post.frame q noise fun n hn => out n (BarrierOldYoung.written n hn), fun p => BarrierOldYoung.gpr_present post p⟩

/-- An immediate old value. -/
theorem old_imm {slot v ra sp dom ys ye old} {d : Config} (e : Entry slot v ra sp dom ys ye old d)
    (h13 : gprGet d.σ 13 = some 0x80064d08#64) (pc : PCAt BarrierOldImm.pc d)
    (imm : old &&& 1#64 ≠ 0#64) : ∃ d1, Steps d d1 ∧ AtBody slot v ra sp d d1 := by
  have input : BarrierOldImm.Input sp ra slot v (Primitives.read8 d.σ.mem (slot + BitVec.ofNat 64 0).toNat) d :=
    { good := e.good, tick := e.tick, minstret := e.minstret, code0 := e.code
      registers := ⟨e.stackReg, e.raReg, e.slotReg, e.valueReg, trivial⟩
      route := {
        write1 := e.frameWrite, read1 := e.slotWrite.read, pins1 := read8_pins _ _, apart1_1 := e.slotFrame
        write2 := e.slotW
        control0 := by rw [e.oldV]; exact imm } }
  obtain ⟨d1, run, post⟩ := (BarrierOldImm.run input).run d ⟨pc, rfl⟩
  have r := post.regs
  rw [BarrierOldImm.registers] at r
  obtain ⟨-, r14, -, r15, r2, r1, -⟩ := r
  have r13 : gprGet d1.σ 13 = some 0x80064d08#64 :=
    (keep_gpr post (by decide) BarrierOldImm.written 13 (by decide) (by decide) (by decide)).trans h13
  exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
    by rw [post.memory, BarrierOldImm.log]; rfl, post.output, ⟨r14, r15, r13, r2, r1, trivial⟩,
    fun q noise out => post.frame q noise fun n hn => out n (by
      have h := BarrierOldImm.written n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega), fun p => BarrierOldImm.gpr_present post p⟩

/-- **The old value's classification** from the major-slot body. -/
theorem old_run {slot v ra sp dom ys ye old} {c d : Config} (e : Entry slot v ra sp dom ys ye old c)
    (m : AtMajor slot v ra sp c d) :
    FnSummary BarrierOldImm.pc (fun x => x = d) (OldPost slot v ra sp ys ye old d) := by
  constructor
  rintro d0 ⟨pc, rfl⟩
  have e' := e.atMajor m
  obtain ⟨-, -, -, -, h13, -⟩ := m.regs
  by_cases imm : old &&& 1#64 = 0#64
  · by_cases above : ye.toNat ≤ old.toNat
    · obtain ⟨d1, run, post⟩ := old_high e' h13 pc imm above
      exact ⟨d1, run, Or.inr ⟨fun h => Nat.not_lt.mpr above h.2.2, post⟩⟩
    · by_cases low : old.toNat ≤ ys.toNat
      · obtain ⟨d1, run, post⟩ := old_low e' h13 pc imm (by omega) low
        exact ⟨d1, run, Or.inr ⟨fun h => by have := h.2.1; omega, post⟩⟩
      · obtain ⟨d1, run, post⟩ := old_young e' h13 pc ⟨imm, by omega, by omega⟩
        exact ⟨d1, run, Or.inl ⟨⟨imm, by omega, by omega⟩, post⟩⟩
  · obtain ⟨d1, run, post⟩ := old_imm e' h13 pc imm
    exact ⟨d1, run, Or.inr ⟨fun h => imm h.1, post⟩⟩

/-! ### The new value's classification (`aa0c`) -/

/-- The domain words the value classification reads, in one memory. -/
structure Domain (dom ys ye : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  domain : bytesT m Layout.sym_Caml_state 8 = dom
  youngStart : bytesT m (dom + BitVec.ofNat 64 32).toNat 8 = ys
  youngEnd : bytesT m (dom + BitVec.ofNat 64 40).toNat 8 = ye
  startRead : ReadWindow (dom + BitVec.ofNat 64 32) 8
  endRead : ReadWindow (dom + BitVec.ofNat 64 40) 8

/-- The remembered set (`Caml_state->ref_table`), in one memory. -/
structure Table (dom tbl ptr limit : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  tableWord : bytesT m (dom + BitVec.ofNat 64 104).toNat 8 = tbl
  ptrWord : bytesT m (tbl + BitVec.ofNat 64 24).toNat 8 = ptr
  limitWord : bytesT m (tbl + BitVec.ofNat 64 32).toNat 8 = limit
  tableRead : ReadWindow (dom + BitVec.ofNat 64 104) 8
  ptrWrite : WriteWindow (tbl + BitVec.ofNat 64 24) 8
  limitRead : ReadWindow (tbl + BitVec.ofNat 64 32) 8
  entryWrite : WriteWindow (ptr + BitVec.ofNat 64 0) 8

/-- The words survive stores apart from them. -/
theorem Table.writeLog {dom tbl ptr limit : BitVec 64} {m : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry}
    (t : Table dom tbl ptr limit m)
    (apart : ∀ x ∈ [(dom + BitVec.ofNat 64 104).toNat, (tbl + BitVec.ofNat 64 24).toNat,
      (tbl + BitVec.ofNat 64 32).toNat], ∀ e ∈ log, x + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ x) :
    Table dom tbl ptr limit (Vsa.Sim.writeLog m log) :=
  { t with
    tableWord := by
      rw [bytesT_writeLog_out _ (outLRange_of_forall (apart _ (List.mem_cons_self ..)))]; exact t.tableWord
    ptrWord := by
      rw [bytesT_writeLog_out _ (outLRange_of_forall (apart _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))]
      exact t.ptrWord
    limitWord := by
      rw [bytesT_writeLog_out _ (outLRange_of_forall
        (apart _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))]
      exact t.limitWord }

/-- The entry's domain words after the major-slot stores. -/
theorem Entry.domainBody {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    Domain dom ys ye (writeLog c.σ.mem (majorLog sp ra slot v)) where
  domain := by rw [bytesT_writeLog_out _ (outLRange_of_forall e.aCs)]; exact e.domain
  youngStart := by rw [bytesT_writeLog_out _ (outLRange_of_forall e.aStart)]; exact e.youngStart
  youngEnd := by rw [bytesT_writeLog_out _ (outLRange_of_forall e.aEnd)]; exact e.youngEnd
  startRead := e.startRead
  endRead := e.endRead

/-- After the value classification without an insertion, or after the
insertion: at the return (`aa44`). -/
structure ValueDone (fsp : BitVec 64) (log : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some 0x8000aa44#64
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  stack : gprGet after.σ 2 = some fsp
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10, 12, 13, 14], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

/-- The new value is a young block. -/
def ValueYoung (ys ye v : BitVec 64) : Prop := v &&& 1#64 = 0#64 ∧ YoungIn ys ye v

/-- The remembered-set insertion: bump `ptr`, store the slot address. -/
def insertLog (tbl ptr slot : BitVec 64) : List WEntry :=
  [((tbl + BitVec.ofNat 64 24).toNat, 8, ptr + 8#64), ((ptr + BitVec.ofNat 64 0).toNat, 8, slot)]

/-- Facts at the body (`aa0c`). -/
structure Body (slot v fsp dom ys ye : BitVec 64) (d : Config) : Prop where
  good : GoodState d.σ
  tick : d.tick < 2
  minstret : ∃ w, d.σ.regs.get? Register.minstret = some w
  code : Code.Caml_modifyLoaded d.σ.mem
  value : gprGet d.σ 14 = some v
  slot : gprGet d.σ 15 = some slot
  state : gprGet d.σ 13 = some 0x80064d08#64
  stack : gprGet d.σ 2 = some fsp
  domain : Domain dom ys ye d.σ.mem

/-- **The new value needs no remembering**: return. -/
theorem value_skip {slot v fsp dom ys ye} {d : Config} (b : Body slot v fsp dom ys ye d)
    (pc : PCAt BarrierValImm.pc d) (skip : ¬ ValueYoung ys ye v) :
    ∃ d1, Steps d d1 ∧ ValueDone fsp [] d d1 := by
  have csV : bytesVal .ld (Primitives.read8 d.σ.mem Layout.sym_Caml_state) = dom := dom_value b.domain.domain
  have endV : bytesVal .ld (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) = ye := by
    rw [read8_value]; exact b.domain.youngEnd
  have startV : bytesVal .ld (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat) = ys := by
    rw [read8_value]; exact b.domain.youngStart
  by_cases imm : v &&& 1#64 = 0#64
  · by_cases above : ye.toNat ≤ v.toNat
    · have input : BarrierValHigh.Input v (0x80064d08#64) (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
          (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) d :=
        { good := b.good, tick := b.tick, minstret := b.minstret, code0 := b.code
          registers := ⟨b.value, b.state, trivial⟩
          route := {
            control0 := imm
            read1 := caml_state_read
            pins1 := by rw [cs_zero_nat]; dsimp only [BarrierValHigh.mem1, BarrierValHigh.mem0]; exact read8_pins _ _
            read2 := by rw [csV]; exact b.domain.endRead
            pins2 := by rw [csV]; dsimp only [BarrierValHigh.mem1, BarrierValHigh.mem0]; exact read8_pins _ _
            control1 := by rw [endV]; exact above } }
      obtain ⟨d1, run, post⟩ := (BarrierValHigh.run input).run d ⟨pc, rfl⟩
      have keep := keep_gpr post (by decide) BarrierValHigh.written
      exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
        by rw [post.memory, BarrierValHigh.log], post.output,
        (keep 2 (by decide) (by decide) (by decide)).trans b.stack,
        fun q noise out => post.frame q noise fun n hn => out n (by
          have h := BarrierValHigh.written n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega), fun p => BarrierValHigh.gpr_present post p⟩
    · have low : v.toNat ≤ ys.toNat :=
        Nat.le_of_not_lt fun h => skip ⟨imm, h, by omega⟩
      have input : BarrierValLow.Input v (0x80064d08#64) (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
          (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat) d :=
        { good := b.good, tick := b.tick, minstret := b.minstret, code0 := b.code
          registers := ⟨b.value, b.state, trivial⟩
          route := {
            control0 := imm
            read1 := caml_state_read
            pins1 := by rw [cs_zero_nat]; dsimp only [BarrierValLow.mem1, BarrierValLow.mem0]; exact read8_pins _ _
            read2 := by rw [csV]; exact b.domain.endRead
            pins2 := by rw [csV]; dsimp only [BarrierValLow.mem1, BarrierValLow.mem0]; exact read8_pins _ _
            control1 := by rw [endV]; omega
            read3 := by rw [csV]; exact b.domain.startRead
            pins3 := by
              rw [csV]; dsimp only [BarrierValLow.mem2, BarrierValLow.mem1, BarrierValLow.mem0]
              exact read8_pins _ _
            control2 := by rw [startV]; exact low } }
      obtain ⟨d1, run, post⟩ := (BarrierValLow.run input).run d ⟨pc, rfl⟩
      have keep := keep_gpr post (by decide) BarrierValLow.written
      exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
        by rw [post.memory, BarrierValLow.log], post.output,
        (keep 2 (by decide) (by decide) (by decide)).trans b.stack,
        fun q noise out => post.frame q noise fun n hn => out n (by
          have h := BarrierValLow.written n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega), fun p => BarrierValLow.gpr_present post p⟩
  · have input : BarrierValImm.Input v d :=
      { good := b.good, tick := b.tick, minstret := b.minstret, code0 := b.code
        registers := ⟨b.value, trivial⟩
        route := { control0 := imm } }
    obtain ⟨d1, run, post⟩ := (BarrierValImm.run input).run d ⟨pc, rfl⟩
    have keep := keep_gpr post (by decide) BarrierValImm.written
    exact ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl,
      by rw [post.memory, BarrierValImm.log], post.output,
      (keep 2 (by decide) (by decide) (by decide)).trans b.stack,
      fun q noise out => post.frame q noise fun n hn => out n (by
        have h := BarrierValImm.written n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega), fun p => BarrierValImm.gpr_present post p⟩

/-- **A young value with room in the remembered set**: insert, then return. -/
theorem value_insert {slot v fsp dom ys ye tbl ptr limit} {d : Config} (b : Body slot v fsp dom ys ye d)
    (t : Table dom tbl ptr limit d.σ.mem) (pc : PCAt BarrierInsert.pc d)
    (young : ValueYoung ys ye v) (room : ptr.toNat < limit.toNat) :
    ∃ d1, Steps d d1 ∧ ValueDone fsp (insertLog tbl ptr slot) d d1 := by
  have csV : bytesVal .ld (Primitives.read8 d.σ.mem Layout.sym_Caml_state) = dom := dom_value b.domain.domain
  have word (x : Nat) : bytesVal .ld (Primitives.read8 d.σ.mem x) = bytesT d.σ.mem x 8 := read8_value _ _
  have tblV : bytesVal .ld (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 104).toNat) = tbl := by rw [word]; exact t.tableWord
  have ptrV : bytesVal .ld (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 24).toNat) = ptr := by rw [word]; exact t.ptrWord
  have limV : bytesVal .ld (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 32).toNat) = limit := by
    rw [word]; exact t.limitWord
  have input : BarrierInsert.Input v (0x80064d08#64) slot (Primitives.read8 d.σ.mem Layout.sym_Caml_state)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 40).toNat) (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 32).toNat)
      (Primitives.read8 d.σ.mem (dom + BitVec.ofNat 64 104).toNat) (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 24).toNat)
      (Primitives.read8 d.σ.mem (tbl + BitVec.ofNat 64 32).toNat) d :=
    { good := b.good, tick := b.tick, minstret := b.minstret, code0 := b.code
      registers := ⟨b.value, b.state, b.slot, trivial⟩
      route := {
        control0 := young.1
        read1 := caml_state_read
        pins1 := by rw [cs_zero_nat]; dsimp only [BarrierInsert.mem1, BarrierInsert.mem0]; exact read8_pins _ _
        read2 := by rw [csV]; exact b.domain.endRead
        pins2 := by rw [csV]; dsimp only [BarrierInsert.mem1, BarrierInsert.mem0]; exact read8_pins _ _
        control1 := by rw [word, b.domain.youngEnd]; exact young.2.2
        read3 := by rw [csV]; exact b.domain.startRead
        pins3 := by rw [csV]; dsimp only [BarrierInsert.mem2, BarrierInsert.mem1, BarrierInsert.mem0]; exact read8_pins _ _
        control2 := by rw [word, b.domain.youngStart]; exact young.2.1
        read4 := by rw [csV]; exact t.tableRead
        pins4 := by
          rw [csV]; dsimp only [BarrierInsert.mem3, BarrierInsert.mem2, BarrierInsert.mem1, BarrierInsert.mem0]
          exact read8_pins _ _
        read5 := by rw [tblV]; exact t.ptrWrite.read
        pins5 := by
          rw [tblV]; dsimp only [BarrierInsert.mem3, BarrierInsert.mem2, BarrierInsert.mem1, BarrierInsert.mem0]
          exact read8_pins _ _
        read6 := by rw [tblV]; exact t.limitRead
        pins6 := by
          rw [tblV]; dsimp only [BarrierInsert.mem3, BarrierInsert.mem2, BarrierInsert.mem1, BarrierInsert.mem0]
          exact read8_pins _ _
        control3 := by rw [ptrV, limV]; exact room
        write1 := by rw [tblV]; exact t.ptrWrite
        write2 := by rw [ptrV]; exact t.entryWrite } }
  obtain ⟨d1, run, post⟩ := (BarrierInsert.run input).run d ⟨pc, rfl⟩
  have keep := keep_gpr post (by decide) BarrierInsert.written
  refine ⟨d1, run, post.good, post.tick, post.minstret, by rw [post.pc]; rfl, ?_, post.output,
    (keep 2 (by decide) (by decide) (by decide)).trans b.stack,
    fun q noise out => post.frame q noise fun n hn => out n (BarrierInsert.written n hn), fun p => BarrierInsert.gpr_present post p⟩
  rw [post.memory, BarrierInsert.log, tblV, ptrV]; rfl

/-! ### Return and the fast-path run -/

/-- Returned to the caller. -/
structure Returned (ra sp : BitVec 64) (log : List WEntry) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  pc : after.σ.regs.get? Register.PC = some ra
  link : gprGet after.σ 1 = some ra
  stack : gprGet after.σ 2 = some sp
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1, 2, 10, 11, 12, 13, 14, 15], (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r
  present : GprPresent before.σ → GprPresent after.σ

theorem frame_pop32 (sp : BitVec 64) : sp + -32#64 + 32#64 = sp := by
  rw [BitVec.add_assoc]; simp

/-- **Restore `ra` and return** (`aa44`). -/
theorem return_run {ra sp : BitVec 64} {d : Config} (good : GoodState d.σ) (tick : d.tick < 2)
    (minstret : ∃ w, d.σ.regs.get? Register.minstret = some w) (code : Code.Caml_modifyLoaded d.σ.mem)
    (stack : gprGet d.σ 2 = some (sp + -32#64)) (raRead : ReadWindow ((sp + -32#64) + BitVec.ofNat 64 24) 8)
    (raWord : bytesT d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat 8 = ra) (aligned : ra.toNat % 4 = 0)
    (pc : PCAt BarrierReturn.pc d) :
    ∃ d1, Steps d d1 ∧ Returned ra sp [] d d1 := by
  have raV : bytesVal .ld (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat) = ra := by
    rw [read8_value]; exact raWord
  have input : BarrierReturn.Input (sp + -32#64) (Primitives.read8 d.σ.mem ((sp + -32#64) + BitVec.ofNat 64 24).toNat) d :=
    { good := good, tick := tick, minstret := minstret, code0 := code
      registers := ⟨stack, trivial⟩
      route := { read1 := raRead, pins1 := read8_pins _ _, control0 := by rw [raV]; exact aligned } }
  obtain ⟨d1, run, post⟩ := (BarrierReturn.run input).run d ⟨pc, rfl⟩
  have r := post.regs
  rw [BarrierReturn.registers] at r
  obtain ⟨r2, r1, -⟩ := r
  rw [frame_pop32] at r2
  rw [raV] at r1
  refine ⟨d1, run, post.good, post.tick, post.minstret, ?_, r1, r2, by rw [post.memory, BarrierReturn.log],
    post.output, fun q noise out => post.frame q noise fun n hn => out n (by
      have h := BarrierReturn.written n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega), fun p => BarrierReturn.gpr_present post p⟩
  rw [post.pc, BarrierReturn.endpoint _ _ (by rw [raV]; exact aligned), raV]

/-- The remembered set, as the insertion path needs it: its words at the
entry, apart from the major-slot stores, and the insertion apart from the
saved `ra` and above the code. -/
structure Remembered (sp ra slot v dom tbl ptr limit : BitVec 64) (c : Config) : Prop where
  table : Table dom tbl ptr limit c.σ.mem
  stored : ∀ x ∈ [(dom + BitVec.ofNat 64 104).toNat, (tbl + BitVec.ofNat 64 24).toNat,
    (tbl + BitVec.ofNat 64 32).toNat], ∀ e ∈ majorLog sp ra slot v, x + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ x
  /-- with room (the only case that inserts), the insertion misses the saved `ra` -/
  frameApart : ptr.toNat < limit.toNat → ∀ e ∈ insertLog tbl ptr slot,
    ((sp + -32#64) + BitVec.ofNat 64 24).toNat + 8 ≤ e.1 ∨ e.1 + e.2.1 ≤ ((sp + -32#64) + BitVec.ofNat 64 24).toNat
  /-- with room, the insertion lies above `caml_modify`'s code -/
  aboveCode : ptr.toNat < limit.toNat → ∀ e ∈ insertLog tbl ptr slot, 0x8000aa98 ≤ e.1

/-- The write barrier never needs to grow the remembered set. -/
def NoGrow (ys ye slot old v ptr limit : BitVec 64) : Prop :=
  YoungIn ys ye slot ∨ OldYoung ys ye old ∨ ¬ ValueYoung ys ye v ∨ ptr.toNat < limit.toNat

/-- Which stores the fast path made. -/
def FastLog (ys ye slot old v sp ra tbl ptr : BitVec 64) (log : List WEntry) : Prop :=
  (YoungIn ys ye slot ∧ log = youngLog slot v) ∨
  (¬ YoungIn ys ye slot ∧ (OldYoung ys ye old ∨ ¬ ValueYoung ys ye v) ∧ log = majorLog sp ra slot v) ∨
  (¬ YoungIn ys ye slot ∧ ¬ OldYoung ys ye old ∧ ValueYoung ys ye v ∧
    log = majorLog sp ra slot v ++ insertLog tbl ptr slot)

/-- The fast path's outcome. -/
structure FastDone (ys ye slot old v sp ra tbl ptr : BitVec 64) (before after : Config) where
  log : List WEntry
  which : FastLog ys ye slot old v sp ra tbl ptr log
  returned : Returned ra sp log before after

theorem frame_gpr {before after : MState} {W : List Nat} (keys : KeysOK W)
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ W, (gprReg n == r) = false) →
      after.regs.get? r = before.regs.get? r)
    (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (out : n ∉ W) : gprGet after n = gprGet before n := by
  apply gprGet_of_frame n lower upper (gpr_avoids_noise n (by omega) lower) ?_ frame
  intro m hm
  have bounds := keys m hm
  exact gprReg_beq_false m (by omega) n (by omega) bounds.1 lower (fun e => out (e ▸ hm))

theorem code_after {log : List WEntry} {m : Std.ExtHashMap Nat (BitVec 8)} (code : Code.Caml_modifyLoaded m)
    (above : ∀ e ∈ log, 0x8000aa98 ≤ e.1) : Code.Caml_modifyLoaded (writeLog m log) :=
  image_writeLog Code.caml_modify_transport code above

/-- The saved `ra` survives the slot store and an apart insertion. -/
theorem ra_saved {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c)
    {log : List WEntry} (apart : ∀ x ∈ log, ((sp + -32#64) + BitVec.ofNat 64 24).toNat + 8 ≤ x.1 ∨
      x.1 + x.2.1 ≤ ((sp + -32#64) + BitVec.ofNat 64 24).toNat) :
    bytesT (writeLog (writeLog c.σ.mem (majorLog sp ra slot v)) log) ((sp + -32#64) + BitVec.ofNat 64 24).toNat 8
      = ra := by
  rw [bytesT_writeLog_out _ (outLRange_of_forall apart)]
  apply word_writeLog_at _ _ 0 _ _ rfl
  apply outLRange_of_forall
  intro x hx
  simp only [majorLog, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  rw [slot_exact]
  rcases e.slotFrame with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem writeLog_nil_eq (m : Std.ExtHashMap Nat (BitVec 8)) : writeLog m [] = m := rfl

theorem ra_saved_major {slot v ra sp dom ys ye old} {c : Config} (e : Entry slot v ra sp dom ys ye old c) :
    bytesT (writeLog c.σ.mem (majorLog sp ra slot v)) ((sp + -32#64) + BitVec.ofNat 64 24).toNat 8 = ra := by
  have h := ra_saved e (log := []) nofun
  rwa [writeLog_nil_eq] at h

/-- Register frames compose through a middle state. -/
theorem frame_chain {a b d : MState} {W W1 W2 : List Nat}
    (h1 : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ W1, (gprReg n == r) = false) →
      b.regs.get? r = a.regs.get? r)
    (h2 : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ W2, (gprReg n == r) = false) →
      d.regs.get? r = b.regs.get? r)
    (s1 : ∀ n ∈ W1, n ∈ W) (s2 : ∀ n ∈ W2, n ∈ W) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) → (∀ n ∈ W, (gprReg n == r) = false) →
      d.regs.get? r = a.regs.get? r :=
  fun r noise out => (h2 r noise fun n hn => out n (s2 n hn)).trans (h1 r noise fun n hn => out n (s1 n hn))

/-- **The write barrier without growing the remembered set.** -/
theorem barrier_fast {slot v ra sp dom ys ye old tbl ptr limit} {c : Config}
    (e : Entry slot v ra sp dom ys ye old c) (rem : Remembered sp ra slot v dom tbl ptr limit c)
    (noGrow : NoGrow ys ye slot old v ptr limit) :
    FnSummary BarrierYoung.pc (fun d => d = c)
      (fun after => Nonempty (FastDone ys ye slot old v sp ra tbl ptr c after)) := by
  constructor
  rintro d ⟨pc, rfl⟩
  have all : ∀ n ∈ [1, 2, 10, 11, 12, 13, 14, 15], n ∈ [1, 2, 10, 11, 12, 13, 14, 15] := fun _ h => h
  by_cases young : YoungIn ys ye slot
  · obtain ⟨d1, run, Y⟩ := (young_run e young).run d ⟨pc, rfl⟩
    have keep := frame_gpr (by decide) Y.frame
    exact ⟨d1, run, ⟨youngLog slot v, Or.inl ⟨young, rfl⟩,
      ⟨Y.good, Y.tick, Y.minstret, Y.pc, (keep 1 (by decide) (by decide) (by decide)).trans e.raReg,
        (keep 2 (by decide) (by decide) (by decide)).trans e.stackReg, Y.memory, Y.output,
        fun r noise out => Y.frame r noise fun n hn => out n (by
          have h := BarrierYoung.written n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega), fun p => Y.present p⟩⟩⟩
  obtain ⟨d1, run1, M⟩ := (major_head e young).run d ⟨pc, rfl⟩
  obtain ⟨d2, run2, O⟩ := (old_run e M).run d1 ⟨M.pc, rfl⟩
  have sub1 : ∀ n ∈ [13, 14, 15], n ∈ [1, 2, 10, 11, 12, 13, 14, 15] := by decide
  have sub2 : ∀ n ∈ [2, 10, 11, 12, 14, 15], n ∈ [1, 2, 10, 11, 12, 13, 14, 15] := by decide
  have sub3 : ∀ n ∈ [10, 12, 13, 14], n ∈ [1, 2, 10, 11, 12, 13, 14, 15] := by decide
  rcases O with ⟨oldYoung, R⟩ | ⟨notOld, B⟩
  · have mem2 : d2.σ.mem = writeLog d.σ.mem (majorLog sp ra slot v) := by rw [R.memory, M.memory]
    obtain ⟨d3, run3, T⟩ := return_run (ra := ra) R.good R.tick R.minstret
      (by rw [mem2]; exact code_after e.code e.aboveCode) R.regs.1 e.frameWrite.read
      (by rw [mem2]; exact ra_saved_major e) e.raAligned R.pc
    exact ⟨d3, run1.trans (run2.trans run3), ⟨majorLog sp ra slot v,
      Or.inr (Or.inl ⟨young, Or.inl oldYoung, rfl⟩),
      ⟨T.good, T.tick, T.minstret, T.pc, T.link, T.stack, by rw [T.memory, mem2, writeLog_nil_eq], by
        rw [T.output, R.output, M.output],
        frame_chain (frame_chain M.frame R.frame sub1 sub2) T.frame
          (fun n h => h) (fun n h => h), fun p => T.present (R.present (M.present p))⟩⟩⟩
  · have mem2 : d2.σ.mem = writeLog d.σ.mem (majorLog sp ra slot v) := by rw [B.memory, M.memory]
    obtain ⟨h14, h15, h13, h2, -, -⟩ := B.regs
    have body : Body slot v (sp + -32#64) dom ys ye d2 :=
      { good := B.good, tick := B.tick, minstret := B.minstret
        code := by rw [mem2]; exact code_after e.code e.aboveCode
        value := h14, slot := h15, state := h13, stack := h2
        domain := by rw [mem2]; exact e.domainBody }
    by_cases valueYoung : ValueYoung ys ye v
    · have room : ptr.toNat < limit.toNat := by
        rcases noGrow with h | h | h | h
        · exact absurd h young
        · exact absurd h notOld
        · exact absurd valueYoung h
        · exact h
      obtain ⟨d3, run3, V⟩ := value_insert body (by rw [mem2]; exact rem.table.writeLog rem.stored)
        B.pc valueYoung room
      have mem3 : d3.σ.mem = writeLog (writeLog d.σ.mem (majorLog sp ra slot v)) (insertLog tbl ptr slot) := by
        rw [V.memory, mem2]
      obtain ⟨d4, run4, T⟩ := return_run (ra := ra) V.good V.tick V.minstret
        (by rw [mem3]; exact code_after (code_after e.code e.aboveCode) (rem.aboveCode room)) V.stack
        e.frameWrite.read (by rw [mem3]; exact ra_saved e (rem.frameApart room)) e.raAligned V.pc
      exact ⟨d4, run1.trans (run2.trans (run3.trans run4)), ⟨majorLog sp ra slot v ++ insertLog tbl ptr slot,
        Or.inr (Or.inr ⟨young, notOld, valueYoung, rfl⟩),
        ⟨T.good, T.tick, T.minstret, T.pc, T.link, T.stack, by rw [T.memory, mem3, writeLog_nil_eq, writeLog_append], by
          rw [T.output, V.output, B.output, M.output],
          frame_chain (frame_chain (frame_chain M.frame B.frame sub1 sub2) V.frame (fun n h => h) sub3) T.frame
            (fun n h => h) (fun n h => h), fun p => T.present (V.present (B.present (M.present p)))⟩⟩⟩
    · obtain ⟨d3, run3, V⟩ := value_skip body B.pc valueYoung
      have mem3 : d3.σ.mem = writeLog d.σ.mem (majorLog sp ra slot v) := by rw [V.memory, mem2, writeLog_nil_eq]
      obtain ⟨d4, run4, T⟩ := return_run (ra := ra) V.good V.tick V.minstret
        (by rw [mem3]; exact code_after e.code e.aboveCode) V.stack
        e.frameWrite.read (by rw [mem3]; exact ra_saved_major e) e.raAligned V.pc
      exact ⟨d4, run1.trans (run2.trans (run3.trans run4)), ⟨majorLog sp ra slot v,
        Or.inr (Or.inl ⟨young, Or.inr valueYoung, rfl⟩),
        ⟨T.good, T.tick, T.minstret, T.pc, T.link, T.stack, by rw [T.memory, mem3, writeLog_nil_eq], by
          rw [T.output, V.output, B.output, M.output],
          frame_chain (frame_chain (frame_chain M.frame B.frame sub1 sub2) V.frame (fun n h => h) sub3) T.frame
            (fun n h => h) (fun n h => h), fun p => T.present (V.present (B.present (M.present p)))⟩⟩⟩

end OCaml.Vm.Gc.Barrier
