import OCaml.Vm.Primitives.Channel.OutList
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Gc.CustomMem
import OCaml.Vm.Gc.Readback

/-!
# `caml_ml_out_channels_list`'s list walk: visiting a record

The walk's head (`0x80016094`) holds the current record in `s0`. It tests
`max` (`+32`, `NULL` for an output channel) and the managed flag
(`flags & 4`, `+68`). A record failing either test is skipped (`next`,
`+48`), back to the head or, at the list's end, to `leave` (`0x80016118`).
A record passing both reaches `caml_alloc_channel`'s inlined body
(`0x800160a8`). Both phases read memory and write only `a5` and `s0`.
-/

namespace OCaml.Vm.Primitives.Channel.OutList
open Vsa.Machine Vsa.Sim LeanRV64DExecutable
set_option autoImplicit false

/-- `&Caml_state`, which the walk keeps in `a3`. -/
def stateAddr : BitVec 64 := 2147896584#64

/-- The walk's loop head, its exit, and the inlined `caml_alloc_channel`. -/
def headPc : BitVec 64 := 0x80016094#64
def exitPc : BitVec 64 := 0x80016118#64
def allocPc : BitVec 64 := 0x800160a8#64

/-- A record's `next` word. -/
def nextRec (m : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64) : BitVec 64 :=
  bytesT m (p + 48#64).toNat 8

/-- The next pc after a record: the head, or `leave` at the list's end. -/
def afterPc (next : BitVec 64) : BitVec 64 := if next = 0#64 then exitPc else headPc

/-- A record is listed: an output channel (`max == NULL`) managed by the GC. -/
def Listed (m : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64) : Prop :=
  bytesT m (p + 32#64).toNat 8 = 0#64 ∧ bytesVal .lw (read8 m (p + 68#64).toNat) &&& 4#64 ≠ 0#64

/-- The registers the walk keeps at its head: the frame `sp`, the record in
`s0`, `a0`, `&Caml_state` and the saved `local_roots`. -/
structure HeadRegs (sp p a0 roots : BitVec 64) (d : Config) : Prop where
  sp : gpr d 2 = some sp
  record : gpr d 8 = some p
  a0 : gpr d 10 = some a0
  state : gpr d 13 = some stateAddr
  roots : gpr d 14 = some roots

/-- The head's register file for the generated blocks. -/
def headR (ra sp p a0 roots : BitVec 64) : Nat → BitVec 64 := fun n =>
  if n = 1 then ra else if n = 2 then sp else if n = 8 then p else if n = 10 then a0
  else if n = 13 then stateAddr else roots

/-- The record's words the walk reads lie in RAM away from `tohost`. -/
structure RecordWindows (p : BitVec 64) : Prop where
  max : ReadWindow (p + 32#64) 8
  next : ReadWindow (p + 48#64) 8
  flags : ReadWindow (p + 68#64) 4

theorem HeadRegs.holds {ra sp p a0 roots : BitVec 64} {d : Config} (h : HeadRegs sp p a0 roots d) :
    GHolds d.σ [(2, headR ra sp p a0 roots 2), (8, headR ra sp p a0 roots 8),
      (10, headR ra sp p a0 roots 10), (13, headR ra sp p a0 roots 13), (14, headR ra sp p a0 roots 14)] :=
  ⟨h.sp, h.record, h.a0, h.state, h.roots, True.intro⟩

/-- A phase's machine facts carry the head's leaf input. -/
theorem _root_.OCaml.Vm.Primitives.EffectPost.leafInput {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {before after : Config}
    {pc value ra : BitVec 64} (post : EffectPost writes mem before pc value after) (keys : KeysOK writes)
    (one : 1 ∉ writes) (leaf : LeafInput ra before) : LeafInput ra after :=
  ⟨post.good, post.image, post.minstret,
    (post.gpr_frame keys 1 (by decide) (by decide) one).trans leaf.raReg, leaf.aligned, post.tick⟩

/-- The head's registers after a phase writing only `a5`, with `s0` advanced. -/
theorem HeadRegs.advance {writes : List Nat} {mem : Std.ExtHashMap Nat (BitVec 8)} {before after : Config}
    {pc value sp p q a0 roots : BitVec 64} (h : HeadRegs sp p a0 roots before)
    (post : EffectPost writes mem before pc value after) (keys : KeysOK writes)
    (kept : ∀ n ∈ [2, 10, 13, 14], n ∉ writes) (record : gpr after 8 = some q) : HeadRegs sp q a0 roots after :=
  ⟨(post.gpr_frame keys 2 (by decide) (by decide) (kept 2 (by simp))).trans h.sp, record,
    (post.gpr_frame keys 10 (by decide) (by decide) (kept 10 (by simp))).trans h.a0,
    (post.gpr_frame keys 13 (by decide) (by decide) (kept 13 (by simp))).trans h.state,
    (post.gpr_frame keys 14 (by decide) (by decide) (kept 14 (by simp))).trans h.roots⟩

/-- The skip block from `0x8001608c`: `s0 := next`, to the head or `leave`. -/
theorem skip_step {ra sp p a0 roots : BitVec 64} {d : Config} (leaf : LeafInput ra d)
    (regs : HeadRegs sp p a0 roots d) (pc : pcOf d = some 0x8001608c#64) (w : RecordWindows p) :
    ∃ d', Steps d d' ∧ EffectPost [8] d.σ.mem d (afterPc (nextRec d.σ.mem p)) a0 d' ∧
      HeadRegs sp (nextRec d.σ.mem p) a0 roots d' := by
  let R := headR ra sp p a0 roots
  have value : bytesVal .ld (read8 d.σ.mem (R 8 + 48#64).toNat) = nextRec d.σ.mem p := read8_value _ _
  by_cases last : nextRec d.σ.mem p = 0#64
  · obtain ⟨d', run, post⟩ := (skipLast_fast d R leaf regs.holds w.next (by
      simp only [skipLast_loads, List.getD_cons_zero]; rw [value, last]; decide)).run d ⟨pc, rfl⟩
    have hrec : gpr d' 8 = some (nextRec d.σ.mem p) := by
      rw [← value]; exact gholds_lookup _ post.regs rfl
    refine ⟨d', run, ?_, regs.advance post.toEffectPost (by decide) (by decide) hrec⟩
    simp only [afterPc, last, ↓reduceIte]
    exact post.toEffectPost
  · obtain ⟨d', run, post⟩ := (skipNext_fast d R leaf regs.holds w.next (by
      simp only [skipNext_loads, List.getD_cons_zero]; rw [value]; simpa [guardB] using last)).run d ⟨pc, rfl⟩
    have hrec : gpr d' 8 = some (nextRec d.σ.mem p) := by
      rw [← value]; exact gholds_lookup _ post.regs rfl
    refine ⟨d', run, ?_, regs.advance post.toEffectPost (by decide) (by decide) hrec⟩
    simp only [afterPc, last, ↓reduceIte]
    exact post.toEffectPost

/-- **An unlisted record is skipped**: from the head on `p`, to the head on
`next` (or `leave` at the end), reading memory and writing `a5` and `s0`. -/
theorem visit_skip {ra sp p a0 roots : BitVec 64} {d : Config} (leaf : LeafInput ra d)
    (regs : HeadRegs sp p a0 roots d) (pc : pcOf d = some headPc) (w : RecordWindows p)
    (skip : ¬ Listed d.σ.mem p) :
    ∃ d', Steps d d' ∧ EffectPost [8, 15] d.σ.mem d (afterPc (nextRec d.σ.mem p)) a0 d' ∧
      HeadRegs sp (nextRec d.σ.mem p) a0 roots d' := by
  let R := headR ra sp p a0 roots
  have maxv : bytesVal .ld (read8 d.σ.mem (R 8 + 32#64).toNat) = bytesT d.σ.mem (p + 32#64).toNat 8 :=
    read8_value _ _
  by_cases out : bytesT d.σ.mem (p + 32#64).toNat 8 = 0#64
  · have flags : bytesVal .lw (read8 d.σ.mem (p + 68#64).toNat) &&& 4#64 = 0#64 :=
      Classical.byContradiction fun ne => skip ⟨out, ne⟩
    obtain ⟨d1, run1, p1⟩ := (testOut_fast d R leaf regs.holds w.max (by
      simp only [testOut_loads, List.getD_cons_zero]; rw [maxv, out]; decide)).run d ⟨pc, rfl⟩
    have r1 := regs.advance p1.toEffectPost (by decide) (by decide) (gholds_lookup _ p1.regs rfl)
    obtain ⟨d2, run2, p2⟩ := (flagsSkip_fast d1 R (p1.toEffectPost.leafInput (by decide) (by decide) leaf)
      r1.holds w.flags (by
        simp only [flagsSkip_loads, List.getD_cons_zero]; rw [p1.memory]; simp only [writeLog, List.foldl_nil]
        change guardB .BEQ (bytesVal .lw (read8 d.σ.mem (p + 68#64).toNat) &&& 4#64) 0#64 = true
        rw [flags]; decide)).run d1 ⟨p1.pc, rfl⟩
    have r2 := r1.advance p2.toEffectPost (by decide) (by decide) (gholds_lookup _ p2.regs rfl)
    have m2 : d2.σ.mem = d.σ.mem := by rw [p2.memory, p1.memory]; rfl
    obtain ⟨d3, run3, p3, r3⟩ := skip_step (p2.toEffectPost.leafInput (by decide) (by decide)
      (p1.toEffectPost.leafInput (by decide) (by decide) leaf)) r2 p2.pc w
    rw [m2] at p3 r3
    refine ⟨d3, run1.trans (run2.trans run3), ?_, r3⟩
    have e12 := p1.toEffectPost.trans p2.toEffectPost
    rw [show writeLog d1.σ.mem [] = d.σ.mem by rw [p1.memory]; rfl] at e12
    exact ((e12.trans p3).widen (by decide))
  · obtain ⟨d1, run1, p1⟩ := (testSkip_fast d R leaf regs.holds w.max (by
      simp only [testSkip_loads, List.getD_cons_zero]; rw [maxv]; simpa [guardB] using out)).run d ⟨pc, rfl⟩
    have r1 := regs.advance p1.toEffectPost (by decide) (by decide) (gholds_lookup _ p1.regs rfl)
    have m1 : d1.σ.mem = d.σ.mem := by rw [p1.memory]; rfl
    obtain ⟨d2, run2, p2, r2⟩ := skip_step (p1.toEffectPost.leafInput (by decide) (by decide) leaf) r1 p1.pc w
    rw [m1] at p2 r2
    refine ⟨d2, run1.trans run2, ?_, r2⟩
    exact ((p1.toEffectPost.trans p2).widen (by decide))

/-- **A listed record reaches `caml_alloc_channel`** (`0x800160a8`), reading
memory and writing `a5`. -/
theorem visit_go {ra sp p a0 roots : BitVec 64} {d : Config} (leaf : LeafInput ra d)
    (regs : HeadRegs sp p a0 roots d) (pc : pcOf d = some headPc) (w : RecordWindows p)
    (go : Listed d.σ.mem p) :
    ∃ d', Steps d d' ∧ EffectPost [15] d.σ.mem d allocPc a0 d' ∧ HeadRegs sp p a0 roots d' := by
  let R := headR ra sp p a0 roots
  have maxv : bytesVal .ld (read8 d.σ.mem (R 8 + 32#64).toNat) = bytesT d.σ.mem (p + 32#64).toNat 8 :=
    read8_value _ _
  obtain ⟨d1, run1, p1⟩ := (testOut_fast d R leaf regs.holds w.max (by
    simp only [testOut_loads, List.getD_cons_zero]; rw [maxv, go.1]; decide)).run d ⟨pc, rfl⟩
  have r1 := regs.advance p1.toEffectPost (by decide) (by decide) (gholds_lookup _ p1.regs rfl)
  obtain ⟨d2, run2, p2⟩ := (flagsGo_fast d1 R (p1.toEffectPost.leafInput (by decide) (by decide) leaf)
    r1.holds w.flags (by
      simp only [flagsGo_loads, List.getD_cons_zero]; rw [p1.memory]; simp only [writeLog, List.foldl_nil]
      change guardB .BEQ (bytesVal .lw (read8 d.σ.mem (p + 68#64).toNat) &&& 4#64) 0#64 = false
      simpa [guardB] using go.2)).run d1 ⟨p1.pc, rfl⟩
  have r2 := r1.advance p2.toEffectPost (by decide) (by decide) (gholds_lookup _ p2.regs rfl)
  refine ⟨d2, run1.trans run2, ?_, r2⟩
  have e12 := p1.toEffectPost.trans p2.toEffectPost
  rw [show writeLog d1.σ.mem [] = d.σ.mem by rw [p1.memory]; rfl] at e12
  exact e12.widen (by decide)

/-- The record's reference count after `caml_alloc_channel`'s increment. -/
def refcount (m : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .lw (read8 m (p + 64#64).toNat) + 1#64) 31 0)

/-- The stores before `caml_alloc_custom_mem`: the refcount and the saved
`local_roots` (`sp + 8`). -/
def enterLog (m : Std.ExtHashMap Nat (BitVec 8)) (sp p roots : BitVec 64) : List WEntry :=
  [((p + 64#64).toNat, 4, refcount m p), ((sp + 8#64).toNat, 8, roots)]

/-- The walk's call site of `caml_alloc_custom_mem`, under its 128-byte frame. -/
def walkSite (sp p : BitVec 64) : Gc.CustomMemSite := ⟨call_call.link, sp, p, 128⟩

/-- **`caml_alloc_channel`'s entry, up to the call of `caml_alloc_custom_mem`**:
the refcount and `local_roots` stores, then the call's arguments. -/
theorem alloc_enter {ra sp p a0 roots : BitVec 64} {d : Config} (leaf : LeafInput ra d)
    (regs : HeadRegs sp p a0 roots d) (pc : pcOf d = some allocPc)
    (wRef : WriteWindow (p + 64#64) 4) (wSlot : WriteWindow (sp + 8#64) 8)
    (outside : ImageOutside (enterLog d.σ.mem sp p roots)) :
    ∃ f, Steps d f ∧ EffectPost [10, 11, 12, 15, 1] (writeLog d.σ.mem (enterLog d.σ.mem sp p roots)) d
        Gc.customMemEntry Gc.channelOps f ∧
      gprGet f.σ 1 = some call_call.link ∧ GHolds f.σ (walkSite sp p).args := by
  let R := headR ra sp p a0 roots
  obtain ⟨d1, run1, p1⟩ := (call_fast d R leaf ⟨regs.sp, regs.record, regs.state, regs.roots, True.intro⟩
    wRef.read wRef wSlot outside).run d ⟨pc, rfl⟩
  obtain ⟨f, run2, p2⟩ := (call_registers_summary call_call_shape call_call_decode d1 (call_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret _ p1.regs (by change KeysOK [10, 11, 15, 12, 2, 8, 13, 14]; decide)
    (by simp only [KeysAvoidRa, keysG, call_regs]; decide)
    (by rfl)).run d1 ⟨p1.pc, rfl⟩
  refine ⟨f, run1.trans run2, ?_, gholds_lookup _ p2.regs (by rfl), ?_⟩
  · have e := p1.toEffectPost.trans p2.toEffectPost
    rw [p1.memory, call_call_target] at e
    exact e
  · exact holds_project p2.regs (by simp [walkSite, Gc.CustomMemSite.args, Gc.channelOps, Gc.channelMem, call_regs,
      lookupG, R, headR])

/-- An offset address without wrap-around. -/
theorem off_toNat {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- `caml_alloc_small`'s entry. -/
def smallEntry : BitVec 64 := 0x8000c0b8#64

/-- After `caml_alloc_custom_mem`: the custom block's data word (the record),
then the CAMLlocal `chan` (`sp + 40`) and `tail` (`sp + 32`, the old `res`). -/
def consEnterLog (m : Std.ExtHashMap Nat (BitVec 8)) (sp p v : BitVec 64) : List WEntry :=
  [((v + 8#64).toNat, 8, p), ((sp + 40#64).toNat, 8, v), ((sp + 32#64).toNat, 8, bytesT m (sp + 24#64).toNat 8)]

/-- **From `caml_alloc_custom_mem`'s return to the call of
`caml_alloc_small(2, Tag_cons)`**, with the custom block `v` below the frame. -/
theorem cons_enter {r sp p v : BitVec 64} {d : Config} (leaf : LeafInput r d)
    (h2 : gpr d 2 = some sp) (h8 : gpr d 8 = some p) (h10 : gpr d 10 = some v)
    (pc : pcOf d = some call_call.link)
    (wData : WriteWindow (v + 8#64) 8) (wRes : WriteWindow (sp + 24#64) 8)
    (wTail : WriteWindow (sp + 32#64) 8) (wChan : WriteWindow (sp + 40#64) 8)
    (below : v.toNat + 16 ≤ sp.toNat) (spFit : sp.toNat + 128 ≤ 2 ^ 32)
    (outside : ImageOutside (consEnterLog d.σ.mem sp p v)) :
    ∃ g, Steps d g ∧ EffectPost [10, 11, 15, 1] (writeLog d.σ.mem (consEnterLog d.σ.mem sp p v)) d smallEntry 2#64 g ∧
      gprGet g.σ 1 = some cons_call.link ∧ GHolds g.σ [(10, 2#64), (11, 0#64), (2, sp), (8, p)] := by
  let R : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp else if n = 8 then p else v
  have hlog : consLog R (cons_loads d.σ.mem R) = consEnterLog d.σ.mem sp p v := by
    rw [show consLog R (cons_loads d.σ.mem R) = [((v + 8#64).toNat, 8, p), ((sp + 40#64).toNat, 8, v),
      ((sp + 32#64).toNat, 8, bytesVal .ld (read8 d.σ.mem (sp + 24#64).toNat))] from rfl, read8_value]; rfl
  have apart : OutLRange ((consLog R (cons_loads d.σ.mem R)).take 1) (R 2 + 24#64).toNat 8 := by
    rw [hlog]
    show OutLRange [((v + 8#64).toNat, 8, p)] (sp + 24#64).toNat 8
    simp only [OutLRange, and_true]
    rw [off_toNat (k := 8) (by omega), off_toNat (k := 24) (by omega)]; omega
  obtain ⟨d1, run1, p1⟩ := (cons_fast d R leaf ⟨h2, h8, h10, True.intro⟩ wData wRes.read apart wChan wTail
    (by rw [hlog]; exact outside)).run d ⟨pc, rfl⟩
  obtain ⟨g, run2, p2⟩ := (call_registers_summary cons_call_shape cons_call_decode d1 (cons_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret _ p1.regs (by change KeysOK [10, 11, 15, 2, 8]; decide)
    (by simp only [KeysAvoidRa, keysG, cons_regs]; decide) (by rfl)).run d1 ⟨p1.pc, rfl⟩
  refine ⟨g, run1.trans run2, ?_, gholds_lookup _ p2.regs (by rfl),
    holds_project p2.regs (by simp [cons_regs, lookupG, R])⟩
  have e := p1.toEffectPost.trans p2.toEffectPost
  rw [p1.memory, hlog, cons_call_target] at e
  exact e

/-- The link block's stores: `res := cell` and the cell's `car` (the chan). -/
def linkStoreLog (m : Std.ExtHashMap Nat (BitVec 8)) (sp cell : BitVec 64) : List WEntry :=
  [((sp + 24#64).toNat, 8, cell), (cell.toNat, 8, bytesT m (sp + 40#64).toNat 8)]

/-- The tail block's store: the cell's `cdr` (the old `res`, in `tail`). -/
def tailStoreLog (m : Std.ExtHashMap Nat (BitVec 8)) (cell : BitVec 64) (sp : BitVec 64) : List WEntry :=
  [((cell + 8#64).toNat, 8, bytesT m (sp + 32#64).toNat 8)]

/-- **From `caml_alloc_small`'s return to the next record**: the cons cell's
fields, `res := cell`, `s0 := next`, back to the head or to `leave`. -/
theorem link_step {r sp p cell : BitVec 64} {d : Config} (leaf : LeafInput r d)
    (h2 : gpr d 2 = some sp) (h8 : gpr d 8 = some p) (h10 : gpr d 10 = some cell)
    (pc : pcOf d = some cons_call.link) (wNext : ReadWindow (p + 48#64) 8)
    (wRes : WriteWindow (sp + 24#64) 8) (wRoots : ReadWindow (sp + 8#64) 8)
    (wTail : ReadWindow (sp + 32#64) 8) (wChan : ReadWindow (sp + 40#64) 8)
    (wCar : WriteWindow cell 8) (wCdr : WriteWindow (cell + 8#64) 8)
    (below : cell.toNat + 16 ≤ sp.toNat) (spFit : sp.toNat + 128 ≤ 2 ^ 32)
    (nextLink : OutLRange (linkStoreLog d.σ.mem sp cell) (p + 48#64).toNat 8)
    (nextTail : OutLRange (tailStoreLog d.σ.mem cell sp) (p + 48#64).toNat 8)
    (outLink : ImageOutside (linkStoreLog d.σ.mem sp cell))
    (outTail : ImageOutside (tailStoreLog d.σ.mem cell sp)) :
    ∃ d', Steps d d' ∧
      EffectPost [12, 14, 15, 8, 13]
        (writeLog (writeLog d.σ.mem (linkStoreLog d.σ.mem sp cell)) (tailStoreLog d.σ.mem cell sp)) d
        (afterPc (nextRec d.σ.mem p)) cell d' ∧
      HeadRegs sp (nextRec d.σ.mem p) cell (bytesT d.σ.mem (sp + 8#64).toNat 8) d' := by
  let R : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp else if n = 8 then p else cell
  have s8 := off_toNat (x := sp) (k := 8) (by omega)
  have s24 := off_toNat (x := sp) (k := 24) (by omega)
  have s32 := off_toNat (x := sp) (k := 32) (by omega)
  have c8 := off_toNat (x := cell) (k := 8) (by omega)
  have hlog : linkLog R (link_loads d.σ.mem R) = linkStoreLog d.σ.mem sp cell := by
    rw [show linkLog R (link_loads d.σ.mem R) = [((sp + 24#64).toNat, 8, cell),
      (cell.toNat, 8, bytesVal .ld (read8 d.σ.mem (sp + 40#64).toNat))] from rfl, read8_value]; rfl
  obtain ⟨d1, run1, p1⟩ := (link_fast d R leaf ⟨h2, h8, h10, True.intro⟩ wChan wRes wRoots
    (by rw [hlog]; show OutLRange [((sp + 24#64).toNat, 8, cell)] (sp + 8#64).toNat 8
        simp only [OutLRange, and_true]; omega)
    wCar wTail
    (by rw [hlog]
        show OutLRange [((sp + 24#64).toNat, 8, cell), (cell.toNat, 8, bytesT d.σ.mem (sp + 40#64).toNat 8)]
          (sp + 32#64).toNat 8
        simp only [OutLRange, and_true]; omega)
    (by rw [hlog]; exact outLink)).run d ⟨pc, rfl⟩
  have m1 : d1.σ.mem = writeLog d.σ.mem (linkStoreLog d.σ.mem sp cell) := by rw [p1.memory, hlog]
  let tailv := bytesVal .ld (read8 d.σ.mem (sp + 32#64).toNat)
  let roots := bytesVal .ld (read8 d.σ.mem (sp + 8#64).toNat)
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then r else if n = 2 then sp else if n = 8 then p
    else if n = 10 then cell else if n = 12 then tailv else roots
  have regs1 : GHolds d1.σ [(2, R1 2), (8, R1 8), (10, R1 10), (12, R1 12), (14, R1 14)] :=
    holds_project p1.regs (by simp [link_regs, link_loads, lookupG, R, R1, tailv, roots])
  have leaf1 : LeafInput (R1 1) d1 := p1.toEffectPost.leafInput (by decide) (by decide) leaf
  have hcell : bytesVal .ld (read8 d1.σ.mem (R1 2 + 24#64).toNat) = cell := by
    rw [read8_value, m1]
    exact Gc.word_writeLog_at _ _ 0 _ cell rfl (by
      show OutLRange [(cell.toNat, 8, bytesT d.σ.mem (sp + 40#64).toNat 8)] (sp + 24#64).toNat 8
      simp only [OutLRange, and_true]; omega)
  have hnext : bytesVal .ld (read8 d1.σ.mem (R1 8 + 48#64).toNat) = nextRec d.σ.mem p := by
    rw [read8_value, m1]; exact bytesT_writeLog_out _ nextLink
  have htail : ∀ loads : List (List (BitVec 8)), loads.getD 0 [] = read8 d1.σ.mem (R1 2 + 24#64).toNat →
      [((bytesVal .ld (loads.getD 0 []) + 8#64).toNat, 8, R1 12)] = tailStoreLog d.σ.mem cell sp := by
    intro loads e
    rw [e, hcell]; simp only [tailStoreLog, R1, tailv, read8_value]; rfl
  have win1 : WriteWindow (bytesVal .ld (read8 d1.σ.mem (R1 2 + 24#64).toNat) + 8#64) 8 := by rw [hcell]; exact wCdr
  have hlog2 : ∀ loads : List (List (BitVec 8)), loads.getD 0 [] = read8 d1.σ.mem (R1 2 + 24#64).toNat →
      ((bytesVal .ld (loads.getD 0 []) + 8#64).toNat, 8, R1 12) :: [] = tailStoreLog d.σ.mem cell sp := htail
  have hroots : bytesVal .ld (read8 d.σ.mem (sp + 8#64).toNat) = bytesT d.σ.mem (sp + 8#64).toNat 8 := read8_value _ _
  have finish : ∀ {d2 : Config} {pc' : BitVec 64} {regs' : GRegs},
      WriteRegistersPost [8, 13, 15] (tailStoreLog d.σ.mem cell sp) d1 pc' (R1 10) regs' d2 →
      lookupG 8 regs' = some (nextRec d.σ.mem p) → lookupG 13 regs' = some stateAddr →
      EffectPost [12, 14, 15, 8, 13]
        (writeLog (writeLog d.σ.mem (linkStoreLog d.σ.mem sp cell)) (tailStoreLog d.σ.mem cell sp)) d pc' cell d2 ∧
      HeadRegs sp (nextRec d.σ.mem p) cell (bytesT d.σ.mem (sp + 8#64).toNat 8) d2 := by
    intro d2 pc' regs' p2 l8 l13
    have e := p1.toEffectPost.trans p2.toEffectPost
    rw [m1] at e
    refine ⟨e.widen (by decide), ?_, gholds_lookup _ p2.regs l8, ?_, gholds_lookup _ p2.regs l13, ?_⟩
    · exact (p2.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans
        (gholds_lookup _ p1.regs (by rfl))
    · exact (p2.toEffectPost.gpr_frame (by decide) 10 (by decide) (by decide) (by decide)).trans
        (gholds_lookup _ p1.regs (by rfl))
    · rw [p2.toEffectPost.gpr_frame (by decide) 14 (by decide) (by decide) (by decide), ← hroots]
      exact gholds_lookup _ p1.regs (by rfl)
  by_cases last : nextRec d.σ.mem p = 0#64
  · obtain ⟨d2, run2, p2⟩ := (tailLast_fast d1 R1 leaf1 regs1 wRes.read win1 wNext
      (by rw [show (tailLastLog R1 (tailLast_loads d1.σ.mem R1)).take 1 = tailStoreLog d.σ.mem cell sp from
            hlog2 _ rfl]; exact nextTail)
      (by rw [show tailLastLog R1 (tailLast_loads d1.σ.mem R1) = tailStoreLog d.σ.mem cell sp from hlog2 _ rfl]
          exact outTail)
      (by simp only [tailLast_loads, List.getD_cons_succ, List.getD_cons_zero]; rw [hnext, last]; decide)).run d1
      ⟨p1.pc, rfl⟩
    rw [show tailLastLog R1 (tailLast_loads d1.σ.mem R1) = tailStoreLog d.σ.mem cell sp from hlog2 _ rfl] at p2
    obtain ⟨e, h⟩ := finish p2 (by show some (bytesVal .ld (read8 d1.σ.mem (R1 8 + 48#64).toNat)) = _; rw [hnext]) (by rfl)
    refine ⟨d2, run1.trans run2, ?_, h⟩
    simp only [afterPc, last, ↓reduceIte]; exact e
  · obtain ⟨d2, run2, p2⟩ := (tailNext_fast d1 R1 leaf1 regs1 wRes.read win1 wNext
      (by rw [show (tailNextLog R1 (tailNext_loads d1.σ.mem R1)).take 1 = tailStoreLog d.σ.mem cell sp from
            hlog2 _ rfl]; exact nextTail)
      (by rw [show tailNextLog R1 (tailNext_loads d1.σ.mem R1) = tailStoreLog d.σ.mem cell sp from hlog2 _ rfl]
          exact outTail)
      (by simp only [tailNext_loads, List.getD_cons_succ, List.getD_cons_zero]; rw [hnext]
          simpa [guardB] using last)).run d1 ⟨p1.pc, rfl⟩
    rw [show tailNextLog R1 (tailNext_loads d1.σ.mem R1) = tailStoreLog d.σ.mem cell sp from hlog2 _ rfl] at p2
    obtain ⟨e, h⟩ := finish p2 (by show some (bytesVal .ld (read8 d1.σ.mem (R1 8 + 48#64).toNat)) = _; rw [hnext]) (by rfl)
    refine ⟨d2, run1.trans run2, ?_, h⟩
    simp only [afterPc, last, ↓reduceIte]; exact e

end OCaml.Vm.Primitives.Channel.OutList
