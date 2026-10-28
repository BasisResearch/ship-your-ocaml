import OCaml.Vm.Primitives.Channel.OutListLoop
import OCaml.Vm.Primitives.Channel.MlOpen
import OCaml.Vm.Sim.SmallNurseryWords
import Vsa.Sim.DeriveLoop
import OCaml.Vm.Boot.Startup.HeapFrame
import OCaml.Vm.Gc.LibHeap
import OCaml.Vm.Gc.LoopFold
import OCaml.Vm.Primitives.Word32Access

/-!
# `caml_ml_out_channels_list`'s list walk as one machine loop

The walk visits the open-channel list (`caml_all_opened_channels`, through
`next`) from the head. For each listed record (an output channel managed by
the GC, `Listed`) it allocates the custom block (`caml_alloc_custom_mem`,
lane a6-gc's `CustomMemCall`) and the cons cell (`caml_alloc_small`) in the
nursery. Each listed record takes 48 bytes: the block's header, ops and data
words, then the cell's header, car and cdr (`objWords`). The loop invariant
(`WalkAt`) holds at the head and at the exit (`leave`), relative to the
head's first visit `e`:
* the records listed so far, `vs`, are laid out below the entry `young_ptr`;
* `res` (`sp + 24`) is the newest cell;
* every byte outside the walk's written set (`Written`) reads as at `e`.
-/

namespace OCaml.Vm.Sim.OutListWalk
open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel.OutList LeanRV64DExecutable
set_option autoImplicit false
variable {Customs : Config → Nat → Prop}

instance (m : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64) : Decidable (Listed m p) := by
  unfold Listed; infer_instance

/-- A channel record's extent. -/
def recBytes : Nat := chanOffBuff + OCaml.Bytecode.ioBufferSize

/-- The walk's fixed data: its frame `sp`, the caller's `local_roots`, the
domain record `D`, `young_ptr`/`young_limit` at the head (`Y`, `Lm`), the
open-channel list and newlib's blocks at the head. -/
structure Walk where
  sp : BitVec 64
  roots : BitVec 64
  D : Nat
  Y : Nat
  Lm : Nat
  chs : List Nat
  H0 : List (Nat × Nat)
  /-- the runtime's custom-allocation state at the primitive's entry -/
  S : Nat → Prop

/-- A byte, as the custom call's frame states it. -/
def mem8 (c : Config) (a : Nat) : BitVec 8 := (c.σ.mem[a]?).getD 0

/-- The runtime's custom-allocation state at the primitive's entry. -/
def StateAt (w : Walk) (_state : Config → Nat → Prop) (a : Nat) : Prop := w.S a

/-- What the walk may write: the frame's scratch slots and the callees'
stack, the free nursery, the records' refcounts, `young_limit`/`young_ptr`
(the call's frame keeps bytes apart from the `young_ptr` word as a whole), the runtime's
custom-allocation state and newlib's own bytes. -/
def Written (w : Walk) (state : Config → Nat → Prop) (a : Nat) : Prop :=
  (w.sp.toNat - Gc.customStackBytes ≤ a ∧ a < w.sp.toNat + 48) ∨ (w.Lm ≤ a ∧ a < w.Y) ∨
    (∃ r ∈ w.chs, r + 64 ≤ a ∧ a < r + 68) ∨ (w.D ≤ a ∧ a < w.D + 16) ∨ StateAt w state a ∨
    VsaIris.VsaHeap.vsaFoot w.H0 a

/-- The listed records of `rs`, at memory `m`. -/
def listedRecs (m : Std.ExtHashMap Nat (BitVec 8)) (rs : List Nat) : List Nat :=
  rs.filter fun r => decide (Listed m (BitVec.ofNat 64 r))

/-- `res` after `j` listed records: `Val_emptylist`, then the newest cell. -/
def resWord (Y j : Nat) : BitVec 64 := if j = 0 then 1#64 else BitVec.ofNat 64 (Y - 48 * j + 8)

/-- A cons cell's header: wosize 2, tag 0. -/
def consHeader : BitVec 64 := 2048#64

theorem consHeader_eq : (2#64 <<< 10) + SmallAllocation.tagWord 0#64 = consHeader := by decide

/-- The six words of the `j`-th listed record `r` (0-based), below
`b = Y - 48 j`: the custom block (header, ops, record) and the cons cell
(header, the block, the previous `res`). -/
def objWords (Y j r : Nat) : List (Nat × BitVec 64) :=
  [(Y - 48 * j - 24, Gc.customHeader), (Y - 48 * j - 16, Gc.channelOps), (Y - 48 * j - 8, BitVec.ofNat 64 r),
   (Y - 48 * j - 48, consHeader), (Y - 48 * j - 40, BitVec.ofNat 64 (Y - 48 * j - 16)),
   (Y - 48 * j - 32, resWord Y j)]

/-- The listed records' objects in the nursery. -/
def NurseryList (m : Std.ExtHashMap Nat (BitVec 8)) (Y : Nat) (vs : List Nat) : Prop :=
  ∀ j r, vs[j]? = some r → ∀ x ∈ objWords Y j r, bytesT m x.1 8 = x.2

theorem objWords_range {Y j r : Nat} {x : Nat × BitVec 64} (hx : x ∈ objWords Y j r) (room : 48 * (j + 1) ≤ Y) :
    Y - 48 * (j + 1) ≤ x.1 ∧ x.1 + 8 ≤ Y - 48 * j := by
  simp only [objWords, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- The listed objects read the same across a frame that keeps the bytes
from the current `young_ptr` up to `Y`. -/
theorem NurseryList.frame {m m' : Std.ExtHashMap Nat (BitVec 8)} {Y : Nat} {vs : List Nat}
    (h : NurseryList m Y vs) (room : 48 * vs.length ≤ Y)
    (same : ∀ a, Y - 48 * vs.length ≤ a → a < Y → bytesT m' a 1 = bytesT m a 1) : NurseryList m' Y vs := by
  intro j r hj x hx
  have lt := (List.getElem?_eq_some_iff.mp hj).1
  have range := objWords_range hx (by have : j + 1 ≤ vs.length := lt; omega)
  rw [Reloc.bytesT_congr (fun i hi => same _ (by have : j + 1 ≤ vs.length := lt; omega) (by omega))]
  exact h j r hj x hx

/-- One more listed record: its six words, below the old ones. -/
theorem NurseryList.snoc {m : Std.ExtHashMap Nat (BitVec 8)} {Y : Nat} {vs : List Nat} {r : Nat}
    (h : NurseryList m Y vs) (fresh : ∀ x ∈ objWords Y vs.length r, bytesT m x.1 8 = x.2) :
    NurseryList m Y (vs ++ [r]) := by
  intro j r' hj
  by_cases lt : j < vs.length
  · rw [List.getElem?_append_left lt] at hj; exact h j r' hj
  · rw [List.getElem?_append_right (by omega)] at hj
    have j0 : j - vs.length = 0 := by
      cases e : j - vs.length with
      | zero => rfl
      | succ k => rw [e] at hj; simp at hj
    rw [j0] at hj
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    have : j = vs.length := by omega
    subst this
    exact fresh

/-- A channel record of the walk: in newlib's arena, word-aligned, apart from
the minor heap and the domain record. -/
structure RecordAt (w : Walk) (r : Nat) : Prop where
  low : Vsa.Sim.DlHeap.heapStart ≤ r
  high : r + recBytes ≤ Vsa.Sim.DlHeap.heapEnd
  aligned : r % 8 = 0
  minor : r + recBytes ≤ Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ r
  domain : r + recBytes ≤ w.D ∨ w.D + Layout.domainStateBytes ≤ r

/-- **The runtime's state grows only into newlib's blocks across one
`caml_alloc_custom_mem` call.** -/
def CustomMemGrows (state : Config → Nat → Prop) : Prop :=
  ∀ H site v f d, Gc.CustomMemReturned state H site v f d →
    ∀ a, state d a → state f a ∨ VsaIris.VsaHeap.vsaFoot H a

theorem customMemGrows {state : Config → Nat → Prop} : CustomMemGrows state :=
  fun _ _ _ _ _ ret => ret.grows

/-- The walk's geometry: the frame above newlib's arena, the domain record,
the nursery (with room for `n` listed records), the records, pairwise apart,
and newlib's blocks at the head covering the nursery, the records and the
domain record. -/
structure WalkGeometry (w : Walk) (n : Nat) : Prop where
  spLow : Vsa.Sim.DlHeap.heapEnd + Gc.customStackBytes ≤ w.sp.toNat
  spHigh : w.sp.toNat + 128 ≤ Layout.sym_stack_top
  spAligned : w.sp.toNat % 16 = 0
  domainLow : Vsa.Sim.DlHeap.heapStart ≤ w.D
  domainHigh : w.D + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  domainAligned : w.D % 8 = 0
  nurseryLow : Gc.minorRegion.lo ≤ w.Lm
  nurseryHigh : w.Y ≤ Gc.minorRegion.hi
  youngAligned : w.Y % 8 = 0
  room : w.Lm + 48 * n ≤ w.Y
  domainApart : w.D + Layout.domainStateBytes ≤ Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ w.D
  records : ∀ r ∈ w.chs, RecordAt w r
  recordsApart : ∀ r ∈ w.chs, ∀ r' ∈ w.chs, r ≠ r' → r + recBytes ≤ r' ∨ r' + recBytes ≤ r
  coverMinor : ∃ x ∈ w.H0, x.1 ≤ Gc.minorRegion.lo ∧ Gc.minorRegion.hi ≤ x.1 + x.2
  coverRecords : ∀ r ∈ w.chs, ∃ x ∈ w.H0, x.1 ≤ r ∧ r + recBytes ≤ x.1 + x.2
  coverDomain : ∃ x ∈ w.H0, x.1 ≤ w.D ∧ w.D + Layout.domainStateBytes ≤ x.1 + x.2
  /-- the entry's state lies where the custom calls' callers may not write
  (`CallerApart` at the entry, whose open-channel list and domain are the walk's) -/
  stateApart : ∀ a, w.S a → ∃ c, Gc.CallerApart c a ∧ (∀ r ∈ w.chs, a < r ∨ r + recBytes ≤ a) ∧
    (word c Layout.sym_Caml_state).toNat = w.D

/-- The callee-saved registers the walk keeps. -/
def calleeSaved : List Nat := [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- **The walk's invariant** at the head (or at `leave` once `rest` is
empty), having visited `pre`, relative to the first visit `e`. -/
structure WalkAt (w : Walk) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (Customs : Config → Nat → Prop) (k : Nat)
    (e : Config) (pre rest : List Nat) (d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  link : ∃ r, gprGet d.σ 1 = some r ∧ r.toNat % 4 = 0
  idle : d.σ.regs.get? Register.htif_payload_writes = some 0#4
  pc : pcOf d = some (if rest = [] then exitPc else headPc)
  regs : ∃ a0, HeadRegs w.sp (BitVec.ofNat 64 (rest.headD 0)) a0 w.roots d
  saved : ∀ n ∈ calleeSaved, gprGet d.σ n = gprGet e.σ n
  gprs : GprsKept e d
  output : d.σ.sailOutput = e.σ.sailOutput
  split : w.chs = pre ++ rest
  list : Gc.OpenChannels d.σ.mem (rest.headD 0) rest
  opened : Gc.OpenChannelList d.σ.mem w.chs
  records : ∀ r ∈ w.chs, ∀ j, j < recBytes → (j < 64 ∨ 68 ≤ j) → bytesT d.σ.mem (r + j) 1 = bytesT e.σ.mem (r + j) 1
  /-- Actual four-byte observations; only visited listed records are bumped. -/
  refwords : ∀ r ∈ w.chs, bytesT d.σ.mem (r + chanOffRefcount) 4 =
    bytesT e.σ.mem (r + chanOffRefcount) 4 +
      (if r ∈ listedRecs e.σ.mem pre then 1#32 else 0#32)
  res : bytesT d.σ.mem (w.sp + 24#64).toNat 8 = resWord w.Y (listedRecs e.σ.mem pre).length
  domain : word d Layout.sym_Caml_state = BitVec.ofNat 64 w.D
  young : word d (w.D + Layout.off_young_ptr) = BitVec.ofNat 64 (w.Y - 48 * (listedRecs e.σ.mem pre).length)
  limit : word d (w.D + Layout.off_young_limit) = BitVec.ofNat 64 w.Lm
  nursery : NurseryList d.σ.mem w.Y (listedRecs e.σ.mem pre)
  frame : ∀ a, ¬ Written w state a → bytesT d.σ.mem a 1 = bytesT e.σ.mem a 1
  counted : Gc.CustomCountStep Customs e d (listedRecs e.σ.mem pre).length
  ready : Ready (k + (listedRecs e.σ.mem rest).length) d
  heap : ∃ H cap, OCaml.Vm.Boot.Startup.HeapReady H cap d ∧ Gc.CustomOwned state H d ∧ Gc.CustomLedger H d ∧ ∀ x ∈ w.H0, x ∈ H
  /-- the state now lies in the entry's state or newlib's free space at the entry -/
  stateIn : ∀ a, state d a → w.S a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a
  allocIn : ∀ a, Gc.CustomAllocFoot d a → Gc.CustomAllocFoot e a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a

/-- Entry spatial evidence and owned records exclude those records from
subsequent state growth into the selected allocator's free footprint. -/
theorem WalkGeometry.state_record_apart {w : Walk} {n : Nat} (g : WalkGeometry w n)
    {S : Nat → Prop} (inside : ∀ a, S a → w.S a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a)
    {a r : Nat} (state : S a) (member : r ∈ w.chs) : a < r ∨ r + recBytes ≤ a := by
  rcases inside a state with old | free
  · obtain ⟨_, _, records, _⟩ := g.stateApart a old
    exact records r member
  · apply Classical.byContradiction
    intro no
    obtain ⟨e, he, lo, hi⟩ := g.coverRecords r member
    rcases free with global | ⟨_, _, outside⟩
    · rcases VsaIris.VsaHeap.allocGlobal_off_arena a global with low | high
      · have bound := (g.records r member).low
        omega
      · have bound := (g.records r member).high
        omega
    · exact outside e he ⟨by omega, by omega⟩

/-- A record's `Listed` test reads the bytes the walk keeps. -/
theorem listed_iff {m m' : Std.ExtHashMap Nat (BitVec 8)} {r : Nat} (fit : r + 80 < 2 ^ 64)
    (same : ∀ j, j < 80 → (j < 64 ∨ 68 ≤ j) → bytesT m' (r + j) 1 = bytesT m (r + j) 1) :
    Listed m' (BitVec.ofNat 64 r) ↔ Listed m (BitVec.ofNat 64 r) := by
  have a32 : (BitVec.ofNat 64 r + 32#64).toNat = r + 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have a68 : (BitVec.ofNat 64 r + 68#64).toNat = r + 68 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have max : bytesT m' (r + 32) 8 = bytesT m (r + 32) 8 :=
    Reloc.bytesT_congr fun j hj => by simpa only [Nat.add_assoc] using same (32 + j) (by omega) (by omega)
  have flags : read8 m' (r + 68) = read8 m (r + 68) := by
    have b : ∀ j, j < 8 → (m'[r + 68 + j]?).getD 0 = (m[r + 68 + j]?).getD 0 := fun j hj => by
      have := same (68 + j) (by omega) (by omega)
      rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte, ← Nat.add_assoc] at this; exact this
    simp only [Primitives.read8]
    have b0 := b 0 (by omega); have b1 := b 1 (by omega); have b2 := b 2 (by omega); have b3 := b 3 (by omega)
    have b4 := b 4 (by omega); have b5 := b 5 (by omega); have b6 := b 6 (by omega); have b7 := b 7 (by omega)
    simp only [Nat.add_zero] at b0
    rw [b0, b1, b2, b3, b4, b5, b6, b7]
  unfold Listed; rw [a32, a68, max, flags]

/-- A list's start is its head (`0` for the empty list). -/
theorem openChannels_head {m : Std.ExtHashMap Nat (BitVec 8)} {x : Nat} {l : List Nat}
    (h : Gc.OpenChannels m x l) : x = l.headD 0 ∧ (l = [] ↔ x = 0) := by
  cases h with
  | nil => exact ⟨rfl, by simp⟩
  | cons ne _ => exact ⟨rfl, by simpa using ne⟩

/-- The record's address as the machine computes it. -/
theorem rec_off {r k : Nat} (fit : r + k < 2 ^ 64) : (BitVec.ofNat 64 r + BitVec.ofNat 64 k).toNat = r + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem RecordAt.fit {w : Walk} {r : Nat} (h : RecordAt w r) : r + recBytes < 2 ^ 32 := by
  have := h.high; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega

theorem RecordAt.windows {w : Walk} {r : Nat} (h : RecordAt w r) : RecordWindows (BitVec.ofNat 64 r) := by
  have fit := h.fit; have lo := h.low
  simp only [recBytes, chanOffBuff, OCaml.Bytecode.ioBufferSize] at fit
  simp only [Vsa.Sim.DlHeap.heapStart] at lo
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [rec_off (by omega)]; omega)
    | (rw [rec_off (by omega), tohost]; omega)

/-- `next` of the visited record is the rest's head. -/
theorem next_eq {m : Std.ExtHashMap Nat (BitVec 8)} {r : Nat} {rest : List Nat} (fit : r + 48 < 2 ^ 64)
    (h : Gc.OpenChannels m r (r :: rest)) :
    nextRec m (BitVec.ofNat 64 r) = BitVec.ofNat 64 (rest.headD 0) ∧
      afterPc (nextRec m (BitVec.ofNat 64 r)) = if rest = [] then exitPc else headPc := by
  cases h with
  | cons _ tail =>
    obtain ⟨hx, empty⟩ := openChannels_head tail
    have e : nextRec m (BitVec.ofNat 64 r) = BitVec.ofNat 64 (rest.headD 0) := by
      rw [← hx, nextRec, rec_off fit, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    refine ⟨e, ?_⟩
    by_cases r0 : rest = []
    · have : (bytesT m (r + Gc.chanOffNext) 8).toNat = 0 := empty.1 r0
      have z : nextRec m (BitVec.ofNat 64 r) = 0#64 := by
        rw [nextRec, rec_off fit]; exact BitVec.eq_of_toNat_eq this
      simp [afterPc, z, r0]
    · have : (bytesT m (r + Gc.chanOffNext) 8).toNat ≠ 0 := fun z => r0 (empty.2 z)
      have nz : nextRec m (BitVec.ofNat 64 r) ≠ 0#64 := by
        rw [nextRec, rec_off fit]; intro z; exact this (by rw [show r + 48 = r + Gc.chanOffNext from rfl] at z; rw [z]; rfl)
      simp [afterPc, nz, r0]

theorem listedRecs_skip {m : Std.ExtHashMap Nat (BitVec 8)} {pre : List Nat} {r : Nat}
    (skip : ¬ Listed m (BitVec.ofNat 64 r)) : listedRecs m (pre ++ [r]) = listedRecs m pre := by
  simp [listedRecs, List.filter_append, skip]

theorem listedRecs_cons_skip {m : Std.ExtHashMap Nat (BitVec 8)} {rest : List Nat} {r : Nat}
    (skip : ¬ Listed m (BitVec.ofNat 64 r)) : listedRecs m (r :: rest) = listedRecs m rest := by
  simp [listedRecs, List.filter_cons, skip]

/-- A configuration with the same memory keeps newlib's heap. -/
theorem HeapReady.of_mem {H : List (Nat × Nat)} {cap : Nat} {c c' : Config}
    (h : OCaml.Vm.Boot.Startup.HeapReady H cap c) (m : c'.σ.mem = c.σ.mem) :
    OCaml.Vm.Boot.Startup.HeapReady H cap c' :=
  h.frame (fun _ _ => by rw [m]) (fun _ _ => by rw [m]) (fun _ _ => by rw [m]) (fun _ _ => by rw [m])

/-- **An unlisted record**: the walk moves on with nothing written. -/
theorem walk_skip {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {e : Config} {pre rest : List Nat} {r : Nat} {d : Config} (custom : Gc.CustomMemCall Ready state Customs)
    (g : WalkGeometry w n) (h : WalkAt w Ready state Customs k e pre (r :: rest) d) (skip : ¬ Listed e.σ.mem (BitVec.ofNat 64 r)) :
    ∃ d', Steps d d' ∧ WalkAt w Ready state Customs k e (pre ++ [r]) rest d' := by
  have mem : r ∈ w.chs := by rw [h.split]; simp
  have hr := g.records r mem
  have fit := hr.fit
  simp only [recBytes, chanOffBuff, OCaml.Bytecode.ioBufferSize] at fit
  obtain ⟨a0, regs⟩ := h.regs
  obtain ⟨ra, hra, al⟩ := h.link
  have leaf : LeafInput ra d := ⟨h.good, h.image, h.minstret, hra, al, h.tick⟩
  have pc : pcOf d = some headPc := by simpa using h.pc
  have recsD : ∀ j, j < 80 → (j < 64 ∨ 68 ≤ j) → bytesT d.σ.mem (r + j) 1 = bytesT e.σ.mem (r + j) 1 :=
    fun j hj hn => h.records r mem j (by unfold recBytes chanOffBuff OCaml.Bytecode.ioBufferSize; omega) hn
  have skipD : ¬ Listed d.σ.mem (BitVec.ofNat 64 r) := by
    rw [listed_iff (by omega) recsD]; exact skip
  have regs : HeadRegs w.sp (BitVec.ofNat 64 r) a0 w.roots d := regs
  have list : Gc.OpenChannels d.σ.mem r (r :: rest) := h.list
  obtain ⟨d', run, post, regs'⟩ := visit_skip leaf regs pc hr.windows skipD
  obtain ⟨nx, after⟩ := next_eq (by omega) list
  have m' : d'.σ.mem = d.σ.mem := post.memory
  have tail : Gc.OpenChannels d.σ.mem (rest.headD 0) rest := by
    cases list with
    | cons _ t =>
      have := (openChannels_head t).1
      rw [← this]; exact t
  have frame := fun n (hn : n ∈ calleeSaved) => (post.gpr_frame (by decide) n (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hn; omega) (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hn; omega) (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans (h.saved n hn)
  have readyD := h.ready
  rw [listedRecs_cons_skip skip] at readyD
  have fr := custom.frame_counted _ d d' readyD (fun a _ => by rw [m']) (by unfold word; rw [m'])
  refine ⟨d', run, {
    good := post.good, image := post.image, minstret := post.minstret, tick := post.tick
    link := ⟨ra, (post.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans hra, al⟩
    idle := (post.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans h.idle
    pc := by rw [post.pc, after]
    regs := ⟨a0, by rw [← nx]; exact regs'⟩
    saved := frame
    gprs := h.gprs.trans post.kept
    output := post.output.trans h.output
    split := by rw [h.split]; simp
    list := by rw [m']; exact tail
    opened := by rw [m']; exact h.opened
    records := by rw [m']; exact h.records
    refwords := by rw [m', listedRecs_skip skip]; exact h.refwords
    res := by rw [m', listedRecs_skip skip]; exact h.res
    domain := by unfold word; rw [m']; exact h.domain
    young := by unfold word; rw [m', listedRecs_skip skip]; exact h.young
    limit := by unfold word; rw [m']; exact h.limit
    nursery := by rw [m', listedRecs_skip skip]; exact h.nursery
    frame := by rw [m']; exact h.frame
    counted := by
      rw [listedRecs_skip skip]
      simpa using h.counted.trans fr.counts
    ready := fr.ready
    stateIn := fun a hs => h.stateIn a ((fr.state a).mp hs)
    allocIn := fun a ha => h.allocIn a (((Gc.customFoot_congr fr.addresses.1 fr.addresses.2).2 a).mp ha)
    heap := by obtain ⟨H, cap, hr, owned, ledger, sub⟩ := h.heap; exact ⟨H, cap, HeapReady.of_mem hr m', owned.frame fr.state, ledger.congr fr.addresses.1 fr.addresses.2, sub⟩ }⟩

/-- Arithmetic over the walk's layout constants. -/
macro "walk_omega" : tactic => `(tactic| (
  have : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have : Vsa.Sim.DlHeap.heapStart = 0x8007d140 := rfl
  have : Gc.minorRegion.lo = 0x80082000 := rfl
  have : Gc.minorRegion.hi = 0x80282000 := rfl
  have : Layout.sym_stack_top = 0x88000000 := rfl
  have : Layout.domainStateBytes = 928 := rfl
  have : recBytes = 65608 := rfl
  have : chanOffBuff = 72 := rfl
  have : OCaml.Bytecode.ioBufferSize = 65536 := rfl
  have : Gc.customStackBytes = 576 := rfl
  have : Layout.off_young_ptr = 8 := rfl
  have : Layout.off_young_limit = 0 := rfl
  have : Layout.sym_Caml_state = 0x80064d08 := rfl
  have : Layout.sym_tohost = 0x80061fc0 := rfl
  have : Layout.sym_bss_end = 0x8007d138 := rfl
  have : Layout.sym_caml_all_opened_channels = 0x80064b40 := rfl
  omega))

/-- The nursery words read as `runtimeFields`. -/
theorem fields_of_words {c : Config} {D Y Lm : Nat} (hD : D < 2 ^ 64) (hY : Y < 2 ^ 64) (hL : Lm < 2 ^ 64)
    (domain : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (young : word c (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y)
    (limit : word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm) :
    (runtimeFields c).youngPtr = Y ∧ (runtimeFields c).youngLimit = Lm := by
  have d : (word c Layout.sym_Caml_state).toNat = D := by rw [domain, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD]
  refine ⟨?_, ?_⟩
  · show domainWord c Layout.off_young_ptr = Y
    rw [domainWord, d, young, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hY]
  · show domainWord c Layout.off_young_limit = Lm
    rw [domainWord, d, limit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL]

/-- A write log missing an 8-byte word keeps it. -/
theorem word_keep {c c' : Config} {log : List WEntry} {a : Nat} (m : c'.σ.mem = writeLog c.σ.mem log)
    (out : OutLRange log a 8) : word c' a = word c a := by
  unfold word; rw [m]; exact bytesT_writeLog_out _ out

/-- The listed records of the visited suffix, with the visited one listed. -/
theorem listedRecs_cons_go {m : Std.ExtHashMap Nat (BitVec 8)} {rest : List Nat} {r : Nat}
    (go : Listed m (BitVec.ofNat 64 r)) : listedRecs m (r :: rest) = r :: listedRecs m rest := by
  simp [listedRecs, List.filter_cons, go]

theorem listedRecs_go {m : Std.ExtHashMap Nat (BitVec 8)} {pre : List Nat} {r : Nat}
    (go : Listed m (BitVec.ofNat 64 r)) : listedRecs m (pre ++ [r]) = listedRecs m pre ++ [r] := by
  simp [listedRecs, List.filter_append, go]

/-- **A listed record, up to `caml_alloc_custom_mem`**: the call's input
(newlib's heap and readiness carried across the refcount and `local_roots`
stores). -/
theorem walk_enter {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {e : Config} {pre rest : List Nat} {r : Nat} {d : Config} (custom : Gc.CustomMemCall Ready state Customs)
    (g : WalkGeometry w n) (h : WalkAt w Ready state Customs k e pre (r :: rest) d)
    (go : Listed e.σ.mem (BitVec.ofNat 64 r)) (count : (listedRecs e.σ.mem w.chs).length ≤ n) :
    ∃ f H cap, Steps d f ∧ Gc.CustomMemInput H cap (walkSite w.sp (BitVec.ofNat 64 r)) f ∧ (∀ x ∈ w.H0, x ∈ H) ∧
      Ready (k + (listedRecs e.σ.mem rest).length + 1) f ∧
      f.σ.mem = writeLog d.σ.mem (enterLog d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots) ∧
      EffectPost [15, 10, 11, 12, 15, 1] (writeLog d.σ.mem (enterLog d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots)) d
        Gc.customMemEntry Gc.channelOps f ∧
      word f Layout.sym_Caml_state = BitVec.ofNat 64 w.D ∧
      (runtimeFields f).youngPtr = w.Y - 48 * (listedRecs e.σ.mem pre).length ∧
      (runtimeFields f).youngLimit = w.Lm ∧
      Gc.CustomFramed Ready state Customs (k + (listedRecs e.σ.mem rest).length + 1) d f ∧
      Gc.CustomOwned state H f := by
  have mem : r ∈ w.chs := by rw [h.split]; simp
  have hr := g.records r mem
  have fit := hr.fit
  have rlo := hr.low; have ral := hr.aligned
  have spl := g.spLow; have sph := g.spHigh; have spa := g.spAligned
  obtain ⟨a0, regs⟩ := h.regs
  have regs : HeadRegs w.sp (BitVec.ofNat 64 r) a0 w.roots d := regs
  obtain ⟨ra, hra, al⟩ := h.link
  have leaf : LeafInput ra d := ⟨h.good, h.image, h.minstret, hra, al, h.tick⟩
  have pc : pcOf d = some headPc := by simpa using h.pc
  have recsD : ∀ j, j < 80 → (j < 64 ∨ 68 ≤ j) → bytesT d.σ.mem (r + j) 1 = bytesT e.σ.mem (r + j) 1 :=
    fun j hj hn => h.records r mem j (by unfold recBytes chanOffBuff OCaml.Bytecode.ioBufferSize; omega) hn
  have goD : Listed d.σ.mem (BitVec.ofNat 64 r) := by rw [listed_iff (by walk_omega) recsD]; exact go
  obtain ⟨d1, run1, post1, regs1⟩ := visit_go leaf regs pc hr.windows goD
  have m1 : d1.σ.mem = d.σ.mem := post1.memory
  have r64 : (BitVec.ofNat 64 r + 64#64).toNat = r + 64 := rec_off (by walk_omega)
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by walk_omega)
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have wRef : WriteWindow (BitVec.ofNat 64 r + 64#64) 4 :=
    ⟨by rw [r64]; walk_omega, by rw [r64]; walk_omega, by rw [r64, tohost]; walk_omega, by rw [r64]; omega⟩
  have wSlot : WriteWindow (w.sp + 8#64) 8 :=
    ⟨by rw [s8]; walk_omega, by rw [s8]; walk_omega, by rw [s8, tohost]; walk_omega, by rw [s8]; omega⟩
  have outside : ImageOutside (enterLog d1.σ.mem w.sp (BitVec.ofNat 64 r) w.roots) := by
    apply imageOutside_of_above
    intro x hx
    simp only [enterLog, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · show Layout.sym_bss_end ≤ (BitVec.ofNat 64 r + 64#64).toNat; rw [r64]; walk_omega
    · show Layout.sym_bss_end ≤ (w.sp + 8#64).toNat; rw [s8]; walk_omega
  obtain ⟨f, run2, post2, link, args⟩ :=
    alloc_enter (post1.leafInput (by decide) (by decide) leaf) regs1 post1.pc wRef wSlot outside
  rw [m1] at post2
  have mf : f.σ.mem = writeLog d.σ.mem (enterLog d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots) := post2.memory
  -- the words `CustomMemInput` reads
  have out8 : ∀ a, (a + 8 ≤ r + 64 ∨ r + 68 ≤ a) → (a + 8 ≤ w.sp.toNat + 8 ∨ w.sp.toNat + 16 ≤ a) →
      OutLRange (enterLog d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots) a 8 := by
    intro a h1 h2
    simp only [enterLog, OutLRange, r64, s8, and_true]; omega
  have dD := g.domainLow; have dH := g.domainHigh; have rd := hr.domain
  have wDom : word f Layout.sym_Caml_state = BitVec.ofNat 64 w.D := by
    rw [word_keep mf (out8 _ (by walk_omega) (by walk_omega))]; exact h.domain
  have wYoung : word f (w.D + Layout.off_young_ptr) =
      BitVec.ofNat 64 (w.Y - 48 * (listedRecs e.σ.mem pre).length) := by
    rw [word_keep mf (out8 _ (by walk_omega) (by walk_omega))]; exact h.young
  have wLimit : word f (w.D + Layout.off_young_limit) = BitVec.ofNat 64 w.Lm := by
    rw [word_keep mf (out8 _ (by walk_omega) (by walk_omega))]; exact h.limit
  have split := h.split
  have total : (listedRecs e.σ.mem w.chs).length =
      (listedRecs e.σ.mem pre).length + 1 + (listedRecs e.σ.mem rest).length := by
    rw [split, listedRecs, List.filter_append, List.length_append, ← listedRecs, ← listedRecs,
      listedRecs_cons_go go, List.length_cons]; omega
  have room := g.room; have yh := g.nurseryHigh; have nl := g.nurseryLow; have ya := g.youngAligned
  have jlt : (listedRecs e.σ.mem pre).length + 1 ≤ n := by omega
  obtain ⟨fy, fl⟩ := fields_of_words (c := f) (by walk_omega) (by walk_omega) (by walk_omega) wDom wYoung wLimit
  obtain ⟨H, cap, heap, owned, _ledger, sub⟩ := h.heap
  -- bytes outside the two stores
  have keepByte : ∀ a, (a < r + 64 ∨ r + 68 ≤ a) → (a < w.sp.toNat + 8 ∨ w.sp.toNat + 16 ≤ a) →
      (f.σ.mem[a]?).getD 0 = (d.σ.mem[a]?).getD 0 := by
    intro a h1 h2
    rw [mf, writeLog_out _ _ _ (by simp only [enterLog, OutL, r64, s8, and_true]; omega)]
  obtain ⟨cov, covIn, covLo, covHi⟩ := g.coverRecords r mem
  have heapF : OCaml.Vm.Boot.Startup.HeapReady H cap f := by
    apply Gc.HeapReady.keep_windows heap (ws := [⟨r + 64, r + 68⟩, ⟨w.sp.toNat + 8, w.sp.toNat + 16⟩])
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl ⟨cov, sub cov covIn, by simp only; omega, by simp only; unfold recBytes chanOffBuff at covHi; omega⟩
      · exact Or.inr (Or.inl (by simp only; walk_omega))
    · intro a ha
      exact keepByte a (ha _ List.mem_cons_self) (ha _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have readyD := h.ready
  rw [listedRecs_cons_go go, List.length_cons, ← Nat.add_assoc] at readyD
  have frF := custom.frame_counted _ d f readyD (fun a sa => by
    have ap := custom.apart d a sa
    have recA := g.state_record_apart h.stateIn sa mem
    have below := ap.belowStack
    exact keepByte a (by walk_omega) (by walk_omega))
    (word_keep mf (out8 _ (by walk_omega) (by walk_omega)))
  have readyF := frF.ready
  refine ⟨f, H, cap, run1.trans run2, {
    leaf := ⟨post2.good, post2.image, post2.minstret, link, by show call_call.link.toNat % 4 = 0; decide, post2.tick⟩
    heap := heapF
    pc := post2.pc
    regs := args
    frame := ⟨spl, by show w.sp.toNat ≤ _; walk_omega, spa, by decide⟩
    room := by rw [fy, fl]; omega
    youngAligned := by rw [fy]; omega }, sub, readyF, mf, post1.trans post2, wDom, fy, fl, frF, owned.frame frF.state⟩

/-- From the custom block `V` (at the old `young_ptr − 16`) back to the head:
its data word and the CAMLlocal slots (`consEnterLog`), `caml_alloc_small`'s
reservation and header (the cell at `V − 24`), `res := cell`, its car and
cdr. -/
def afterLog (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) (r V D : Nat) : List WEntry :=
  consEnterLog m sp (BitVec.ofNat 64 r) (BitVec.ofNat 64 V) ++
    [(D + 8, 8, BitVec.ofNat 64 (V - 32)), (V - 32, 8, consHeader)] ++
    [((sp + 24#64).toNat, 8, BitVec.ofNat 64 (V - 24)), (V - 24, 8, BitVec.ofNat 64 V),
     (V - 16, 8, bytesT m (sp + 24#64).toNat 8)]

/-- The walk's numbers around one listed record's allocations. -/
structure AfterNums (sp : BitVec 64) (r V D Lm : Nat) : Prop where
  spLow : Vsa.Sim.DlHeap.heapEnd + Gc.customStackBytes ≤ sp.toNat
  spHigh : sp.toNat + 128 ≤ Layout.sym_stack_top
  spAligned : sp.toNat % 16 = 0
  domainLow : Vsa.Sim.DlHeap.heapStart ≤ D
  domainHigh : D + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd
  domainAligned : D % 8 = 0
  domainApart : D + Layout.domainStateBytes ≤ Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ D
  limitLow : Gc.minorRegion.lo ≤ Lm
  room : Lm + 32 ≤ V
  youngHigh : V + 16 ≤ Gc.minorRegion.hi
  aligned : V % 8 = 0
  recLow : Vsa.Sim.DlHeap.heapStart ≤ r
  recHigh : r + recBytes ≤ Vsa.Sim.DlHeap.heapEnd
  recMinor : r + recBytes ≤ Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ r
  recDomain : r + recBytes ≤ D ∨ D + Layout.domainStateBytes ≤ r

/-- **After `caml_alloc_custom_mem`, back to the head**: the cons cell's
allocation and fields, as one write log over the return's memory. -/
theorem walk_after {ra sp : BitVec 64} {r V D Lm : Nat} {g : Config} (nums : AfterNums sp r V D Lm)
    (leaf : LeafInput ra g) (h2 : gpr g 2 = some sp) (h8 : gpr g 8 = some (BitVec.ofNat 64 r))
    (h10 : gpr g 10 = some (BitVec.ofNat 64 V)) (pc : pcOf g = some call_call.link)
    (wD : word g Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (wY : word g (D + Layout.off_young_ptr) = BitVec.ofNat 64 (V - 8))
    (wL : word g (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm) :
    ∃ d', Steps g d' ∧
      EffectPost [10, 11, 15, 1, 6, 10, 12, 13, 14, 15, 16, 17, 12, 14, 15, 8, 13]
        (writeLog g.σ.mem (afterLog g.σ.mem sp r V D)) g (afterPc (nextRec g.σ.mem (BitVec.ofNat 64 r)))
        (BitVec.ofNat 64 (V - 24)) d' ∧
      HeadRegs sp (nextRec g.σ.mem (BitVec.ofNat 64 r)) (BitVec.ofNat 64 (V - 24))
        (bytesT g.σ.mem (sp + 8#64).toNat 8) d' ∧ gprGet d'.σ 1 = some cons_call.link := by
  obtain ⟨spl, sph, spa, dl, dh, da, dap, ll, room, yh, ya, rl, rh, rm, rdm⟩ := nums
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have nat : ∀ x, x < 2 ^ 64 → (BitVec.ofNat 64 x).toNat = x := fun x hx => toNat_ofNat_small hx
  have s8 : (sp + 8#64).toNat = sp.toNat + 8 := off_toNat (by walk_omega)
  have s24 : (sp + 24#64).toNat = sp.toNat + 24 := off_toNat (by walk_omega)
  have s32 : (sp + 32#64).toNat = sp.toNat + 32 := off_toNat (by walk_omega)
  have s40 : (sp + 40#64).toNat = sp.toNat + 40 := off_toNat (by walk_omega)
  have vN : (BitVec.ofNat 64 V).toNat = V := nat _ (by walk_omega)
  have v8 : (BitVec.ofNat 64 V + 8#64).toNat = V + 8 := by rw [off_toNat (by rw [vN]; walk_omega), vN]
  have r48 : (BitVec.ofNat 64 r + 48#64).toNat = r + 48 := rec_off (by walk_omega)
  have win : ∀ x : BitVec 64, x.toNat = x.toNat → Layout.sym_bss_end ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 32 →
      x.toNat % 8 = 0 → WriteWindow x 8 := fun x _ lo hi al =>
    ⟨by walk_omega, hi, by walk_omega, al⟩
  -- the cons block and the call of `caml_alloc_small`
  have outC : ImageOutside (consEnterLog g.σ.mem sp (BitVec.ofNat 64 r) (BitVec.ofNat 64 V)) := by
    apply imageOutside_of_above; intro x hx
    simp only [consEnterLog, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · show _ ≤ (BitVec.ofNat 64 V + 8#64).toNat; rw [v8]; walk_omega
    · show _ ≤ (sp + 40#64).toNat; rw [s40]; walk_omega
    · show _ ≤ (sp + 32#64).toNat; rw [s32]; walk_omega
  obtain ⟨g1, run1, post1, link1, regs1⟩ := cons_enter leaf h2 h8 h10 pc
    (win _ rfl (by rw [v8]; walk_omega) (by rw [v8]; walk_omega) (by rw [v8]; omega))
    (win _ rfl (by rw [s24]; walk_omega) (by rw [s24]; walk_omega) (by rw [s24]; omega))
    (win _ rfl (by rw [s32]; walk_omega) (by rw [s32]; walk_omega) (by rw [s32]; omega))
    (win _ rfl (by rw [s40]; walk_omega) (by rw [s40]; walk_omega) (by rw [s40]; omega))
    (by rw [vN]; walk_omega) (by walk_omega) outC
  have m1 := post1.memory
  have outC8 : ∀ a, (a + 8 ≤ V + 8 ∨ V + 16 ≤ a) → (a + 8 ≤ sp.toNat + 32 ∨ sp.toNat + 48 ≤ a) →
      OutLRange (consEnterLog g.σ.mem sp (BitVec.ofNat 64 r) (BitVec.ofNat 64 V)) a 8 := by
    intro a h1 h2
    simp only [consEnterLog, OutLRange, v8, s32, s40, and_true]; omega
  have wD1 : word g1 Layout.sym_Caml_state = BitVec.ofNat 64 D := by
    rw [word_keep m1 (outC8 _ (by walk_omega) (by walk_omega))]; exact wD
  have wY1 : word g1 (D + Layout.off_young_ptr) = BitVec.ofNat 64 (V - 8) := by
    rw [word_keep m1 (outC8 _ (by walk_omega) (by walk_omega))]; exact wY
  have wL1 : word g1 (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm := by
    rw [word_keep m1 (outC8 _ (by walk_omega) (by walk_omega))]; exact wL
  have small := SmallAllocation.NurseryMemory.of_words (ra := cons_call.link) (size := 2#64) (tag := 0#64)
    wD1 wY1 wL1 (by walk_omega) (by walk_omega) da (by decide) (by simp only [BitVec.toNat_ofNat]; omega)
    (by walk_omega) (by walk_omega) (by omega)
    (by simp only [BitVec.toNat_ofNat]; walk_omega)
  have leaf1 : LeafInput cons_call.link g1 :=
    ⟨post1.good, post1.image, post1.minstret, link1, by decide, post1.tick⟩
  obtain ⟨g2, run2, post2⟩ := (SmallAllocation.alloc_small_nursery g1 cons_call.link 2#64 0#64 _ _ _
    (small.input leaf1 (gholds_lookup _ regs1 (by rfl)) (gholds_lookup _ regs1 (by rfl)))).run g1
    ⟨post1.pc, rfl⟩
  have cellEq : SmallAllocation.nurseryHeader (BitVec.ofNat 64 (V - 8)) 2#64 + 8#64 = BitVec.ofNat 64 (V - 24) := by
    apply BitVec.eq_of_toNat_eq
    simp only [SmallAllocation.nurseryHeader, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat]
    walk_omega
  have hctor : SmallAllocation.constructorLog cons_call.link 2#64 0#64 (BitVec.ofNat 64 D) (BitVec.ofNat 64 (V - 8)) =
      [(D + 8, 8, BitVec.ofNat 64 (V - 32)), (V - 32, 8, consHeader)] := by
    rw [SmallAllocation.constructorLog_words (by walk_omega) (by walk_omega) (by decide)
      (by rw [show (2#64 : BitVec 64).toNat = 2 from rfl]; omega)]
    rw [show (2#64 : BitVec 64).toNat = 2 from rfl, show V - 8 - 8 - 8 * 2 = V - 32 by omega, consHeader_eq]
  have m2 : g2.σ.mem = writeLog (writeLog g.σ.mem (consEnterLog g.σ.mem sp (BitVec.ofNat 64 r) (BitVec.ofNat 64 V)))
      [(D + 8, 8, BitVec.ofNat 64 (V - 32)), (V - 32, 8, consHeader)] := by
    rw [post2.memory, m1, hctor]
  have outK8 : ∀ a, (a + 8 ≤ D + 8 ∨ D + 16 ≤ a) → (a + 8 ≤ V - 32 ∨ V - 24 ≤ a) →
      OutLRange [(D + 8, 8, BitVec.ofNat 64 (V - 32)), (V - 32, 8, consHeader)] a 8 := by
    intro a h1 h2; simp only [OutLRange, and_true]; omega
  have read2 : ∀ a, (a + 8 ≤ D + 8 ∨ D + 16 ≤ a) → (a + 8 ≤ V - 32 ∨ V - 24 ≤ a) →
      (a + 8 ≤ V + 8 ∨ V + 16 ≤ a) → (a + 8 ≤ sp.toNat + 32 ∨ sp.toNat + 48 ≤ a) →
      bytesT g2.σ.mem a 8 = bytesT g.σ.mem a 8 := by
    intro a h1 h2 h3 h4
    rw [m2, bytesT_writeLog_out _ (outK8 a h1 h2), bytesT_writeLog_out _ (outC8 a h3 h4)]
  have nextEq : nextRec g2.σ.mem (BitVec.ofNat 64 r) = nextRec g.σ.mem (BitVec.ofNat 64 r) := by
    unfold nextRec; rw [r48]; exact read2 _ (by walk_omega) (by walk_omega) (by walk_omega) (by walk_omega)
  have rootsEq : bytesT g2.σ.mem (sp + 8#64).toNat 8 = bytesT g.σ.mem (sp + 8#64).toNat 8 := by
    rw [s8]; exact read2 _ (by walk_omega) (by walk_omega) (by walk_omega) (by omega)
  have chanEq : bytesT g2.σ.mem (sp + 40#64).toNat 8 = BitVec.ofNat 64 V := by
    rw [m2, bytesT_writeLog_out _ (outK8 _ (by rw [s40]; walk_omega) (by rw [s40]; walk_omega))]
    exact Gc.word_writeLog_at _ _ 1 _ _ rfl (by simp only [consEnterLog, List.drop, OutLRange, s32, s40, and_true]; omega)
  have tailEq : bytesT g2.σ.mem (sp + 32#64).toNat 8 = bytesT g.σ.mem (sp + 24#64).toNat 8 := by
    rw [m2, bytesT_writeLog_out _ (outK8 _ (by rw [s32]; walk_omega) (by rw [s32]; walk_omega))]
    exact Gc.word_writeLog_at _ _ 2 _ _ rfl (by simp only [consEnterLog, List.drop, OutLRange])
  have cellN : (BitVec.ofNat 64 (V - 24)).toNat = V - 24 := nat _ (by walk_omega)
  have cdrN : (BitVec.ofNat 64 (V - 24) + 8#64).toNat = V - 16 := by
    rw [off_toNat (by rw [cellN]; walk_omega), cellN]; omega
  have leaf2 : LeafInput cons_call.link g2 :=
    ⟨post2.good, post2.image, post2.minstret, gholds_lookup _ post2.regs (by rfl), by decide, post2.tick⟩
  have k2 : ∀ n, n ∈ [2, 8] → gpr g2 n = gpr g1 n := fun n hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> exact post2.toEffectPost.gpr_frame (by decide) _ (by decide) (by decide) (by decide)
  have h2' : gpr g2 2 = some sp := (k2 2 (by simp)).trans (gholds_lookup _ regs1 (by rfl))
  have h8' : gpr g2 8 = some (BitVec.ofNat 64 r) := (k2 8 (by simp)).trans (gholds_lookup _ regs1 (by rfl))
  have h10' : gpr g2 10 = some (BitVec.ofNat 64 (V - 24)) := by rw [post2.result, cellEq]
  have outL : ImageOutside (linkStoreLog g2.σ.mem sp (BitVec.ofNat 64 (V - 24))) := by
    apply imageOutside_of_above; intro x hx
    simp only [linkStoreLog, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · show _ ≤ (sp + 24#64).toNat; rw [s24]; walk_omega
    · show _ ≤ (BitVec.ofNat 64 (V - 24)).toNat; rw [cellN]; walk_omega
  have outT : ImageOutside (tailStoreLog g2.σ.mem (BitVec.ofNat 64 (V - 24)) sp) := by
    apply imageOutside_of_above; intro x hx
    simp only [tailStoreLog, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; show _ ≤ (BitVec.ofNat 64 (V - 24) + 8#64).toNat; rw [cdrN]; walk_omega
  obtain ⟨d', run3, post3, regs3⟩ := link_step leaf2 h2' h8' h10' post2.pc
    ⟨by rw [r48]; walk_omega, by rw [r48]; walk_omega, by rw [r48, tohost]; walk_omega⟩
    (win _ rfl (by rw [s24]; walk_omega) (by rw [s24]; walk_omega) (by rw [s24]; omega))
    (win _ rfl (by rw [s8]; walk_omega) (by rw [s8]; walk_omega) (by rw [s8]; omega)).read
    (win _ rfl (by rw [s32]; walk_omega) (by rw [s32]; walk_omega) (by rw [s32]; omega)).read
    (win _ rfl (by rw [s40]; walk_omega) (by rw [s40]; walk_omega) (by rw [s40]; omega)).read
    (win _ rfl (by rw [cellN]; walk_omega) (by rw [cellN]; walk_omega) (by rw [cellN]; omega))
    (win _ rfl (by rw [cdrN]; walk_omega) (by rw [cdrN]; walk_omega) (by rw [cdrN]; omega))
    (by rw [cellN]; walk_omega) (by walk_omega)
    (by simp only [linkStoreLog, OutLRange, r48, s24, cellN, and_true]; walk_omega)
    (by simp only [tailStoreLog, OutLRange, r48, cdrN, and_true]; walk_omega) outL outT
  rw [nextEq, rootsEq] at regs3
  rw [nextEq] at post3
  refine ⟨d', run1.trans (run2.trans run3), ?_, regs3,
    (post3.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans (gholds_lookup _ post2.regs (by rfl))⟩
  have final : writeLog (writeLog g2.σ.mem (linkStoreLog g2.σ.mem sp (BitVec.ofNat 64 (V - 24))))
      (tailStoreLog g2.σ.mem (BitVec.ofNat 64 (V - 24)) sp) = writeLog g.σ.mem (afterLog g.σ.mem sp r V D) := by
    rw [m2, afterLog, writeLog_append, writeLog_append, ← m2, ← writeLog_append]
    congr 1
    simp only [linkStoreLog, tailStoreLog, chanEq, tailEq, cellN, cdrN, List.cons_append, List.nil_append]
  rw [final] at post3
  exact (post1.trans post2.toEffectPost).trans post3

theorem vsaFoot_sub {H0 H : List (Nat × Nat)} (sub : ∀ x ∈ H0, x ∈ H) {a : Nat}
    (h : VsaIris.VsaHeap.vsaFoot H a) : VsaIris.VsaHeap.vsaFoot H0 a := by
  rcases h with g | ⟨lo, hi, out⟩
  · exact Or.inl g
  · exact Or.inr ⟨lo, hi, fun x hx => out x (sub x hx)⟩

theorem not_vsaFoot_in {H : List (Nat × Nat)} {x : Nat × Nat} (hx : x ∈ H) {a : Nat}
    (lo : Vsa.Sim.DlHeap.heapStart ≤ a) (inn : x.1 ≤ a ∧ a < x.1 + x.2) : ¬ VsaIris.VsaHeap.vsaFoot H a := by
  rintro (g | ⟨_, _, out⟩)
  · simp only [VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange] at g
    simp only [Vsa.Sim.DlHeap.heapStart] at lo; omega
  · exact out x hx inn

theorem vsaFoot_low {H : List (Nat × Nat)} {a : Nat} (h : VsaIris.VsaHeap.vsaFoot H a) :
    a < Vsa.Sim.DlHeap.heapEnd := by
  rcases h with g | ⟨_, hi, _⟩
  · simp only [VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange] at g
    simp only [Vsa.Sim.DlHeap.heapEnd]; omega
  · exact hi

/-- A record's bytes other than its refcount are outside the walk's writes. -/
theorem record_not_written {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n) {r : Nat} (mem : r ∈ w.chs) {j : Nat}
    (hj : j < recBytes) (hn : j < 64 ∨ 68 ≤ j) : ¬ Written w state (r + j) := by
  have hr := g.records r mem
  have rl := hr.low; have rh := hr.high; have rm := hr.minor; have rd := hr.domain
  have spl := g.spLow; have nl := g.nurseryLow; have nh := g.nurseryHigh; have dh := g.domainHigh
  rintro (stk | nur | ⟨r', mem', lo, hi⟩ | yng | hs | foot)
  · walk_omega
  · walk_omega
  · by_cases same : r' = r
    · subst same; omega
    · rcases g.recordsApart r mem r' mem' (Ne.symm same) with a | a <;> walk_omega
  · walk_omega
  · obtain ⟨c, ap, op, _⟩ := g.stateApart _ hs
    have := op r mem
    omega
  · obtain ⟨x, hx, xlo, xhi⟩ := g.coverRecords r mem
    exact not_vsaFoot_in hx (by omega) ⟨by omega, by simp only [recBytes] at hj xhi; omega⟩ foot

/-- The open-channel list carries over when the head word and every
record's `next` word read the same. -/
theorem opened_transfer {m m' : Std.ExtHashMap Nat (BitVec 8)} {chs : List Nat} (h : Gc.OpenChannelList m chs)
    (head : bytesT m' Layout.sym_caml_all_opened_channels 8 = bytesT m Layout.sym_caml_all_opened_channels 8)
    (nexts : ∀ r ∈ chs, bytesT m' (r + Gc.chanOffNext) 8 = bytesT m (r + Gc.chanOffNext) 8) :
    Gc.OpenChannelList m' chs := by
  unfold Gc.OpenChannelList at h ⊢; rw [head]; exact h.congr nexts

/-- The nursery words back from `runtimeFields`. -/
theorem words_of_fields {c : Config} {D Y Lm : Nat} (hD : D < 2 ^ 64) (hY : Y < 2 ^ 64) (hL : Lm < 2 ^ 64)
    (domain : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (young : (runtimeFields c).youngPtr = Y) (limit : (runtimeFields c).youngLimit = Lm) :
    word c (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y ∧ word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm := by
  have d : (word c Layout.sym_Caml_state).toNat = D := by rw [domain, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD]
  change domainWord c Layout.off_young_ptr = Y at young
  change domainWord c Layout.off_young_limit = Lm at limit
  rw [domainWord, d] at young limit
  exact ⟨BitVec.eq_of_toNat_eq (by rw [young, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hY]),
    BitVec.eq_of_toNat_eq (by rw [limit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL])⟩

/-- Bytes outside the cons stores' footprint: the cell `[V − 32, V − 8)`, the
block's data word `[V + 8, V + 16)`, the CAMLlocal slots and `young_ptr`. -/
theorem afterLog_outL {m : Std.ExtHashMap Nat (BitVec 8)} {sp : BitVec 64} {r V D a : Nat}
    (spFit : sp.toNat + 128 < 2 ^ 64) (vFit : V + 16 < 2 ^ 64) (vLow : 32 ≤ V)
    (cell : a < V - 32 ∨ V - 8 ≤ a) (data : a < V + 8 ∨ V + 16 ≤ a) (slots : a < sp.toNat + 24 ∨ sp.toNat + 48 ≤ a)
    (young : a < D + 8 ∨ D + 16 ≤ a) : OutL (afterLog m sp r V D) a := by
  have s24 : (sp + 24#64).toNat = sp.toNat + 24 := off_toNat (by omega)
  have s32 : (sp + 32#64).toNat = sp.toNat + 32 := off_toNat (by omega)
  have s40 : (sp + 40#64).toNat = sp.toNat + 40 := off_toNat (by omega)
  have v8 : (BitVec.ofNat 64 V + 8#64).toNat = V + 8 := by
    rw [off_toNat (by rw [toNat_ofNat_small (by omega)]; omega), toNat_ofNat_small (by omega)]
  simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, OutL, s24, s32, s40, v8, and_true]
  omega

/-- Words outside the cons stores' footprint. -/
theorem afterLog_outLRange {m : Std.ExtHashMap Nat (BitVec 8)} {sp : BitVec 64} {r V D a : Nat}
    (spFit : sp.toNat + 128 < 2 ^ 64) (vFit : V + 16 < 2 ^ 64) (vLow : 32 ≤ V)
    (cell : a + 8 ≤ V - 32 ∨ V - 8 ≤ a) (data : a + 8 ≤ V + 8 ∨ V + 16 ≤ a)
    (slots : a + 8 ≤ sp.toNat + 24 ∨ sp.toNat + 48 ≤ a) (young : a + 8 ≤ D + 8 ∨ D + 16 ≤ a) :
    OutLRange (afterLog m sp r V D) a 8 := by
  have s24 : (sp + 24#64).toNat = sp.toNat + 24 := off_toNat (by omega)
  have s32 : (sp + 32#64).toNat = sp.toNat + 32 := off_toNat (by omega)
  have s40 : (sp + 40#64).toNat = sp.toNat + 40 := off_toNat (by omega)
  have v8 : (BitVec.ofNat 64 V + 8#64).toNat = V + 8 := by
    rw [off_toNat (by rw [toNat_ofNat_small (by omega)]; omega), toNat_ofNat_small (by omega)]
  simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, OutLRange, s24, s32, s40, v8, and_true]
  omega

/-- A byte of the runtime's state misses the cons stores. -/
theorem state_misses_after {a V D Lm Y sp : Nat} (minor : a < Gc.minorRegion.lo ∨ Gc.minorRegion.hi ≤ a)
    (below : a < Vsa.Sim.DlHeap.heapEnd) (young : a + 8 ≤ D + 8 ∨ D + 8 + 8 ≤ a)
    (lm : Gc.minorRegion.lo ≤ Lm) (room : Lm + 32 ≤ V) (hi : V + 16 ≤ Y) (yh : Y ≤ Gc.minorRegion.hi)
    (spl : Vsa.Sim.DlHeap.heapEnd + Gc.customStackBytes ≤ sp) :
    (a < V - 32 ∨ V - 8 ≤ a) ∧ (a < V + 8 ∨ V + 16 ≤ a) ∧ (a < sp + 24 ∨ sp + 48 ≤ a) ∧
      (a < D + 8 ∨ D + 16 ≤ a) := by
  walk_omega

theorem outside_of {lo hi a : Nat} (h : ¬ (lo ≤ a ∧ a < hi)) : a < lo ∨ hi ≤ a := by omega

/-- The state's one static word misses the list head. -/
theorem state_misses_head {c : Config} {a : Nat} (ap : Gc.CallerApart c a) :
    a + 8 ≤ Layout.sym_caml_all_opened_channels ∨ Layout.sym_caml_all_opened_channels + 8 ≤ a := by
  by_cases lo : a < Vsa.Sim.DlHeap.heapStart
  · have := ap.static lo
    simp only [VsaIris.InExt, Layout.sym_caml_extra_heap_resources] at this
    walk_omega
  · walk_omega

/-- **One listed record's machine run**, from the head `d` through the call
(`f`), its return (`g'`) and back to the head (`d'`): the custom block at `V`,
the cell at `V − 24`, and every fact the invariant needs, by name. -/
structure ListedStep (w : Walk) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (Customs : Config → Nat → Prop) (k : Nat)
    (e : Config) (pre rest : List Nat) (r : Nat) (d f g' d' : Config) (V j : Nat)
    (H H' : List (Nat × Nat)) (cap' : Nat) : Prop where
  run : Steps d d'
  count : (listedRecs e.σ.mem pre).length = j
  young : V + 16 = w.Y - 48 * j
  room : w.Lm + 48 * (j + 1) ≤ w.Y
  enterMem : f.σ.mem = writeLog d.σ.mem (enterLog d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots)
  postF : EffectPost [15, 10, 11, 12, 15, 1] (writeLog d.σ.mem (enterLog d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots))
    d Gc.customMemEntry Gc.channelOps f
  domainF : word f Layout.sym_Caml_state = BitVec.ofNat 64 w.D
  openedF : Gc.OpenChannelList f.σ.mem w.chs
  sub : ∀ x ∈ w.H0, x ∈ H
  callKept : ∀ a, ¬ state f a → ¬ VsaIris.VsaHeap.vsaFoot H a →
    (a < w.sp.toNat - Gc.customStackBytes ∨ w.sp.toNat ≤ a) → (a + 24 < V + 16 ∨ V + 16 ≤ a) →
    (a + 8 ≤ w.D + 8 ∨ w.D + 16 ≤ a) → bytesT g'.σ.mem a 1 = bytesT f.σ.mem a 1
  header : bytesT g'.σ.mem (V - 8) 8 = Gc.customHeader
  ops : bytesT g'.σ.mem V 8 = Gc.channelOps
  domainG : word g' Layout.sym_Caml_state = BitVec.ofNat 64 w.D
  limitG : word g' (w.D + Layout.off_young_limit) = BitVec.ofNat 64 w.Lm
  savedG : ∀ n ∈ calleeSaved, gprGet g'.σ n = gprGet f.σ n
  gprsG : GprsKept f g'
  outputG : g'.σ.sailOutput = f.σ.sailOutput
  idleG : g'.σ.regs.get? Register.htif_payload_writes = some 0#4
  countedF : Gc.CustomCountStep Customs d f 0
  countedG : Gc.CustomCountStep Customs f g' 1
  readyG : Ready (k + (listedRecs e.σ.mem rest).length) g'
  heapG : OCaml.Vm.Boot.Startup.HeapReady H' cap' g'
  ownedG : Gc.CustomOwned state H' g'
  ledgerG : Gc.CustomLedger H' g'
  sub' : ∀ x ∈ H, x ∈ H'
  afterMem : d'.σ.mem = writeLog g'.σ.mem (afterLog g'.σ.mem w.sp r V w.D)
  post : EffectPost [10, 11, 15, 1, 6, 10, 12, 13, 14, 15, 16, 17, 12, 14, 15, 8, 13]
    (writeLog g'.σ.mem (afterLog g'.σ.mem w.sp r V w.D)) g' (afterPc (nextRec g'.σ.mem (BitVec.ofNat 64 r)))
    (BitVec.ofNat 64 (V - 24)) d'
  regs : HeadRegs w.sp (nextRec g'.σ.mem (BitVec.ofNat 64 r)) (BitVec.ofNat 64 (V - 24))
    (bytesT g'.σ.mem (w.sp + 8#64).toNat 8) d'
  link : gprGet d'.σ 1 = some cons_call.link
  stateF : ∀ a, state f a → w.S a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a
  stateG : ∀ a, state g' a → w.S a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a
  allocGrowth : ∀ a, Gc.CustomAllocFoot g' a → Gc.CustomAllocFoot d a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a

/-- **A listed record's machine run** exists. -/
theorem walk_listed_run {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d : Config} (custom : Gc.CustomMemCall Ready state Customs)
    (grows : CustomMemGrows state)
    (g : WalkGeometry w n) (h : WalkAt w Ready state Customs k e pre (r :: rest) d)
    (go : Listed e.σ.mem (BitVec.ofNat 64 r)) (count : (listedRecs e.σ.mem w.chs).length ≤ n) :
    ∃ f g' d' V H H' cap', ListedStep w Ready state Customs k e pre rest r d f g' d' V
      (listedRecs e.σ.mem pre).length H H' cap' := by
  have mem : r ∈ w.chs := by rw [h.split]; simp
  have hr := g.records r mem
  have rl := hr.low; have rh := hr.high; have rm := hr.minor; have rdm := hr.domain; have ral := hr.aligned
  have spl := g.spLow; have sph := g.spHigh; have spa := g.spAligned
  have dl := g.domainLow; have dh := g.domainHigh; have da := g.domainAligned; have dap := g.domainApart
  have nl := g.nurseryLow; have nh := g.nurseryHigh; have ya := g.youngAligned; have room := g.room
  obtain ⟨f, H, cap, run1, input, sub, readyF, mf, postF, wDomF, fyF, flF, iffF, ownedF⟩ := walk_enter custom g h go count
  obtain ⟨g', run2, v, ret, readyG⟩ := (custom.call H cap _ _ f readyF input ownedF).run f ⟨input.pc, rfl⟩
  have split := h.split
  have total : (listedRecs e.σ.mem w.chs).length =
      (listedRecs e.σ.mem pre).length + 1 + (listedRecs e.σ.mem rest).length := by
    rw [split, listedRecs, List.filter_append, List.length_append, ← listedRecs, ← listedRecs,
      listedRecs_cons_go go, List.length_cons]; omega
  have hv : v.toNat + 16 = w.Y - 48 * (listedRecs e.σ.mem pre).length := by rw [ret.block, fyF]
  have vEq : v = BitVec.ofNat 64 v.toNat := (BitVec.eq_of_toNat_eq (toNat_ofNat_small v.isLt)).symm
  have wDomG : word g' Layout.sym_Caml_state = BitVec.ofNat 64 w.D := ret.domain.trans wDomF
  obtain ⟨wYG, wLG⟩ := words_of_fields (c := g') (Y := v.toNat - 8) (Lm := w.Lm) (by walk_omega) (by walk_omega)
    (by walk_omega) wDomG (by rw [ret.youngPtr, fyF]; omega) (by rw [ret.youngLimit, flF])
  obtain ⟨ra', hra', al'⟩ := ret.link
  have leafG : LeafInput ra' g' := ⟨ret.good, ret.image, ret.minstret, hra', al', ret.tick⟩
  have h10 : gpr g' 10 = some (BitVec.ofNat 64 v.toNat) := by rw [← vEq]; exact ret.result
  have nums : AfterNums w.sp r v.toNat w.D w.Lm :=
    ⟨spl, sph, spa, dl, dh, da, dap, nl, by omega, by omega, by omega, rl, rh, rm, rdm⟩
  obtain ⟨d', run3, post3, regs3, link3⟩ := walk_after nums leafG ret.stack ret.record h10 ret.pc wDomG wYG wLG
  have domF : Gc.domainAddr f Layout.off_young_ptr = w.D + 8 := by
    simp only [Gc.domainAddr, wDomF, BitVec.toNat_ofNat, Layout.off_young_ptr]; walk_omega
  have r64 : (BitVec.ofNat 64 r + 64#64).toNat = r + 64 := rec_off (by walk_omega)
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by walk_omega)
  have nextsF : ∀ r' ∈ w.chs, bytesT f.σ.mem (r' + Gc.chanOffNext) 8 = bytesT d.σ.mem (r' + Gc.chanOffNext) 8 := by
    intro r' mem'
    have hr' := g.records r' mem'
    have l' := hr'.low; have h' := hr'.high
    rw [mf]; apply bytesT_writeLog_out
    simp only [enterLog, OutLRange, r64, s8, and_true, Gc.chanOffNext]
    by_cases same : r' = r
    · subst same; walk_omega
    · rcases g.recordsApart r mem r' mem' (Ne.symm same) with a | a <;> walk_omega
  have openedF : Gc.OpenChannelList f.σ.mem w.chs := opened_transfer h.opened (by
    rw [mf]; apply bytesT_writeLog_out
    simp only [enterLog, OutLRange, r64, s8, and_true]; walk_omega) nextsF
  obtain ⟨H', cap', heapG, ownedG, ledgerG, sub'⟩ := ret.heap
  have stateF : ∀ a, state f a → w.S a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a := fun a hs => h.stateIn a ((iffF.state a).mp hs)
  have grows : ∀ a, state g' a → state f a ∨ VsaIris.VsaHeap.vsaFoot H a := grows _ _ _ _ _ ret.toCustomMemReturned
  exact ⟨f, g', d', v.toNat, H, H', cap', {
    run := run1.trans (run2.trans run3)
    count := rfl
    young := hv
    room := by omega
    enterMem := mf
    postF := postF
    domainF := wDomF
    openedF := openedF
    sub := sub
    callKept := fun a hs hf hk hb hy => by
      rw [Channel.bytesT_one_byte, Channel.bytesT_one_byte]
      exact ret.kept a hs hf hk (by rw [fyF]; omega) (by rw [domF]; exact hy)
    header := ret.header
    ops := ret.ops
    domainG := wDomG
    limitG := wLG
    savedG := ret.saved
    gprsG := ret.gprs
    outputG := ret.output
    idleG := ret.idle
    countedF := iffF.counts
    countedG := ⟨ret.count⟩
    readyG := readyG
    heapG := heapG
    ownedG := ownedG
    ledgerG := ledgerG
    allocGrowth := fun a ha => by
      rcases ret.allocGrows a ha with old | free
      · exact Or.inl (((Gc.customFoot_congr iffF.addresses.1 iffF.addresses.2).2 a).mp old)
      · exact Or.inr (vsaFoot_sub sub free)
    sub' := sub'
    afterMem := post3.memory
    post := post3
    regs := regs3
    link := link3
    stateF := stateF
    stateG := fun a hs => (grows a hs).elim (stateF a) fun x => Or.inr (vsaFoot_sub sub x) }⟩

/-- The run's numbers. -/
theorem ListedStep.nums {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) :
    w.Lm + 32 ≤ V ∧ V + 16 ≤ w.Y ∧ 32 ≤ V ∧ V + 16 < 2 ^ 64 ∧ w.sp.toNat + 128 < 2 ^ 64 := by
  have := s.young; have := s.room; have := g.nurseryLow; have := g.nurseryHigh; have := g.spHigh
  walk_omega

/-- A byte the call and both store logs miss reads as at the head. -/
theorem ListedStep.chain {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) (mem : r ∈ w.chs) {a : Nat}
    (e1 : a < r + 64 ∨ r + 68 ≤ a) (e2 : a < w.sp.toNat + 8 ∨ w.sp.toNat + 16 ≤ a)
    (hs : ¬ state f a) (hf : ¬ VsaIris.VsaHeap.vsaFoot H a)
    (hk : a < w.sp.toNat - Gc.customStackBytes ∨ w.sp.toNat ≤ a) (hb : a + 24 < V + 16 ∨ V + 16 ≤ a)
    (hy : a + 8 ≤ w.D + 8 ∨ w.D + 16 ≤ a) (c1 : a < V - 32 ∨ V - 8 ≤ a) (c2 : a < V + 8 ∨ V + 16 ≤ a)
    (c3 : a < w.sp.toNat + 24 ∨ w.sp.toNat + 48 ≤ a) (c4 : a < w.D + 8 ∨ w.D + 16 ≤ a) :
    bytesT d'.σ.mem a 1 = bytesT d.σ.mem a 1 := by
  obtain ⟨_, _, vl, vf, spf⟩ := s.nums g
  have hr := g.records r mem
  have r64 : (BitVec.ofNat 64 r + 64#64).toNat = r + 64 := rec_off (by have := hr.fit; walk_omega)
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by omega)
  rw [Channel.bytesT_one_byte, s.afterMem,
    writeLog_out _ _ _ (afterLog_outL (m := g'.σ.mem) (r := r) (D := w.D) spf vf vl c1 c2 c3 c4),
    ← Channel.bytesT_one_byte, s.callKept a hs hf hk hb hy, Channel.bytesT_one_byte, s.enterMem,
    writeLog_out _ _ _ (by simp only [enterLog, OutL, r64, s8, and_true]; omega), ← Channel.bytesT_one_byte]

/-- A byte the call and the entry stores miss reads at the return as at the head. -/
theorem ListedStep.atReturn {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) (mem : r ∈ w.chs) {a : Nat}
    (e1 : a < r + 64 ∨ r + 68 ≤ a) (e2 : a < w.sp.toNat + 8 ∨ w.sp.toNat + 16 ≤ a)
    (hs : ¬ state f a) (hf : ¬ VsaIris.VsaHeap.vsaFoot H a)
    (hk : a < w.sp.toNat - Gc.customStackBytes ∨ w.sp.toNat ≤ a) (hb : a + 24 < V + 16 ∨ V + 16 ≤ a)
    (hy : a + 8 ≤ w.D + 8 ∨ w.D + 16 ≤ a) : bytesT g'.σ.mem a 1 = bytesT d.σ.mem a 1 := by
  have hr := g.records r mem
  have r64 : (BitVec.ofNat 64 r + 64#64).toNat = r + 64 := rec_off (by have := hr.fit; walk_omega)
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by have := g.spHigh; walk_omega)
  rw [s.callKept a hs hf hk hb hy, Channel.bytesT_one_byte, s.enterMem,
    writeLog_out _ _ _ (by simp only [enterLog, OutL, r64, s8, and_true]; omega), ← Channel.bytesT_one_byte]

/-- The state at the call is the walk's. -/
theorem ListedStep.notState {w : Walk} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    {a : Nat} (hn : ¬ w.S a) (hf : ¬ VsaIris.VsaHeap.vsaFoot w.H0 a) : ¬ state f a := fun hs =>
  (s.stateF a hs).elim hn hf

/-- **The frame**: every byte the walk does not write reads as at the head. -/
theorem ListedStep.frame {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) (mem : r ∈ w.chs) (a : Nat) (hw : ¬ Written w state a) :
    bytesT d'.σ.mem a 1 = bytesT d.σ.mem a 1 := by
  obtain ⟨vlm, vy, _, _, _⟩ := s.nums g
  have stk := outside_of fun x => hw (Or.inl x)
  have nur := outside_of fun x => hw (Or.inr (Or.inl x))
  have rf := outside_of fun x => hw (Or.inr (Or.inr (Or.inl ⟨r, mem, x⟩)))
  have yg := outside_of fun x => hw (Or.inr (Or.inr (Or.inr (Or.inl x))))
  have st : ¬ state f a := s.notState (fun x => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x))))))
    fun x => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr x)))))
  have ft : ¬ VsaIris.VsaHeap.vsaFoot H a :=
    fun x => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (vsaFoot_sub s.sub x))))))
  have c576 : Gc.customStackBytes = 576 := rfl
  exact s.chain g mem rf (by omega) st ft (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-- A record byte other than the refcount, at the return. -/
theorem ListedStep.recordAtReturn {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) (mem : r ∈ w.chs) {i : Nat} (hi : i < recBytes) (hn : i < 64 ∨ 68 ≤ i) :
    bytesT g'.σ.mem (r + i) 1 = bytesT d.σ.mem (r + i) 1 := by
  obtain ⟨vlm, vy, _, _, _⟩ := s.nums g
  have hr := g.records r mem
  have rl := hr.low; have rh := hr.high; have rm := hr.minor; have rd := hr.domain
  have nl := g.nurseryLow; have nh := g.nurseryHigh; have spl := g.spLow
  obtain ⟨xr, xrIn, xrl, xrh⟩ := g.coverRecords r mem
  apply s.atReturn g mem (by omega) (by walk_omega)
  · intro hs; have := g.state_record_apart s.stateF hs mem
    have : chanOffBuff + OCaml.Bytecode.ioBufferSize = recBytes := rfl
    omega
  · exact not_vsaFoot_in (s.sub _ xrIn) (by omega) ⟨by omega, by omega⟩
  all_goals walk_omega

/-- Read the low four bytes of the actual increment store before the call. -/
theorem enter_refword (m : Std.ExtHashMap Nat (BitVec 8)) (sp p roots : BitVec 64)
    (apart : OutLRange [((sp + 8#64).toNat, 8, roots)] (p + 64#64).toNat 4) :
    bytesT (writeLog m (enterLog m sp p roots)) (p + 64#64).toNat 4 =
      bytesT m (p + 64#64).toNat 4 + 1#32 := by
  have split : enterLog m sp p roots =
      [((p + 64#64).toNat, 4, refcount m p)] ++ [((sp + 8#64).toNat, 8, roots)] := rfl
  rw [split, writeLog_append, bytesT_writeLog_out _ apart, word32_writeLog]
  have low : (bytesVal .lw (read8 m (p + 64#64).toNat)).setWidth 32 =
      bytesT m (p + 64#64).toNat 4 := by
    rw [Channel.lw_read8, truncate_signed_word]
  simp only [refcount, Sail.BitVec.extractLsb, BitVec.extractLsb]
  change (((bytesVal .lw (read8 m (p + 64#64).toNat) + 1#64).setWidth 32).signExtend 64).setWidth 32 = _
  rw [show ∀ v : BitVec 32, (v.signExtend 64).setWidth 32 = v from fun v => truncate_signed_word v]
  rw [BitVec.setWidth_add _ _ (by decide), low]
  rfl

/-- The native SW is read back after both allocations, with every other
record's four-byte field preserved by the same record frame. -/
theorem ListedStep.refwords {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) (mem : r ∈ w.chs) (q : Nat) (member : q ∈ w.chs) :
    bytesT d'.σ.mem (q + chanOffRefcount) 4 =
      bytesT d.σ.mem (q + chanOffRefcount) 4 + (if q = r then 1#32 else 0#32) := by
  obtain ⟨vlm, vy, vl, vf, spf⟩ := s.nums g
  have qr := g.records q member
  have ql := qr.low; have qh := qr.high; have qm := qr.minor; have qd := qr.domain
  have spl := g.spLow; have nh := g.nurseryHigh; have nl := g.nurseryLow
  have rfit := (g.records r mem).fit
  have r64 : (BitVec.ofNat 64 r + 64#64).toNat = r + 64 := rec_off (by walk_omega)
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by walk_omega)
  obtain ⟨xr, xrIn, xrl, xrh⟩ := g.coverRecords q member
  have minRec : 68 ≤ recBytes := by decide
  have minBytes : 68 ≤ chanOffBuff + OCaml.Bytecode.ioBufferSize := by decide
  have kept : bytesT d'.σ.mem (q + chanOffRefcount) 4 = bytesT f.σ.mem (q + chanOffRefcount) 4 := by
    apply Reloc.bytesT_congr
    intro i hi
    have hs : ¬ state f (q + chanOffRefcount + i) := by
      intro hs
      have := g.state_record_apart s.stateF hs member
      unfold chanOffRefcount at *
      omega
    have hf : ¬ VsaIris.VsaHeap.vsaFoot H (q + chanOffRefcount + i) :=
      not_vsaFoot_in (s.sub _ xrIn) (by omega) ⟨by unfold chanOffRefcount; omega,
        by unfold chanOffRefcount; omega⟩
    rw [Channel.bytesT_one_byte, s.afterMem,
      writeLog_out _ _ _ (afterLog_outL (m := g'.σ.mem) (r := r) (D := w.D) spf vf vl
        (by unfold chanOffRefcount; walk_omega) (by unfold chanOffRefcount; walk_omega)
        (by unfold chanOffRefcount; walk_omega) (by unfold chanOffRefcount; walk_omega)),
      ← Channel.bytesT_one_byte]
    exact s.callKept _ hs hf (by unfold chanOffRefcount; walk_omega)
      (by unfold chanOffRefcount; walk_omega) (by unfold chanOffRefcount; walk_omega)
  rw [kept, s.enterMem]
  by_cases eq : q = r
  · subst q
    rw [if_pos rfl]
    have tail : OutLRange [((w.sp + 8#64).toNat, 8, w.roots)] (BitVec.ofNat 64 r + 64#64).toNat 4 := by
      simp only [OutLRange, r64, s8, and_true]; walk_omega
    simpa only [r64, chanOffRefcount] using enter_refword d.σ.mem w.sp (BitVec.ofNat 64 r) w.roots tail
  · rw [if_neg eq, BitVec.add_zero]
    apply bytesT_writeLog_out
    have apart := g.recordsApart r mem q member (Ne.symm eq)
    simp only [enterLog, OutLRange, r64, s8, and_true]
    unfold chanOffRefcount
    rcases apart with apart | apart <;> walk_omega

/-- The frame's stack slots at the return. -/
theorem ListedStep.stackAtReturn {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) {a : Nat} (lo : w.sp.toNat ≤ a) (hi : a < w.sp.toNat + 128) :
    bytesT g'.σ.mem a 1 = bytesT f.σ.mem a 1 := by
  obtain ⟨vlm, vy, _, _, _⟩ := s.nums g
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh
  exact s.callKept a (fun hs => by have := (custom.apart f a hs).belowStack; walk_omega)
    (fun hf => by have := vsaFoot_low hf; walk_omega) (Or.inr lo) (by walk_omega) (by walk_omega)

/-- `local_roots` saved at `sp + 8`, at the return. -/
theorem ListedStep.roots {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap') (g : WalkGeometry w n) :
    bytesT g'.σ.mem (w.sp + 8#64).toNat 8 = w.roots := by
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by have := g.spHigh; walk_omega)
  rw [Reloc.bytesT_congr (m := f.σ.mem) fun i hi =>
    s.stackAtReturn custom g (by rw [s8]; omega) (by rw [s8]; omega), s.enterMem]
  exact Gc.word_writeLog_at _ _ 1 _ _ rfl (by simp only [enterLog, List.drop, OutLRange])

/-- `res` at the return. -/
theorem ListedStep.res {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap') (g : WalkGeometry w n)
    (mem : r ∈ w.chs) (h : bytesT d.σ.mem (w.sp + 24#64).toNat 8 = resWord w.Y j) :
    bytesT g'.σ.mem (w.sp + 24#64).toNat 8 = resWord w.Y j := by
  have hr := g.records r mem
  have r64 : (BitVec.ofNat 64 r + 64#64).toNat = r + 64 := rec_off (by have := hr.fit; walk_omega)
  have spl := g.spLow; have rh := hr.high
  have s8 : (w.sp + 8#64).toNat = w.sp.toNat + 8 := off_toNat (by have := g.spHigh; walk_omega)
  have s24 : (w.sp + 24#64).toNat = w.sp.toNat + 24 := off_toNat (by have := g.spHigh; walk_omega)
  rw [Reloc.bytesT_congr (m := f.σ.mem) fun i hi =>
    s.stackAtReturn custom g (by rw [s24]; omega) (by rw [s24]; omega), s.enterMem,
    bytesT_writeLog_out _ (by simp only [enterLog, OutLRange, r64, s8, s24, and_true]; walk_omega)]
  exact h

/-- The new record's six words at the head after the run. -/
theorem ListedStep.fresh {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap') (g : WalkGeometry w n)
    (mem : r ∈ w.chs) (h : bytesT d.σ.mem (w.sp + 24#64).toNat 8 = resWord w.Y j) :
    ∀ x ∈ objWords w.Y j r, bytesT d'.σ.mem x.1 8 = x.2 := by
  obtain ⟨vlm, vy, vl, vf, spf⟩ := s.nums g
  have yv := s.young
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh; have dap := g.domainApart
  have nl := g.nurseryLow
  have s24 : (w.sp + 24#64).toNat = w.sp.toNat + 24 := off_toNat (by omega)
  have s32 : (w.sp + 32#64).toNat = w.sp.toNat + 32 := off_toNat (by omega)
  have s40 : (w.sp + 40#64).toNat = w.sp.toNat + 40 := off_toNat (by omega)
  have v8 : (BitVec.ofNat 64 V + 8#64).toNat = V + 8 := by
    rw [off_toNat (by rw [toNat_ofNat_small (by omega)]; omega), toNat_ofNat_small (by omega)]
  have outW := fun {a : Nat} (c1 : a + 8 ≤ V - 32 ∨ V - 8 ≤ a) (c2 : a + 8 ≤ V + 8 ∨ V + 16 ≤ a)
      (c3 : a + 8 ≤ w.sp.toNat + 24 ∨ w.sp.toNat + 48 ≤ a) (c4 : a + 8 ≤ w.D + 8 ∨ w.D + 16 ≤ a) =>
    afterLog_outLRange (m := g'.σ.mem) (r := r) spf vf vl c1 c2 c3 c4
  intro x hx
  simp only [objWords, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · show bytesT d'.σ.mem (w.Y - 48 * j - 24) 8 = Gc.customHeader
    rw [show w.Y - 48 * j - 24 = V - 8 by omega, s.afterMem,
      bytesT_writeLog_out _ (outW (by omega) (by omega) (by walk_omega) (by walk_omega))]
    exact s.header
  · show bytesT d'.σ.mem (w.Y - 48 * j - 16) 8 = Gc.channelOps
    rw [show w.Y - 48 * j - 16 = V by omega, s.afterMem,
      bytesT_writeLog_out _ (outW (by omega) (by omega) (by walk_omega) (by walk_omega))]
    exact s.ops
  · show bytesT d'.σ.mem (w.Y - 48 * j - 8) 8 = BitVec.ofNat 64 r
    rw [show w.Y - 48 * j - 8 = (BitVec.ofNat 64 V + 8#64).toNat by rw [v8]; omega, s.afterMem]
    exact Gc.word_writeLog_at _ _ 0 _ _ rfl (by
      simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, List.drop, OutLRange, v8, s24, s32,
        s40, and_true]
      walk_omega)
  · show bytesT d'.σ.mem (w.Y - 48 * j - 48) 8 = consHeader
    rw [show w.Y - 48 * j - 48 = V - 32 by omega, s.afterMem]
    exact Gc.word_writeLog_at _ _ 4 _ _ rfl (by
      simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, List.drop, OutLRange, s24, and_true]
      walk_omega)
  · show bytesT d'.σ.mem (w.Y - 48 * j - 40) 8 = BitVec.ofNat 64 (w.Y - 48 * j - 16)
    rw [show w.Y - 48 * j - 40 = V - 24 by omega, show w.Y - 48 * j - 16 = V by omega, s.afterMem]
    exact Gc.word_writeLog_at _ _ 6 _ _ rfl (by
      simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, List.drop, OutLRange, and_true]
      omega)
  · show bytesT d'.σ.mem (w.Y - 48 * j - 32) 8 = resWord w.Y j
    rw [show w.Y - 48 * j - 32 = V - 16 by omega, s.afterMem, ← s.res custom g mem h]
    exact Gc.word_writeLog_at _ _ 7 _ _ rfl (by simp only [afterLog, consEnterLog, List.cons_append,
      List.nil_append, List.drop, OutLRange])

/-- The older listed objects survive the run. -/
theorem ListedStep.older {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap') (g : WalkGeometry w n)
    (mem : r ∈ w.chs) {a : Nat} (lo : w.Y - 48 * j ≤ a) (hi : a < w.Y) :
    bytesT d'.σ.mem a 1 = bytesT d.σ.mem a 1 := by
  obtain ⟨vlm, vy, vl, vf, spf⟩ := s.nums g
  have yv := s.young
  have hr := g.records r mem
  have rl := hr.low; have rh := hr.high; have rm := hr.minor
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh; have dap := g.domainApart
  have nl := g.nurseryLow
  obtain ⟨xm, xmIn, xml, xmh⟩ := g.coverMinor
  apply s.chain g mem (by walk_omega) (by walk_omega) (fun hs => by have := (custom.apart f a hs).minor; walk_omega)
    (not_vsaFoot_in (s.sub _ xmIn) (by walk_omega) ⟨by walk_omega, by walk_omega⟩)
  all_goals walk_omega

/-- Readiness from the return to the head. -/
theorem ListedStep.ready {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (custom : Gc.CustomMemCall Ready state Customs)
    (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap') (g : WalkGeometry w n) :
    Ready (k + (listedRecs e.σ.mem rest).length) d' ∧ word d' Layout.sym_Caml_state = BitVec.ofNat 64 w.D ∧
      (∀ a, state d' a → w.S a ∨ VsaIris.VsaHeap.vsaFoot w.H0 a) ∧
      Gc.CustomCountStep Customs g' d' 0 ∧ Gc.CustomOwned state H' d' ∧ Gc.CustomLedger H' d' ∧
      (∀ a, Gc.CustomAllocFoot d' a → Gc.CustomAllocFoot g' a) := by
  obtain ⟨vlm, vy, vl, vf, spf⟩ := s.nums g
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh; have nl := g.nurseryLow
  have dD : word d' Layout.sym_Caml_state = BitVec.ofNat 64 w.D := by
    rw [word_keep s.afterMem (afterLog_outLRange spf vf vl (by walk_omega) (by walk_omega) (by walk_omega)
      (by have := g.domainLow; walk_omega))]
    exact s.domainG
  have fr := custom.frame_counted _ g' d' s.readyG (fun a sa => by
    have ap := custom.apart g' a sa
    have yp := ap.youngPtr
    have dom : Gc.domainAddr g' Layout.off_young_ptr = w.D + 8 := by
      simp only [Gc.domainAddr, s.domainG, BitVec.toNat_ofNat, Layout.off_young_ptr]; walk_omega
    rw [dom] at yp
    obtain ⟨c1, c2, c3, c4⟩ := state_misses_after ap.minor ap.belowStack yp nl vlm vy nh spl
    rw [s.afterMem, writeLog_out _ _ _ (afterLog_outL spf vf vl c1 c2 c3 c4)])
    (dD.trans s.domainG.symm)
  exact ⟨fr.ready, dD, (fun a hs => s.stateG a ((fr.state a).mp hs)), fr.counts, s.ownedG.frame fr.state, s.ledgerG.congr fr.addresses.1 fr.addresses.2,
    fun a ha => ((Gc.customFoot_congr fr.addresses.1 fr.addresses.2).2 a).mp ha⟩

/-- newlib's heap from the return to the head. -/
theorem ListedStep.heap {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {r : Nat} {d f g' d' : Config} {V j : Nat}
    {H H' : List (Nat × Nat)} {cap' : Nat} (s : ListedStep w Ready state Customs k e pre rest r d f g' d' V j H H' cap')
    (g : WalkGeometry w n) : OCaml.Vm.Boot.Startup.HeapReady H' cap' d' := by
  obtain ⟨vlm, vy, vl, vf, spf⟩ := s.nums g
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh; have nl := g.nurseryLow
  have dl := g.domainLow
  obtain ⟨xm, xmIn, xml, xmh⟩ := g.coverMinor
  obtain ⟨xd, xdIn, xdl, xdh⟩ := g.coverDomain
  apply Gc.HeapReady.keep_windows s.heapG
    (ws := [⟨V - 32, V - 8⟩, ⟨V + 8, V + 16⟩, ⟨w.sp.toNat + 24, w.sp.toNat + 48⟩, ⟨w.D + 8, w.D + 16⟩])
  · simp only [List.forall_mem_cons]
    refine ⟨Or.inl ⟨xm, s.sub' _ (s.sub _ xmIn), ?_, ?_⟩, Or.inl ⟨xm, s.sub' _ (s.sub _ xmIn), ?_, ?_⟩,
      Or.inr (Or.inl ?_), Or.inl ⟨xd, s.sub' _ (s.sub _ xdIn), ?_, ?_⟩, fun _ h => absurd h List.not_mem_nil⟩
    all_goals (simp only; walk_omega)
  · intro a ha
    have h1 := ha _ List.mem_cons_self
    have h2 := ha ⟨V + 8, V + 16⟩ (by simp)
    have h3 := ha ⟨w.sp.toNat + 24, w.sp.toNat + 48⟩ (by simp)
    have h4 := ha ⟨w.D + 8, w.D + 16⟩ (by simp)
    simp only at h1 h2 h3 h4
    rw [s.afterMem, writeLog_out _ _ _ (afterLog_outL spf vf vl h1 h2 h3 h4)]

/-- The list head's word is outside the walk's writes. -/
theorem head_not_written {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (custom : Gc.CustomMemCall Ready state Customs) (g : WalkGeometry w n) {i : Nat} (hi : i < 8) :
    ¬ Written w state (Layout.sym_caml_all_opened_channels + i) := by
  have spl := g.spLow; have nl := g.nurseryLow; have dl := g.domainLow
  intro hw
  rcases hw with stk | nur | ⟨r', mem', lo, _⟩ | yng | hs | foot
  · walk_omega
  · walk_omega
  · have := (g.records r' mem').low; walk_omega
  · walk_omega
  · obtain ⟨c, ap, _, _⟩ := g.stateApart _ hs
    have := state_misses_head ap; omega
  · rcases foot with gl | ⟨lo, _, _⟩
    · simp only [VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange, Layout.sym_caml_all_opened_channels] at gl
      omega
    · walk_omega

/-- **A listed record**: its custom block and cons cell are allocated, `res`
is the new cell, and the walk moves on. -/
theorem walk_listed {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {e : Config} {pre rest : List Nat} {r : Nat} {d : Config} (custom : Gc.CustomMemCall Ready state Customs)
    (grows : CustomMemGrows state)
    (g : WalkGeometry w n) (h : WalkAt w Ready state Customs k e pre (r :: rest) d)
    (go : Listed e.σ.mem (BitVec.ofNat 64 r)) (count : (listedRecs e.σ.mem w.chs).length ≤ n) :
    ∃ d', Steps d d' ∧ WalkAt w Ready state Customs k e (pre ++ [r]) rest d' := by
  have mem : r ∈ w.chs := by rw [h.split]; simp
  obtain ⟨f, g', d', V, H, H', cap', s⟩ := walk_listed_run custom grows g h go count
  obtain ⟨vlm, vy, vl, vf, spf⟩ := s.nums g
  have yv := s.young
  have hr := g.records r mem
  have spl := g.spLow; have nh := g.nurseryHigh; have dh := g.domainHigh; have dap := g.domainApart
  have nl := g.nurseryLow; have dl := g.domainLow
  have split := h.split
  have nexts : ∀ r' ∈ w.chs, bytesT d'.σ.mem (r' + Gc.chanOffNext) 8 = bytesT d.σ.mem (r' + Gc.chanOffNext) 8 :=
    fun r' mem' => Reloc.bytesT_congr fun i hi => by
      rw [Nat.add_assoc]
      exact s.frame g mem _ (record_not_written custom g mem' (by
        simp only [Gc.chanOffNext, recBytes, chanOffBuff, OCaml.Bytecode.ioBufferSize]; omega)
        (by simp only [Gc.chanOffNext]; omega))
  have headEq : bytesT d'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT d.σ.mem Layout.sym_caml_all_opened_channels 8 :=
    Reloc.bytesT_congr fun i hi => s.frame g mem _ (head_not_written custom g hi)
  have list' : Gc.OpenChannels d'.σ.mem (rest.headD 0) rest := by
    have l : Gc.OpenChannels d.σ.mem r (r :: rest) := h.list
    cases l with
    | cons _ t =>
      rw [← (openChannels_head t).1]
      exact t.congr fun r' hr' => nexts r' (by rw [split]; simp [hr'])
  have rfit := hr.fit
  obtain ⟨nx, after⟩ := next_eq (m := d.σ.mem) (by walk_omega) (show Gc.OpenChannels d.σ.mem r (r :: rest) from h.list)
  have nextG : nextRec g'.σ.mem (BitVec.ofNat 64 r) = nextRec d.σ.mem (BitVec.ofNat 64 r) := by
    unfold nextRec; rw [rec_off (by walk_omega)]
    exact Reloc.bytesT_congr fun i hi => by
      rw [Nat.add_assoc]
      exact s.recordAtReturn custom g mem (by simp only [recBytes, chanOffBuff, OCaml.Bytecode.ioBufferSize]; omega)
        (by omega)
  have regs := s.regs
  rw [nextG, nx, s.roots custom g] at regs
  have s24 : (w.sp + 24#64).toNat = w.sp.toNat + 24 := off_toNat (by omega)
  have listedNew : listedRecs e.σ.mem (pre ++ [r]) = listedRecs e.σ.mem pre ++ [r] := listedRecs_go go
  have lenNew : (listedRecs e.σ.mem (pre ++ [r])).length = (listedRecs e.σ.mem pre).length + 1 := by
    rw [listedNew, List.length_append]; rfl
  have ns : ∀ n ∈ calleeSaved, n ∉ [10, 11, 15, 1, 6, 10, 12, 13, 14, 15, 16, 17, 12, 14, 15, 8, 13] ∧
      n ∉ [15, 10, 11, 12, 15, 1] ∧ 1 ≤ n ∧ n ≤ 31 := by decide
  obtain ⟨readyD, domD, stateD, countedD, ownedD, ledgerD, allocD⟩ := s.ready custom g
  refine ⟨d', s.run, {
    good := s.post.good, image := s.post.image, minstret := s.post.minstret, tick := s.post.tick
    link := ⟨cons_call.link, s.link, by decide⟩
    idle := (s.post.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans s.idleG
    pc := by rw [s.post.pc, nextG, after]
    regs := ⟨_, regs⟩
    saved := fun n hn => by
      obtain ⟨n1, n2, lo, hi⟩ := ns n hn
      exact (s.post.gpr_frame (by decide) n lo hi n1).trans ((s.savedG n hn).trans
        ((s.postF.gpr_frame (by decide) n lo hi n2).trans (h.saved n hn)))
    gprs := h.gprs.trans (s.postF.kept.trans (s.gprsG.trans s.post.kept))
    output := s.post.output.trans (s.outputG.trans (s.postF.output.trans h.output))
    split := by rw [split]; simp
    list := list'
    opened := opened_transfer h.opened headEq nexts
    records := fun r' mem' j' hj' hn =>
      (s.frame g mem _ (record_not_written custom g mem' hj' hn)).trans (h.records r' mem' j' hj' hn)
    refwords := by
      have nd := h.opened.nodup
      rw [h.split] at nd
      have fresh : r ∉ listedRecs e.σ.mem pre := by
        intro member
        have inPre := (List.mem_filter.mp member).1
        have disjoint := (List.nodup_append.mp nd).2.2
        exact disjoint r inPre r List.mem_cons_self rfl
      intro q hq
      rw [s.refwords custom g mem q hq, h.refwords q hq, listedNew]
      by_cases eq : q = r
      · subst q; simp [fresh]
      · simp [eq, BitVec.add_assoc]
    res := by
      rw [lenNew, s.afterMem]
      refine (Gc.word_writeLog_at _ _ 5 _ _ rfl (by
        simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, List.drop, OutLRange, s24, and_true]
        walk_omega)).trans ?_
      simp only [resWord, Nat.add_one_ne_zero, ↓reduceIte]; congr 1; omega
    domain := domD
    young := by
      rw [lenNew]; unfold word; rw [s.afterMem]
      refine (Gc.word_writeLog_at _ _ 3 _ _ rfl (by
        simp only [afterLog, consEnterLog, List.cons_append, List.nil_append, List.drop, OutLRange, s24, and_true]
        walk_omega)).trans ?_
      congr 1; omega
    limit := by
      rw [word_keep s.afterMem (afterLog_outLRange spf vf vl (by walk_omega) (by walk_omega) (by walk_omega)
        (by walk_omega))]
      exact s.limitG
    nursery := by
      rw [listedNew]
      exact NurseryList.snoc (h.nursery.frame (by omega) fun a lo hi => s.older custom g mem lo hi)
        (s.fresh custom g mem h.res)
    frame := fun a hw => (s.frame g mem a hw).trans (h.frame a hw)
    counted := by
      rw [lenNew]
      simpa using ((h.counted.trans s.countedF).trans s.countedG).trans countedD
    ready := readyD
    heap := ⟨H', cap', s.heap g, ownedD, ledgerD, fun x hx => s.sub' x (s.sub x hx)⟩
    stateIn := stateD
    allocIn := fun a ha => by
      rcases s.allocGrowth a (allocD a ha) with old | free
      · exact h.allocIn a old
      · exact Or.inr free }⟩

/-- Any two invariants at one configuration name the same rest of the list. -/
theorem WalkAt.rest_unique {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre pre' rest rest' : List Nat} {d : Config} (g : WalkGeometry w n)
    (h : WalkAt w Ready state Customs k e pre rest d) (h' : WalkAt w Ready state Customs k e pre' rest' d) : rest = rest' := by
  have small : ∀ {p q : List Nat}, w.chs = p ++ q → q.headD 0 < 2 ^ 64 := fun {p q} sp => by
    cases q with
    | nil => simp
    | cons x _ => have := (g.records x (by rw [sp]; simp)).fit; simp; walk_omega
  obtain ⟨a0, r1⟩ := h.regs
  obtain ⟨a0', r2⟩ := h'.regs
  have heads : rest.headD 0 = rest'.headD 0 := by
    have e1 := r1.record.symm.trans r2.record
    simp only [Option.some.injEq] at e1
    have := congrArg BitVec.toNat e1
    rwa [toNat_ofNat_small (small h.split), toNat_ofNat_small (small h'.split)] at this
  have l2 := h'.list
  rw [← heads] at l2
  exact h.list.unique l2

open Classical in
/-- The walk's rank: the length of the list left at `d`. -/
noncomputable def walkRank (w : Walk) (Ready : Nat → Config → Prop) (state : Config → Nat → Prop) (k : Nat)
    (e : Config) (d : Config) : Nat :=
  if h : ∃ rest, ∃ pre, WalkAt w Ready state Customs k e pre rest d then (Classical.choose h).length else 0

theorem walkRank_eq {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    {k : Nat} {e : Config} {pre rest : List Nat} {d : Config} (g : WalkGeometry w n)
    (h : WalkAt w Ready state Customs k e pre rest d) : walkRank (Customs := Customs) w Ready state k e d = rest.length := by
  have ex : ∃ rest, ∃ pre, WalkAt w Ready state Customs k e pre rest d := ⟨rest, pre, h⟩
  unfold walkRank; rw [dite_cond_eq_true (eq_true ex)]
  obtain ⟨pre', h'⟩ := Classical.choose_spec ex
  rw [h'.rest_unique g h]

/-- **The walk**: from its first visit to `leave`, every record visited. -/
theorem walk_loop {w : Walk} {n : Nat} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {e : Config} (custom : Gc.CustomMemCall Ready state Customs) (grows : CustomMemGrows state) (g : WalkGeometry w n)
    (count : (listedRecs e.σ.mem w.chs).length ≤ n) (start : WalkAt w Ready state Customs k e [] w.chs e) :
    ∃ d, Steps e d ∧ WalkAt w Ready state Customs k e w.chs [] d := by
  let active := fun d => ∃ pre r rest, WalkAt w Ready state Customs k e pre (r :: rest) d
  let finished := fun d => WalkAt w Ready state Customs k e w.chs [] d
  have T : Vsa.Logic.Triple active finished := by
    apply Gc.loop_to_exit (entry := headPc) (walkRank (Customs := Customs) w Ready state k e)
    · intro c ⟨pre, r, rest, h⟩; exact (by simpa using h.pc : pcOf c = some headPc)
    · intro c h pc
      have := h.pc
      simp only [↓reduceIte] at this
      have e2 : some exitPc = some headPc := this.symm.trans pc
      exact absurd e2 (by decide)
    · intro c ⟨pre, r, rest, h⟩
      have step : ∃ d', Steps c d' ∧ WalkAt w Ready state Customs k e (pre ++ [r]) rest d' := by
        by_cases go : Listed e.σ.mem (BitVec.ofNat 64 r)
        · exact walk_listed custom grows g h go count
        · exact walk_skip custom g h go
      obtain ⟨d', run, h'⟩ := step
      refine ⟨d', run, ?_, ?_⟩
      · cases rest with
        | nil =>
          right
          have sp := h'.split
          rw [List.append_nil] at sp
          rw [← sp] at h'
          exact h'
        | cons r' rest' => exact Or.inl ⟨_, r', rest', h'⟩
      · rw [walkRank_eq g h, walkRank_eq g h']; simp
  by_cases empty : w.chs = []
  · have s0 := start; rw [empty] at s0
    exact ⟨e, .refl e, by rw [empty]; exact s0⟩
  · obtain ⟨r, rest, hrs⟩ := List.exists_cons_of_ne_nil empty
    have s0 := start; rw [hrs] at s0
    exact T e ⟨[], r, rest, s0⟩

end OCaml.Vm.Sim.OutListWalk
