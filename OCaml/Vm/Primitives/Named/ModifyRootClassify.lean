import OCaml.Vm.Primitives.Named.ModifyRootRun

/-!
# Classifying a value in `caml_modify_generational_global_root`

The function classifies the new value `v` once and the old `w = *r` once on
each of three paths: immediate (low bit set), young (between `young_start`
and `young_end`), old (`In_heap` by the page table), or none of these. Every
classification is the same four decisions: the low bit, `young_end`,
`young_start`, and the page-table bit. `classify` composes them over any state
predicate, and `Lands` names the three exits. `WBlocks` bundles the blocks
that the old-`v` and other-`v` paths share, and `wClassify` classifies `w` for
either path. Before the first list call the run stays `Settled`: `Acting`, with
the memory after the prologue.
-/

namespace OCaml.Vm.Primitives.Named.ModifyRoot
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Gc OCaml.Vm.Gc.Skiplist
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady nativeFrameBase)
open NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif wl_nil)
open RegisterRoot (Young Old rootValue YoungAt ListsFoot IsList lists_kept)

variable {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
  {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}

/-- A register of a block's post, its value rewritten. -/
theorem holds_at {σ : MState} {L : GRegs} {n : Nat} {a b : BitVec 64} (h : GHolds σ L) (hl : lookupG n L = some a)
    (e : a = b) : gprGet σ n = some b := e ▸ gholds_lookup _ h hl

/-- The page-table bit of `w`: `In_heap`. -/
def HeapBit (cls : Nat → Nat) (w : BitVec 64) : Prop := BitVec.ofNat 64 (cls (w.toNat / 4096)) &&& 1#64 ≠ 0#64

/-- **Where a classification exits**: at `pY` (with `Y`) for a young `w`, at
`pO` for an old one, at `pN` for any other. -/
inductive Lands (start stop : BitVec 64) (cls : Nat → Nat) (w pY pO pN : BitVec 64) (Y : Config → Prop)
    (y : Config) : Prop
  | young : Young start stop w → PCAt pY y → Y y → Lands start stop cls w pY pO pN Y y
  | old : Old start stop cls w → PCAt pO y → Lands start stop cls w pY pO pN Y y
  | none : ¬ Young start stop w → ¬ Old start stop cls w → PCAt pN y → Lands start stop cls w pY pO pN Y y

/-- **The four decisions**: from `E` (past the low bit), `young_end` leads to
the page table (`L`) or to `young_start` (`S`), which leads to the young exit or
the page table, whose bit picks the old or the other exit. -/
theorem classify {St E S L Y : Config → Prop} {pY pO pN start stop w : BitVec 64} {cls : Nat → Nat}
    (blk : w &&& 1#64 = 0#64)
    (endStep : ∀ x, St x → E x → ∃ y, Steps x y ∧ St y ∧
      (stop.toNat ≤ w.toNat ∧ L y ∨ w.toNat < stop.toNat ∧ S y))
    (startStep : ∀ x, St x → S x → ∃ y, Steps x y ∧ St y ∧
      (start.toNat < w.toNat ∧ PCAt pY y ∧ Y y ∨ w.toNat ≤ start.toNat ∧ L y))
    (lookStep : ∀ x, St x → L x → ∃ y, Steps x y ∧ St y ∧
      (HeapBit cls w ∧ PCAt pO y ∨ ¬ HeapBit cls w ∧ PCAt pN y))
    {x : Config} (s : St x) (e : E x) :
    ∃ y, Steps x y ∧ St y ∧ Lands start stop cls w pY pO pN Y y := by
  have fromL (x1 : Config) (s1 : St x1) (l1 : L x1) (ny : ¬ Young start stop w) :
      ∃ y, Steps x1 y ∧ St y ∧ Lands start stop cls w pY pO pN Y y := by
    obtain ⟨y, run, sy, out⟩ := lookStep x1 s1 l1
    rcases out with ⟨b, pc⟩ | ⟨b, pc⟩
    · exact ⟨y, run, sy, .old ⟨blk, fun p => ny ⟨blk, p⟩, b⟩ pc⟩
    · exact ⟨y, run, sy, .none ny (fun o => b o.2.2) pc⟩
  obtain ⟨x1, run1, s1, out1⟩ := endStep x s e
  rcases out1 with ⟨ge, l1⟩ | ⟨lt, s1'⟩
  · obtain ⟨y, run, sy, ly⟩ := fromL x1 s1 l1 fun yg => by have := yg.2.1; omega
    exact ⟨y, run1.trans run, sy, ly⟩
  · obtain ⟨x2, run2, s2, out2⟩ := startStep x1 s1 s1'
    rcases out2 with ⟨gt, pc, yy⟩ | ⟨le, l2⟩
    · exact ⟨x2, run1.trans run2, s2, .young ⟨blk, lt, gt⟩ pc yy⟩
    · obtain ⟨y, run, sy, ly⟩ := fromL x2 s2 l2 fun yg => by have := yg.2.2; omega
      exact ⟨y, run1.trans (run2.trans run), sy, ly⟩

/-- `classify` behind the low-bit decision `I`: an immediate exits at `pN`. -/
theorem classifyImm {St I E S L Y : Config → Prop} {pY pO pN start stop w : BitVec 64} {cls : Nat → Nat}
    (immStep : ∀ x, St x → I x → ∃ y, Steps x y ∧ St y ∧
      (w &&& 1#64 ≠ 0#64 ∧ PCAt pN y ∨ w &&& 1#64 = 0#64 ∧ E y))
    (endStep : ∀ x, St x → E x → ∃ y, Steps x y ∧ St y ∧
      (stop.toNat ≤ w.toNat ∧ L y ∨ w.toNat < stop.toNat ∧ S y))
    (startStep : ∀ x, St x → S x → ∃ y, Steps x y ∧ St y ∧
      (start.toNat < w.toNat ∧ PCAt pY y ∧ Y y ∨ w.toNat ≤ start.toNat ∧ L y))
    (lookStep : ∀ x, St x → L x → ∃ y, Steps x y ∧ St y ∧
      (HeapBit cls w ∧ PCAt pO y ∨ ¬ HeapBit cls w ∧ PCAt pN y))
    {x : Config} (s : St x) (i : I x) :
    ∃ y, Steps x y ∧ St y ∧ Lands start stop cls w pY pO pN Y y := by
  obtain ⟨x1, run1, s1, out⟩ := immStep x s i
  rcases out with ⟨imm, pc⟩ | ⟨blk, e⟩
  · exact ⟨x1, run1, s1, .none (fun yg => imm yg.1) (fun o => imm o.1) pc⟩
  · obtain ⟨y, run, sy, ly⟩ := classify blk endStep startStep lookStep s1 e
    exact ⟨y, run1.trans run, sy, ly⟩

/-! ### Steps from `Acting` -/

/-- The link register as a leaf input. -/
theorem Acting.leaf {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {c x : Config} (act : Acting Shape foot H0 m1 sp v r rs c x ys os) :
    LeafInput (regsAt x 1) x := by
  obtain ⟨l, hl, al⟩ := act.link
  rw [regsAt_of hl]
  exact ⟨act.good, act.image, act.minstret, hl, al, act.tick⟩

/-- **A block writing temporaries only, from `Acting`.** -/
theorem Acting.line {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {c x : Config} (act : Acting Shape foot H0 m1 sp v r rs c x ys os)
    {p q val : BitVec 64} {writes : List Nat} {regs : GRegs} (pc0 : PCAt p x) (keys : KeysOK writes)
    (temps : ∀ n ∈ writes, 10 ≤ n ∧ n ≤ 17)
    (blk : FnSummary p (fun d => d = x) (WriteRegistersPost writes [] x q val regs)) :
    ∃ y, Steps x y ∧ Acting Shape foot H0 m1 sp v r rs c y ys os ∧ y.σ.mem = x.σ.mem ∧
      WriteRegistersPost writes [] x q val regs y := by
  obtain ⟨y, run, p⟩ := blk.run x ⟨pc0, rfl⟩
  exact ⟨y, run, act.temps p keys temps (gpr_some_of p.result), by rw [p.memory, wl_nil], p⟩

/-- **A two-way block from `Acting`**: the taken twin when the guard `g`
holds, the fall-through twin otherwise. -/
theorem Acting.branch {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {c x : Config} (act : Acting Shape foot H0 m1 sp v r rs c x ys os)
    {p qT qF val : BitVec 64} {writes : List Nat} {regsT regsF : GRegs} (pc0 : PCAt p x) (g : Bool)
    (keys : KeysOK writes) (temps : ∀ n ∈ writes, 10 ≤ n ∧ n ≤ 17)
    (taken : g = true → FnSummary p (fun d => d = x) (WriteRegistersPost writes [] x qT val regsT))
    (fall : g = false → FnSummary p (fun d => d = x) (WriteRegistersPost writes [] x qF val regsF)) :
    ∃ y, Steps x y ∧ Acting Shape foot H0 m1 sp v r rs c y ys os ∧ y.σ.mem = x.σ.mem ∧
      (g = true ∧ WriteRegistersPost writes [] x qT val regsT y ∨
        g = false ∧ WriteRegistersPost writes [] x qF val regsF y) := by
  cases hg : g
  · obtain ⟨y, run, a, mem, p⟩ := act.line pc0 keys temps (fall hg)
    exact ⟨y, run, a, mem, Or.inr ⟨rfl, p⟩⟩
  · obtain ⟨y, run, a, mem, p⟩ := act.line pc0 keys temps (taken hg)
    exact ⟨y, run, a, mem, Or.inl ⟨rfl, p⟩⟩

/-- **Before any list call**: `Acting` with the memory after the prologue. -/
structure Settled (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H0 : List (Nat × Nat)) (m1 : Std.ExtHashMap Nat (BitVec 8)) (sp v r : BitVec 64) (rs : List (BitVec 64))
    (c : Config) (ys os : List (BitVec 64)) (x : Config) : Prop where
  acting : Acting Shape foot H0 m1 sp v r rs c x ys os
  memory : x.σ.mem = m1

/-! ### The page-table decision -/

/-- **The page-table decision**: the lookup's block (`a0 = w`), the call,
`caml_page_table_lookup`, and the bit's twin blocks, which exit at `pO` for
`In_heap` and at `pN` otherwise. -/
theorem Settled.look {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (pt : PageTableLookup Table)
    {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {c x : Config} {call : CallInstr} {w pO pN : BitVec 64}
    (shape : CallShape call) (decode : CallDecode call) (pins : ∀ y : Config, ExecutableImage y → CallPins call y)
    (target : call.target = pageTableLookupPc) (aligned : call.link.toNat % 4 = 0)
    (s : Settled Shape foot H0 m1 sp v r rs c ys os x) (table : Table m1 cls)
    {writes : List Nat} {regs : GRegs} (keys : KeysOK writes) (temps : ∀ n ∈ writes, 10 ≤ n ∧ n ≤ 17)
    (blk : ∃ y, Steps x y ∧ WriteRegistersPost writes [] x call.pc w regs y) (wr : lookupG 10 regs = some w)
    (notHeap : ∀ y, LeafInput (regsAt y 1) y →
      GHolds y.σ [(8, regsAt y 8), (9, regsAt y 9), (10, regsAt y 10)] →
      guardB .BEQ (regsAt y 10 &&& 1#64) 0#64 = true →
      FnSummary call.link (fun d => d = y) (WriteRegistersPost [10] [] y pN (regsAt y 10 &&& 1#64)
        [(10, regsAt y 10 &&& 1#64), (8, regsAt y 8), (9, regsAt y 9)]))
    (heap : ∀ y, LeafInput (regsAt y 1) y →
      GHolds y.σ [(8, regsAt y 8), (9, regsAt y 9), (10, regsAt y 10)] →
      guardB .BEQ (regsAt y 10 &&& 1#64) 0#64 = false →
      FnSummary call.link (fun d => d = y) (WriteRegistersPost [10] [] y pO (regsAt y 10 &&& 1#64)
        [(10, regsAt y 10 &&& 1#64), (8, regsAt y 8), (9, regsAt y 9)])) :
    ∃ y, Steps x y ∧ Settled Shape foot H0 m1 sp v r rs c ys os y ∧
      (HeapBit cls w ∧ PCAt pO y ∨ ¬ HeapBit cls w ∧ PCAt pN y) := by
  obtain ⟨y1, run1, pc1, act1, mem1, bit⟩ := s.acting.lookup pt shape decode pins target aligned s.memory
    table keys temps blk wr
  have b10 : regsAt y1 10 = BitVec.ofNat 64 (cls (w.toNat / 4096)) := regsAt_of bit
  have regs1 : GHolds y1.σ [(8, regsAt y1 8), (9, regsAt y1 9), (10, regsAt y1 10)] :=
    ⟨gpr_some (gpr_some_of act1.s0), gpr_some (gpr_some_of act1.s1), gpr_some act1.a0, trivial⟩
  obtain ⟨y, run, act, mem, out⟩ := act1.branch pc1 (guardB .BEQ (regsAt y1 10 &&& 1#64) 0#64) (by decide)
    (by decide) (notHeap y1 act1.leaf regs1) (heap y1 act1.leaf regs1)
  refine ⟨y, run1.trans run, ⟨act, mem.trans mem1⟩, ?_⟩
  rcases out with ⟨g, p⟩ | ⟨g, p⟩
  · exact Or.inr ⟨fun hb => hb (by rw [b10] at g; simpa [guardB] using g), p.pc⟩
  · exact Or.inl ⟨by rw [b10] at g; simpa [HeapBit, guardB] using g, p.pc⟩

/-! ### The shared `w` blocks -/

/-- **The blocks classifying `w = *r`** on the old-`v` and other-`v` paths:
the low bit (`pImm`), `Caml_state` (`pState`), `young_end` (`pEnd`),
`young_start` (`pStart`), the page-table call (`pLook`, `call`) and its bit
(at `call.link`). -/
structure WBlocks (pImm pState pEnd pStart pLook pY pO pN : BitVec 64) (call : CallInstr) : Prop where
  imm : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x → GHolds x.σ [(8, R 8), (9, R 9), (10, R 10)] →
    ReadWindow (R 9) 8 → guardB .BNE (bytesVal .ld (read8 x.σ.mem (R 9).toNat) &&& 1#64) 0#64 = true →
    FnSummary pImm (fun d => d = x) (WriteRegistersPost [10, 15] [] x pN (bytesVal .ld (read8 x.σ.mem (R 9).toNat))
      [(15, bytesVal .ld (read8 x.σ.mem (R 9).toNat) &&& 1#64), (10, bytesVal .ld (read8 x.σ.mem (R 9).toNat)),
        (8, R 8), (9, R 9)])
  block : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x → GHolds x.σ [(8, R 8), (9, R 9), (10, R 10)] →
    ReadWindow (R 9) 8 → guardB .BNE (bytesVal .ld (read8 x.σ.mem (R 9).toNat) &&& 1#64) 0#64 = false →
    FnSummary pImm (fun d => d = x) (WriteRegistersPost [10, 15] [] x pState
      (bytesVal .ld (read8 x.σ.mem (R 9).toNat))
      [(15, bytesVal .ld (read8 x.σ.mem (R 9).toNat) &&& 1#64), (10, bytesVal .ld (read8 x.σ.mem (R 9).toNat)),
        (8, R 8), (9, R 9)])
  state : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(8, R 8), (9, R 9), (10, R 10)] →
    FnSummary pState (fun d => d = x) (WriteRegistersPost [15] [] x pEnd (R 10)
      [(15, bytesVal .ld (read8 x.σ.mem (0x80064d08#64).toNat)), (8, R 8), (9, R 9), (10, R 10)])
  aboveEnd : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(8, R 8), (9, R 9), (10, R 10), (15, R 15)] → ReadWindow (R 15 + 40#64) 8 →
    guardB .BGEU (R 10) (bytesVal .ld (read8 x.σ.mem (R 15 + 40#64).toNat)) = true →
    FnSummary pEnd (fun d => d = x) (WriteRegistersPost [14] [] x pLook (R 10)
      [(14, bytesVal .ld (read8 x.σ.mem (R 15 + 40#64).toNat)), (8, R 8), (9, R 9), (10, R 10), (15, R 15)])
  belowEnd : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(8, R 8), (9, R 9), (10, R 10), (15, R 15)] → ReadWindow (R 15 + 40#64) 8 →
    guardB .BGEU (R 10) (bytesVal .ld (read8 x.σ.mem (R 15 + 40#64).toNat)) = false →
    FnSummary pEnd (fun d => d = x) (WriteRegistersPost [14] [] x pStart (R 10)
      [(14, bytesVal .ld (read8 x.σ.mem (R 15 + 40#64).toNat)), (8, R 8), (9, R 9), (10, R 10), (15, R 15)])
  young : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(8, R 8), (9, R 9), (10, R 10), (15, R 15)] → ReadWindow (R 15 + 32#64) 8 →
    guardB .BLTU (bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat)) (R 10) = true →
    FnSummary pStart (fun d => d = x) (WriteRegistersPost [15] [] x pY (R 10)
      [(15, bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat)), (8, R 8), (9, R 9), (10, R 10)])
  notYoung : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(8, R 8), (9, R 9), (10, R 10), (15, R 15)] → ReadWindow (R 15 + 32#64) 8 →
    guardB .BLTU (bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat)) (R 10) = false →
    FnSummary pStart (fun d => d = x) (WriteRegistersPost [15] [] x pLook (R 10)
      [(15, bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat)), (8, R 8), (9, R 9), (10, R 10)])
  look : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x →
    GHolds x.σ [(1, R 1), (8, R 8), (9, R 9), (10, R 10)] →
    FnSummary pLook (fun d => d = x) (WriteRegistersPost [] [] x call.pc (R 10) [(1, R 1), (8, R 8), (9, R 9), (10, R 10)])
  callShape : CallShape call
  callDecode : CallDecode call
  callPins : ∀ y : Config, ExecutableImage y → CallPins call y
  target : call.target = pageTableLookupPc
  linkAligned : call.link.toNat % 4 = 0
  notHeap : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x → GHolds x.σ [(8, R 8), (9, R 9), (10, R 10)] →
    guardB .BEQ (R 10 &&& 1#64) 0#64 = true →
    FnSummary call.link (fun d => d = x) (WriteRegistersPost [10] [] x pN (R 10 &&& 1#64)
      [(10, R 10 &&& 1#64), (8, R 8), (9, R 9)])
  heap : ∀ (x : Config) (R : Nat → BitVec 64), LeafInput (R 1) x → GHolds x.σ [(8, R 8), (9, R 9), (10, R 10)] →
    guardB .BEQ (R 10 &&& 1#64) 0#64 = false →
    FnSummary call.link (fun d => d = x) (WriteRegistersPost [10] [] x pO (R 10 &&& 1#64)
      [(10, R 10 &&& 1#64), (8, R 8), (9, R 9)])

/-- **`w = *r` classified** on the old-`v` or other-`v` path. -/
theorem wClassify {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (pt : PageTableLookup Table)
    {pImm pState pEnd pStart pLook pY pO pN : BitVec 64} {call : CallInstr}
    (B : WBlocks pImm pState pEnd pStart pLook pY pO pN call)
    {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {D start stop w : BitVec 64} {c x : Config}
    (table : Table m1 cls) (young : YoungAt m1 D start stop) (win : ReadWindow r 8)
    (hw : bytesVal .ld (read8 m1 r.toNat) = w)
    (s : Settled Shape foot H0 m1 sp v r rs c ys os x) (pc0 : PCAt pImm x) :
    ∃ y, Steps x y ∧ Settled Shape foot H0 m1 sp v r rs c ys os y ∧
      Lands start stop cls w pY pO pN (fun _ => True) y := by
  refine classifyImm (St := Settled Shape foot H0 m1 sp v r rs c ys os) (I := fun y => PCAt pImm y)
    (E := fun y => PCAt pState y ∧ gprGet y.σ 10 = some w)
    (S := fun y => PCAt pStart y ∧ gprGet y.σ 10 = some w ∧ gprGet y.σ 15 = some D)
    (L := fun y => PCAt pLook y ∧ gprGet y.σ 10 = some w) ?_ ?_ ?_ ?_ s pc0
  · -- the low bit
    intro x s pc0
    let R := regsAt x
    have r9 : R 9 = r := regsAt_of s.acting.s1
    have val : bytesVal .ld (read8 x.σ.mem (R 9).toNat) = w := by rw [r9, s.memory, hw]
    have regs : GHolds x.σ [(8, R 8), (9, R 9), (10, R 10)] :=
      ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some s.acting.a0, trivial⟩
    have w9 : ReadWindow (R 9) 8 := by rw [r9]; exact win
    obtain ⟨y, run, act, mem, out⟩ := s.acting.branch pc0
      (guardB .BNE (bytesVal .ld (read8 x.σ.mem (R 9).toNat) &&& 1#64) 0#64) (by decide) (by decide)
      (B.imm x R s.acting.leaf regs w9) (B.block x R s.acting.leaf regs w9)
    refine ⟨y, run, ⟨act, mem.trans s.memory⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · exact Or.inl ⟨by rw [val] at g; simpa [guardB] using g, p.pc⟩
    · exact Or.inr ⟨by rw [val] at g; simpa [guardB] using g, p.pc, holds_at p.regs rfl val⟩
  · -- `young_end`
    intro x s ⟨pc0, a0⟩
    let R := regsAt x
    have r10 : R 10 = w := regsAt_of a0
    obtain ⟨x1, run1, act1, mem1, p1⟩ := s.acting.line pc0 (by decide) (by decide)
      (B.state x R s.acting.leaf
        ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0), trivial⟩)
    have m1' : x1.σ.mem = m1 := mem1.trans s.memory
    have d15 : gprGet x1.σ 15 = some D := holds_at p1.regs rfl (by rw [s.memory]; exact young.state)
    have x1_10 : gprGet x1.σ 10 = some w := holds_at p1.regs rfl r10
    let R1 := regsAt x1
    have r1_15 : R1 15 = D := regsAt_of d15
    have r1_10 : R1 10 = w := regsAt_of x1_10
    have stopV : bytesVal .ld (read8 x1.σ.mem (R1 15 + 40#64).toNat) = stop := by
      rw [r1_15, m1']; exact young.stopWord
    have regs1 : GHolds x1.σ [(8, R1 8), (9, R1 9), (10, R1 10), (15, R1 15)] :=
      ⟨gpr_some (gpr_some_of act1.s0), gpr_some (gpr_some_of act1.s1), gpr_some act1.a0, gpr_some (gpr_some_of d15),
        trivial⟩
    have win1 : ReadWindow (R1 15 + 40#64) 8 := by rw [r1_15]; exact young.stopWin
    obtain ⟨y, run, act, mem, out⟩ := act1.branch p1.pc
      (guardB .BGEU (R1 10) (bytesVal .ld (read8 x1.σ.mem (R1 15 + 40#64).toNat))) (by decide) (by decide)
      (B.aboveEnd x1 R1 act1.leaf regs1 win1) (B.belowEnd x1 R1 act1.leaf regs1 win1)
    refine ⟨y, run1.trans run, ⟨act, mem.trans m1'⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · have := bgeu_true _ _ g
      rw [stopV, r1_10] at this
      exact Or.inl ⟨this, p.pc, holds_at p.regs rfl r1_10⟩
    · have := bgeu_false _ _ g
      rw [stopV, r1_10] at this
      exact Or.inr ⟨this, p.pc, holds_at p.regs rfl r1_10, holds_at p.regs rfl r1_15⟩
  · -- `young_start`
    intro x s ⟨pc0, a0, d15⟩
    let R := regsAt x
    have r10 : R 10 = w := regsAt_of a0
    have r15 : R 15 = D := regsAt_of d15
    have startV : bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat) = start := by
      rw [r15, s.memory]; exact young.startWord
    have regs : GHolds x.σ [(8, R 8), (9, R 9), (10, R 10), (15, R 15)] :=
      ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0),
        gpr_some (gpr_some_of d15), trivial⟩
    have win : ReadWindow (R 15 + 32#64) 8 := by rw [r15]; exact young.startWin
    obtain ⟨y, run, act, mem, out⟩ := s.acting.branch pc0
      (guardB .BLTU (bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat)) (R 10)) (by decide) (by decide)
      (B.young x R s.acting.leaf regs win) (B.notYoung x R s.acting.leaf regs win)
    refine ⟨y, run, ⟨act, mem.trans s.memory⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · have := bltu_true _ _ g
      rw [startV, r10] at this
      exact Or.inl ⟨this, p.pc, trivial⟩
    · have := bltu_false _ _ g
      rw [startV, r10] at this
      exact Or.inr ⟨this, p.pc, holds_at p.regs rfl r10⟩
  · -- the page table
    intro x s ⟨pc0, a0⟩
    let R := regsAt x
    have r10 : R 10 = w := regsAt_of a0
    obtain ⟨l, hl, -⟩ := s.acting.link
    have blk := (B.look x R s.acting.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of s.acting.s0),
      gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0), trivial⟩).run x ⟨pc0, rfl⟩
    rw [r10] at blk
    exact s.look pt B.callShape B.callDecode B.callPins B.target B.linkAligned table (by decide) (by decide) blk
      (by rw [← r10]; rfl) (fun y => B.notHeap y (regsAt y)) (fun y => B.heap y (regsAt y))

/-- The `w` blocks of the old-`v` path: an immediate or unboxed `w` inserts
`r` in the old list (`0x8000cc48`), a young or old one stores (`0x8000cb80`). -/
theorem oBlocks : WBlocks 0x8000cb50#64 0x8000cb5c#64 0x8000cb64#64 0x8000cb6c#64 0x8000cb74#64 0x8000cb80#64
    0x8000cb80#64 0x8000cc48#64 oldLookup_call where
  imm := oldImm_fast
  block := oldBlock_fast
  state := oldState_fast
  aboveEnd := oldAboveEnd_fast
  belowEnd := oldBelowEnd_fast
  young := oldYoung_fast
  notYoung := oldNotYoung_fast
  look := oldLookup_fast
  callShape := oldLookup_call_shape
  callDecode := oldLookup_call_decode
  callPins := fun _ h => oldLookup_call_pins h
  target := oldLookup_call_target
  linkAligned := by decide
  notHeap := fun x R h g ok => by
    rw [show oldLookup_call.link = 0x8000cb78#64 by decide]; exact oldNotHeap_fast x R h g ok
  heap := fun x R h g ok => by
    rw [show oldLookup_call.link = 0x8000cb78#64 by decide]; exact oldHeap_fast x R h g ok

/-- The `w` blocks of the other-`v` path: a young `w` leaves the young list
(`0x8000cc20`), an old one both lists (`0x8000cc10`), any other stores
(`0x8000cb80`). -/
theorem xBlocks : WBlocks 0x8000cbe0#64 0x8000cbec#64 0x8000cbf4#64 0x8000cbfc#64 0x8000cc04#64 0x8000cc20#64
    0x8000cc10#64 0x8000cb80#64 xLookup_call where
  imm := xImm_fast
  block := xBlock_fast
  state := xState_fast
  aboveEnd := xAboveEnd_fast
  belowEnd := xBelowEnd_fast
  young := xYoung_fast
  notYoung := xNotYoung_fast
  look := xLookup_fast
  callShape := xLookup_call_shape
  callDecode := xLookup_call_decode
  callPins := fun _ h => xLookup_call_pins h
  target := xLookup_call_target
  linkAligned := by decide
  notHeap := fun x R h g ok => by
    rw [show xLookup_call.link = 0x8000cc08#64 by decide]; exact xNotHeap_fast x R h g ok
  heap := fun x R h g ok => by
    rw [show xLookup_call.link = 0x8000cc08#64 by decide]; exact xHeap_fast x R h g ok

/-! ### The new value and the young-`v` path -/

/-- The young exit of `v`'s classification: `a0 = r`, `a3 = young_end`,
`a5 = young_start`, which the young-`v` path reuses. -/
structure YoungRegs (r start stop : BitVec 64) (y : Config) : Prop where
  slot : gprGet y.σ 10 = some r
  stop : gprGet y.σ 13 = some stop
  start : gprGet y.σ 15 = some start

/-- **`v` classified** (a block `v`, from `0x8000cb28`): young to
`0x8000cb98`, old to `0x8000cb50`, other to `0x8000cbe0`. -/
theorem vClassify {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (pt : PageTableLookup Table)
    {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {D start stop : BitVec 64} {c x : Config}
    (table : Table m1 cls) (young : YoungAt m1 D start stop) (blk : v &&& 1#64 = 0#64)
    (s : Settled Shape foot H0 m1 sp v r rs c ys os x) (pc0 : PCAt 0x8000cb28#64 x)
    (a0 : gprGet x.σ 10 = some r) (a1 : gprGet x.σ 11 = some v) :
    ∃ y, Steps x y ∧ Settled Shape foot H0 m1 sp v r rs c ys os y ∧
      Lands start stop cls v 0x8000cb98#64 0x8000cb50#64 0x8000cbe0#64 (YoungRegs r start stop) y := by
  refine classify (St := Settled Shape foot H0 m1 sp v r rs c ys os)
    (E := fun y => PCAt 0x8000cb28#64 y ∧ gprGet y.σ 10 = some r ∧ gprGet y.σ 11 = some v)
    (S := fun y => PCAt 0x8000cb38#64 y ∧ gprGet y.σ 10 = some r ∧ gprGet y.σ 11 = some v ∧
      gprGet y.σ 13 = some stop ∧ gprGet y.σ 15 = some D)
    (L := fun y => PCAt 0x8000cb40#64 y) blk ?_ ?_ ?_ s ⟨pc0, a0, a1⟩
  · -- `Caml_state` and `young_end`
    intro x s ⟨pc0, a0, a1⟩
    let R := regsAt x
    have r10 : R 10 = r := regsAt_of a0
    have r11 : R 11 = v := regsAt_of a1
    obtain ⟨x1, run1, act1, mem1, p1⟩ := s.acting.line pc0 (by decide) (by decide)
      (newState_fast x R s.acting.leaf ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1),
        gpr_some (gpr_some_of a0), gpr_some (gpr_some_of a1), trivial⟩)
    have m1' : x1.σ.mem = m1 := mem1.trans s.memory
    have d15 : gprGet x1.σ 15 = some D := holds_at p1.regs rfl (by rw [s.memory]; exact young.state)
    have x1_10 : gprGet x1.σ 10 = some r := holds_at p1.regs rfl r10
    have x1_11 : gprGet x1.σ 11 = some v := holds_at p1.regs rfl r11
    let R1 := regsAt x1
    have r1_15 : R1 15 = D := regsAt_of d15
    have r1_10 : R1 10 = r := regsAt_of x1_10
    have r1_11 : R1 11 = v := regsAt_of x1_11
    have stopV : bytesVal .ld (read8 x1.σ.mem (R1 15 + 40#64).toNat) = stop := by
      rw [r1_15, m1']; exact young.stopWord
    have regs1 : GHolds x1.σ (newAboveEnd_input R1) :=
      ⟨gpr_some (gpr_some_of act1.s0), gpr_some (gpr_some_of act1.s1), gpr_some (gpr_some_of x1_10),
        gpr_some (gpr_some_of x1_11), gpr_some (gpr_some_of d15), trivial⟩
    have win1 : ReadWindow (R1 15 + 40#64) 8 := by rw [r1_15]; exact young.stopWin
    obtain ⟨y, run, act, mem, out⟩ := act1.branch p1.pc
      (guardB .BGEU (R1 11) (bytesVal .ld (read8 x1.σ.mem (R1 15 + 40#64).toNat))) (by decide) (by decide)
      (newAboveEnd_fast x1 R1 act1.leaf regs1 win1) (newBelowEnd_fast x1 R1 act1.leaf regs1 win1)
    refine ⟨y, run1.trans run, ⟨act, mem.trans m1'⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · have := bgeu_true _ _ g
      rw [stopV, r1_11] at this
      exact Or.inl ⟨this, p.pc⟩
    · have := bgeu_false _ _ g
      rw [stopV, r1_11] at this
      exact Or.inr ⟨this, p.pc, holds_at p.regs rfl r1_10, holds_at p.regs rfl r1_11, holds_at p.regs rfl stopV,
        holds_at p.regs rfl r1_15⟩
  · -- `young_start`
    intro x s ⟨pc0, a0, a1, a3, d15⟩
    let R := regsAt x
    have r10 : R 10 = r := regsAt_of a0
    have r11 : R 11 = v := regsAt_of a1
    have r13 : R 13 = stop := regsAt_of a3
    have r15 : R 15 = D := regsAt_of d15
    have startV : bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat) = start := by
      rw [r15, s.memory]; exact young.startWord
    have regs : GHolds x.σ (newYoung_input R) :=
      ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0),
        gpr_some (gpr_some_of a1), gpr_some (gpr_some_of a3), gpr_some (gpr_some_of d15), trivial⟩
    have win : ReadWindow (R 15 + 32#64) 8 := by rw [r15]; exact young.startWin
    obtain ⟨y, run, act, mem, out⟩ := s.acting.branch pc0
      (guardB .BLTU (bytesVal .ld (read8 x.σ.mem (R 15 + 32#64).toNat)) (R 11)) (by decide) (by decide)
      (newYoung_fast x R s.acting.leaf regs win) (newNotYoung_fast x R s.acting.leaf regs win)
    refine ⟨y, run, ⟨act, mem.trans s.memory⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · have := bltu_true _ _ g
      rw [startV, r11] at this
      exact Or.inl ⟨this, p.pc, ⟨holds_at p.regs rfl r10, holds_at p.regs rfl r13, holds_at p.regs rfl startV⟩⟩
    · have := bltu_false _ _ g
      rw [startV, r11] at this
      exact Or.inr ⟨this, p.pc⟩
  · -- the page table
    intro x s pc0
    let R := regsAt x
    have r8 : R 8 = v := regsAt_of s.acting.s0
    obtain ⟨l, hl, -⟩ := s.acting.link
    have blk := (newLookup_fast x R s.acting.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of s.acting.s0),
      gpr_some (gpr_some_of s.acting.s1), gpr_some s.acting.a0, trivial⟩).run x ⟨pc0, rfl⟩
    rw [r8] at blk
    exact s.look pt newLookup_call_shape newLookup_call_decode (fun _ h => newLookup_call_pins h)
      newLookup_call_target (by decide) table (by decide) (by decide) blk (by rw [← r8]; rfl)
      (fun y h g ok => by
        rw [show newLookup_call.link = 0x8000cb48#64 by decide]; exact newNotHeap_fast y (regsAt y) h g ok)
      (fun y h g ok => by
        rw [show newLookup_call.link = 0x8000cb48#64 by decide]; exact newHeap_fast y (regsAt y) h g ok)

/-- **`w = *r` classified on the young-`v` path** (from `0x8000cb98`, with
`v`'s young bounds in `a3`/`a5`): a young `w` stores (`0x8000cb80`), an old one
moves `r` to the young list (`0x8000cbb8`), any other inserts it there
(`0x8000cbc8`). -/
theorem yClassify {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (pt : PageTableLookup Table)
    {H0 : List (Nat × Nat)} {m1 : Std.ExtHashMap Nat (BitVec 8)} {sp v r : BitVec 64}
    {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {start stop w : BitVec 64} {c x : Config}
    (table : Table m1 cls) (win : ReadWindow r 8) (hw : bytesVal .ld (read8 m1 r.toNat) = w)
    (s : Settled Shape foot H0 m1 sp v r rs c ys os x) (pc0 : PCAt 0x8000cb98#64 x)
    (regs0 : YoungRegs r start stop x) :
    ∃ y, Steps x y ∧ Settled Shape foot H0 m1 sp v r rs c ys os y ∧
      Lands start stop cls w 0x8000cb80#64 0x8000cbb8#64 0x8000cbc8#64 (fun _ => True) y := by
  refine classifyImm (St := Settled Shape foot H0 m1 sp v r rs c ys os)
    (I := fun y => PCAt 0x8000cb98#64 y ∧ YoungRegs r start stop y)
    (E := fun y => PCAt 0x8000cba4#64 y ∧ gprGet y.σ 10 = some w ∧ gprGet y.σ 13 = some stop ∧
      gprGet y.σ 15 = some start)
    (S := fun y => PCAt 0x8000cba8#64 y ∧ gprGet y.σ 10 = some w ∧ gprGet y.σ 15 = some start)
    (L := fun y => PCAt 0x8000cbac#64 y ∧ gprGet y.σ 10 = some w) ?_ ?_ ?_ ?_ s ⟨pc0, regs0⟩
  · -- the low bit
    intro x s ⟨pc0, regs0⟩
    let R := regsAt x
    have r10 : R 10 = r := regsAt_of regs0.slot
    have r13 : R 13 = stop := regsAt_of regs0.stop
    have r15 : R 15 = start := regsAt_of regs0.start
    have val : bytesVal .ld (read8 x.σ.mem (R 10).toNat) = w := by rw [r10, s.memory, hw]
    have regs : GHolds x.σ (yImm_input R) :=
      ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of regs0.slot),
        gpr_some (gpr_some_of regs0.stop), gpr_some (gpr_some_of regs0.start), trivial⟩
    have w10 : ReadWindow (R 10) 8 := by rw [r10]; exact win
    obtain ⟨y, run, act, mem, out⟩ := s.acting.branch pc0
      (guardB .BNE (bytesVal .ld (read8 x.σ.mem (R 10).toNat) &&& 1#64) 0#64) (by decide) (by decide)
      (yImm_fast x R s.acting.leaf regs w10) (yBlock_fast x R s.acting.leaf regs w10)
    refine ⟨y, run, ⟨act, mem.trans s.memory⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · exact Or.inl ⟨by rw [val] at g; simpa [guardB] using g, p.pc⟩
    · exact Or.inr ⟨by rw [val] at g; simpa [guardB] using g, p.pc, holds_at p.regs rfl val,
        holds_at p.regs rfl r13, holds_at p.regs rfl r15⟩
  · -- `young_end`
    intro x s ⟨pc0, a0, a3, a5⟩
    let R := regsAt x
    have r10 : R 10 = w := regsAt_of a0
    have r13 : R 13 = stop := regsAt_of a3
    have r15 : R 15 = start := regsAt_of a5
    have regs : GHolds x.σ (yAboveEnd_input R) :=
      ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0),
        gpr_some (gpr_some_of a3), gpr_some (gpr_some_of a5), trivial⟩
    obtain ⟨y, run, act, mem, out⟩ := s.acting.branch pc0 (guardB .BGEU (R 10) (R 13)) (by decide) (by decide)
      (yAboveEnd_fast x R s.acting.leaf regs) (yBelowEnd_fast x R s.acting.leaf regs)
    refine ⟨y, run, ⟨act, mem.trans s.memory⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · have := bgeu_true _ _ g
      rw [r13, r10] at this
      exact Or.inl ⟨this, p.pc, holds_at p.regs rfl r10⟩
    · have := bgeu_false _ _ g
      rw [r13, r10] at this
      exact Or.inr ⟨this, p.pc, holds_at p.regs rfl r10, holds_at p.regs rfl r15⟩
  · -- `young_start`
    intro x s ⟨pc0, a0, a5⟩
    let R := regsAt x
    have r10 : R 10 = w := regsAt_of a0
    have r15 : R 15 = start := regsAt_of a5
    have regs : GHolds x.σ (yYoung_input R) :=
      ⟨gpr_some (gpr_some_of s.acting.s0), gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0),
        gpr_some (gpr_some_of a5), trivial⟩
    obtain ⟨y, run, act, mem, out⟩ := s.acting.branch pc0 (guardB .BLTU (R 15) (R 10)) (by decide) (by decide)
      (yYoung_fast x R s.acting.leaf regs) (yNotYoung_fast x R s.acting.leaf regs)
    refine ⟨y, run, ⟨act, mem.trans s.memory⟩, ?_⟩
    rcases out with ⟨g, p⟩ | ⟨g, p⟩
    · have := bltu_true _ _ g
      rw [r15, r10] at this
      exact Or.inl ⟨this, p.pc, trivial⟩
    · have := bltu_false _ _ g
      rw [r15, r10] at this
      exact Or.inr ⟨this, p.pc, holds_at p.regs rfl r10⟩
  · -- the page table
    intro x s ⟨pc0, a0⟩
    let R := regsAt x
    have r10 : R 10 = w := regsAt_of a0
    obtain ⟨l, hl, -⟩ := s.acting.link
    have blk := (yLookup_fast x R s.acting.leaf ⟨gpr_some (gpr_some_of hl), gpr_some (gpr_some_of s.acting.s0),
      gpr_some (gpr_some_of s.acting.s1), gpr_some (gpr_some_of a0), trivial⟩).run x ⟨pc0, rfl⟩
    rw [r10] at blk
    exact s.look pt yLookup_call_shape yLookup_call_decode (fun _ h => yLookup_call_pins h)
      yLookup_call_target (by decide) table (by decide) (by decide) blk (by rw [← r10]; rfl)
      (fun y h g ok => by
        rw [show yLookup_call.link = 0x8000cbb0#64 by decide]; exact yNotHeap_fast y (regsAt y) h g ok)
      (fun y h g ok => by
        rw [show yLookup_call.link = 0x8000cbb0#64 by decide]; exact yHeap_fast y (regsAt y) h g ok)

end OCaml.Vm.Primitives.Named.ModifyRoot
