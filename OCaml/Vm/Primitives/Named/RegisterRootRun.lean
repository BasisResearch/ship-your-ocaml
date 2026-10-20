import OCaml.Vm.Primitives.Named.RegisterRoot
import OCaml.Vm.Primitives.Named.RootsUpdate
import OCaml.Vm.Gc.PageTable
import OCaml.Vm.Gc.LibHeap
import OCaml.Vm.Primitives.GprsPersist
import OCaml.Vm.Primitives.Named.NamedHash
import OCaml.Vm.Sim.CopyStringInput
import OCaml.Vm.Boot.Startup.NativeNested

/-!
# `caml_register_generational_global_root(r)` as a machine run

By the class of `v = *r`: an immediate returns at once; a young block
(strictly between `young_start` and `young_end`) is filed in
`caml_global_roots_young`; otherwise `caml_page_table_lookup(v)` decides
`In_heap`, filed in `caml_global_roots_old`, or nothing. The two filings are
tail calls of `caml_skiplist_insert` (`Skiplist.Ops.insert`); the global
roots after are `GlobalRoots.insert_young`/`insert_old`.
-/

namespace OCaml.Vm.Primitives.Named.RegisterRoot
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm OCaml.Vm.Primitives OCaml.Vm.Gc OCaml.Vm.Gc.Skiplist
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady nativeFrameBase)
open NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif wl_nil)

/-- The root's value. -/
def rootValue (c : Config) (r : BitVec 64) : BitVec 64 := bytesVal .ld (read8 c.σ.mem r.toNat)

/-- A young block: strictly between `young_start` and `young_end`. -/
def Young (start stop v : BitVec 64) : Prop :=
  v &&& 1#64 = 0#64 ∧ v.toNat < stop.toNat ∧ start.toNat < v.toNat

/-- An old block: not young, `In_heap` by the page table. -/
def Old (start stop : BitVec 64) (cls : Nat → Nat) (v : BitVec 64) : Prop :=
  v &&& 1#64 = 0#64 ∧ ¬ (v.toNat < stop.toNat ∧ start.toNat < v.toNat) ∧
    BitVec.ofNat 64 (cls (v.toNat / 4096)) &&& 1#64 ≠ 0#64

/-- `Caml_state` and the young generation's bounds. -/
structure YoungAt (m : Std.ExtHashMap Nat (BitVec 8)) (D start stop : BitVec 64) : Prop where
  state : bytesVal .ld (read8 m (0x80064d08#64).toNat) = D
  startWord : bytesVal .ld (read8 m (D + 32#64).toNat) = start
  stopWord : bytesVal .ld (read8 m (D + 40#64).toNat) = stop
  startWin : ReadWindow (D + 32#64) 8
  stopWin : ReadWindow (D + 40#64) 8

/-- **A call of `caml_register_generational_global_root(r)`**: a fresh root
slot `r`, newlib's heap, a native frame, the global roots, the page table and
the young bounds. -/
structure RootInput (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop)
    (H : List (Nat × Nat)) (cap : Nat) (rs ys os : List (BitVec 64)) (cls : Nat → Nat)
    (D start stop sp ra r : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  slot : gprGet c.σ 10 = some r
  stack : gprGet c.σ 2 = some sp
  window : ReadWindow r 8
  heap : HeapReady H cap c
  frame : NativeFrame sp opStack
  roots : GlobalRoots Shape foot c.σ.mem rs ys os
  fresh : r ∉ rs ++ ys ++ os
  table : Table c.σ.mem cls
  young : YoungAt c.σ.mem D start stop

/-- **The root filed**: back at `ra` with `sp` and the callee-saved registers;
the young list gains `r` when `v` is young, the old list when it is old;
newlib's heap ready; every byte outside the two lists, newlib's footprint, the
stack window and `random_seed` kept. -/
structure RootFiled (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (H : List (Nat × Nat)) (rs ys os : List (BitVec 64)) (cls : Nat → Nat)
    (start stop sp ra r : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : PCAt ra d
  link : gprGet d.σ 1 = some ra
  stack : gprGet d.σ 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput
  htif : d.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes
  heap : ∃ H' cap', HeapReady H' cap' d ∧
    ∀ a, VsaIris.VsaHeap.vsaFoot H' a → VsaIris.VsaHeap.vsaFoot H a ∨ ListsFoot Shape foot c.σ.mem a
  /-- the lists' footprints lie in the old ones and newlib's footprint -/
  feet : ∀ a, ListsFoot Shape foot d.σ.mem a → ListsFoot Shape foot c.σ.mem a ∨ VsaIris.VsaHeap.vsaFoot H a
  roots : ∃ ys' os', GlobalRoots Shape foot d.σ.mem rs ys' os' ∧
    (∀ k, k ∈ ys' ↔ (Young start stop (rootValue c r) ∧ k = r) ∨ k ∈ ys) ∧
    (∀ k, k ∈ os' ↔ (Old start stop cls (rootValue c r) ∧ k = r) ∨ k ∈ os)
  kept : ∀ a, ¬ ListsFoot Shape foot c.σ.mem a → ¬ VsaIris.VsaHeap.vsaFoot H a →
    (a < sp.toNat - opStack ∨ sp.toNat ≤ a) → (a < randomSeed ∨ randomSeed + 4 ≤ a) →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

/-- Newlib's heap is ready at a configuration with the same memory. -/
theorem HeapReady.of_mem {H : List (Nat × Nat)} {cap : Nat} {c d : Config} (h : HeapReady H cap c)
    (same : d.σ.mem = c.σ.mem) : HeapReady H cap d :=
  OCaml.Vm.Gc.HeapReady.keep_windows h (ws := []) (fun _ w => nomatch w) fun a _ => by rw [same]

/-- A root that is neither young nor old leaves both lists. -/
theorem lists_kept {ys : List (BitVec 64)} {P : Prop} {r : BitVec 64} (no : ¬ P) :
    ∀ k, k ∈ ys ↔ (P ∧ k = r) ∨ k ∈ ys :=
  fun k => ⟨Or.inr, fun h => h.elim (fun p => absurd p.1 no) id⟩

/-- **An immediate value**: `*r`'s low bit is set; return at once. -/
theorem imm_path {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
    {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} {H : List (Nat × Nat)} {cap : Nat}
    {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {D start stop sp ra r : BitVec 64} {c : Config}
    (h : RootInput Shape foot Table H cap rs ys os cls D start stop sp ra r c) (pc : PCAt 0x8000ca04#64 c)
    (imm : rootValue c r &&& 1#64 ≠ 0#64) :
    ∃ d, Steps c d ∧ RootFiled Shape foot H rs ys os cls start stop sp ra r c d := by
  let R := regsAt c
  have r10 : R 10 = r := regsAt_of h.slot
  have r1 : R 1 = ra := regsAt_of h.leaf.raReg
  have leaf0 : LeafInput (R 1) c := by rw [r1]; exact h.leaf
  have value : bytesVal .ld ((imm_loads c.σ.mem R).getD 0 []) = rootValue c r := by
    simp only [imm_loads, List.getD_cons_zero, r10, rootValue]
  obtain ⟨c1, run1, p1⟩ := (imm_fast c R leaf0 ⟨gpr_some (gpr_some_of h.slot), trivial⟩ (by rw [r10]; exact h.window)
    (by rw [value]; simpa [guardB] using imm)).run c ⟨pc, rfl⟩
  let R1 := regsAt c1
  have c1_1 : gprGet c1.σ 1 = some ra :=
    (p1.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans h.leaf.raReg
  have c1_10 : gprGet c1.σ 10 = some (rootValue c r) := by rw [← value]; exact gholds_lookup _ p1.regs rfl
  have leaf1 : LeafInput (R1 1) c1 := by
    rw [show R1 1 = ra from regsAt_of c1_1]; exact ⟨p1.good, p1.image, p1.minstret, c1_1, h.leaf.aligned, p1.tick⟩
  obtain ⟨d, run2, p2⟩ := (immRet_fast c1 R1 leaf1 ⟨gpr_some (gpr_some_of c1_1), gpr_some (gpr_some_of c1_10), trivial⟩).run
    c1 ⟨p1.pc, rfl⟩
  have mem : d.σ.mem = c.σ.mem := by rw [p2.memory, wl_nil, p1.memory, wl_nil]
  have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 15]) : gprGet d.σ n = gprGet c.σ n :=
    (p2.gpr_frame (by decide) n lo hi (by simp)).trans (p1.gpr_frame (by decide) n lo hi out)
  have notYoung : ¬ Young start stop (rootValue c r) := fun y => imm y.1
  have notOld : ¬ Old start stop cls (rootValue c r) := fun o => imm o.1
  refine ⟨d, run1.trans run2,
    { good := p2.good
      image := p2.image
      minstret := p2.minstret
      tick := p2.tick
      pc := ?_
      link := (keep 1 (by decide) (by decide) (by decide)).trans h.leaf.raReg
      stack := (keep 2 (by decide) (by decide) (by decide)).trans h.stack
      saved := ?_
      gprs := GprsKept.of_steps gprsPersist (run1.trans run2) (keep 3 (by decide) (by decide) (by decide))
      output := p2.output.trans p1.output
      htif := (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
      heap := ⟨H, cap, HeapReady.of_mem h.heap mem, fun _ f => Or.inl f⟩
      feet := fun a l => Or.inl (by rw [mem] at l; exact l)
      roots := ⟨ys, os, by rw [mem]; exact h.roots, lists_kept notYoung, lists_kept notOld⟩
      kept := fun a _ _ _ _ => by rw [mem] }⟩
  · have := p2.pc; rwa [show R1 1 = ra from regsAt_of c1_1] at this
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    exact keep n (by omega) (by omega) (by simp; omega)

/-- **After an insertion's return**, from a pre-insertion state `e` that
agrees with the entry below the arena and outside the stack window. -/
theorem filed_of_returned {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
    {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (ops : Ops Shape foot) {H : List (Nat × Nat)}
    {cap : Nat} {rs ys os : List (BitVec 64)} {cls : Nat → Nat} {D start stop sp ra r : BitVec 64}
    {c e d : Config} {hdr : Nat} {cells : List (BitVec 64)}
    (h : RootInput Shape foot Table H cap rs ys os cls D start stop sp ra r c) (run : Steps c d)
    (list : hdr = globalRootsYoung ∨ hdr = globalRootsOld) (sh : Shape c.σ.mem hdr cells)
    (low : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (e.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (outside : ∀ a, (a < sp.toNat - opStack ∨ sp.toNat ≤ a) → (e.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (savedE : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet e.σ n = gprGet c.σ n)
    (gpE : gpr e 3 = gpr c 3) (outE : e.σ.sailOutput = c.σ.sailOutput)
    (htifE : e.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes)
    (ret : Returned H (foot e.σ.mem hdr cells) sp ra e d)
    (feet : ∀ a, ListsFoot Shape foot d.σ.mem a → ListsFoot Shape foot e.σ.mem a ∨ VsaIris.VsaHeap.vsaFoot H a)
    (roots : ∃ ys' os', GlobalRoots Shape foot d.σ.mem rs ys' os' ∧
      (∀ k, k ∈ ys' ↔ (Young start stop (rootValue c r) ∧ k = r) ∨ k ∈ ys) ∧
      (∀ k, k ∈ os' ↔ (Old start stop cls (rootValue c r) ∧ k = r) ∨ k ∈ os)) :
    RootFiled Shape foot H rs ys os cls start stop sp ra r c d := by
  obtain ⟨she, ft, -⟩ := ops.keep_list sh fun a f => low a (ops.low _ _ _ sh a f)
  have lists : ∀ a, ListsFoot Shape foot e.σ.mem a ↔ ListsFoot Shape foot c.σ.mem a :=
    h.roots.listsFoot_keep ops fun a ⟨_, _, _, sh', f⟩ => low a (ops.low _ _ _ sh' a f)
  obtain ⟨H', cap', hr, hb⟩ := ret.heap
  exact
    { good := ret.good
      image := ret.image
      minstret := ret.minstret
      tick := ret.tick
      pc := ret.pc
      link := ret.link
      stack := ret.stack
      saved := fun n hn => (ret.saved n hn).trans (savedE n hn)
      gprs := GprsKept.of_steps gprsPersist run (ret.gprs.gp.trans gpE)
      output := ret.output.trans outE
      htif := ret.htif.trans htifE
      heap := ⟨H', cap', hr, fun a f => (hb a f).imp id fun t => (lists a).1 ⟨hdr, cells, Or.inr list, she, t⟩⟩
      feet := fun a l => (feet a l).imp (lists a).1 id
      roots := roots
      kept := fun a nl nf win seed => by
        rw [ret.kept a (fun f => nl ⟨hdr, cells, Or.inr list, sh, (ft a).1 f⟩) nf win seed]
        exact outside a win }

/-- At the page-table lookup (`0x8000ca2c`): `v` in `a0`, `r` in `a1`, the
entry's memory and callee-saved registers. -/
structure AtLookup (c e : Config) (sp ra r : BitVec 64) : Prop where
  leaf : LeafInput ra e
  pc : PCAt 0x8000ca2c#64 e
  stack : gprGet e.σ 2 = some sp
  value : gprGet e.σ 10 = some (rootValue c r)
  slot : gprGet e.σ 11 = some r
  memory : e.σ.mem = c.σ.mem
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet e.σ n = gprGet c.σ n
  gp : gpr e 3 = gpr c 3
  output : e.σ.sailOutput = c.σ.sailOutput
  htif : e.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes

theorem frame32 {sp : BitVec 64} (frame : NativeFrame sp opStack) {k : Nat} (hk : k ≤ 32) :
    sp - 32#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (sp.toNat - 32 + k) ∧
      sp + 18446744073709551584#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (sp.toNat - 32 + k) := by
  have lower := frame.lower
  have upper := frame.upper
  have hE : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have hT : Layout.sym_stack_top = 0x88000000 := rfl
  have l : 32 ≤ sp.toNat := by unfold opStack at lower; omega
  have u : sp.toNat < 2 ^ 32 := by omega
  have k64 : k < 2 ^ 64 := by omega
  constructor <;> bv_omega

/-- **The page-table path**: `caml_page_table_lookup(v)` with `ra` and `r`
saved in a 32-byte frame; `In_heap` files `r` in the old list, otherwise
return. -/
theorem lookup_path {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
    {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (ops : Ops Shape foot)
    (pt : PageTableLookup Table) {H : List (Nat × Nat)} {cap : Nat} {rs ys os : List (BitVec 64)}
    {cls : Nat → Nat} {D start stop sp ra r : BitVec 64} {c e : Config}
    (h : RootInput Shape foot Table H cap rs ys os cls D start stop sp ra r c) (run : Steps c e)
    (at0 : AtLookup c e sp ra r) (blk : rootValue c r &&& 1#64 = 0#64)
    (notYoung : ¬ ((rootValue c r).toNat < stop.toNat ∧ start.toNat < (rootValue c r).toNat)) :
    ∃ d, Steps c d ∧ RootFiled Shape foot H rs ys os cls start stop sp ra r c d := by
  have frame := h.frame
  have lower : Vsa.Sim.DlHeap.heapEnd + 768 ≤ sp.toNat := frame.lower
  have hE : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have l32 : 32 ≤ sp.toNat := by omega
  let v := rootValue c r
  -- the frame's saves
  let L := regsAt e
  have l1 : L 1 = ra := regsAt_of at0.leaf.raReg
  have l2 : L 2 = sp := regsAt_of at0.stack
  have l10 : L 10 = v := regsAt_of at0.value
  have l11 : L 11 = r := regsAt_of at0.slot
  have small := frame.resize (small := 32) (by unfold opStack; decide) (by decide)
  have slotW (k : Nat) (hk : k + 8 ≤ 32) (al : k % 8 = 0) : WriteWindow (L 2 - 32#64 + BitVec.ofNat 64 k) 8 := by
    rw [l2, (frame32 frame (k := k) (by omega)).1]
    have w := small.word (off := k) hk al
    rwa [show nativeFrameBase sp 32 + k = sp.toNat - 32 + k by unfold nativeFrameBase; rfl] at w
  have saveNat (k : Nat) (hk : k ≤ 32) : (L 2 - 32#64 + BitVec.ofNat 64 k).toNat = sp.toNat - 32 + k := by
    rw [l2, (frame32 frame (k := k) hk).1, BitVec.toNat_ofNat]; omega
  have log0 : LogInW [⟨sp.toNat - 32, sp.toNat⟩] (lookupLog L (lookup_loads e.σ.mem L)) := by
    have e8 := saveNat 8 (by decide)
    have e24 := saveNat 24 (by decide)
    simp only [lookupLog, LogInW, InsideW, e8, e24, and_true]; omega
  obtain ⟨e1, run1, p1⟩ := (lookup_fast e L (by rw [l1]; exact at0.leaf)
    ⟨gpr_some (gpr_some_of at0.leaf.raReg), gpr_some (gpr_some_of at0.stack), gpr_some (gpr_some_of at0.value),
      gpr_some (gpr_some_of at0.slot), trivial⟩
    (slotW 24 (by decide) (by decide)) (slotW 8 (by decide) (by decide))
    (OCaml.Vm.Sim.imageOutside_of_above fun x hx => by
      have := OCaml.Vm.Sim.logInW_mem log0 hx
      simp only [InsideW] at this
      simp only [Layout.sym_bss_end]
      rcases this with ⟨lo, -⟩ | f
      · omega
      · exact f.elim)).run e ⟨at0.pc, rfl⟩
  -- the call
  have e1_10 : gprGet e1.σ 10 = some v := by rw [← l10]; exact gholds_lookup _ p1.regs rfl
  have e1_2 : gprGet e1.σ 2 = some (L 2 + 18446744073709551584#64) := gholds_lookup _ p1.regs rfl
  let args : GRegs := [(10, v), (2, L 2 + 18446744073709551584#64)]
  obtain ⟨e2, run2, p2⟩ := (call_registers_summary lookup_call_shape lookup_call_decode e1 (lookup_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret args ⟨e1_10, e1_2, trivial⟩ (by change KeysOK [10, 2]; decide)
    (by simp [KeysAvoidRa, args, keysG]) rfl).run e1 ⟨p1.pc, rfl⟩
  -- the memory from here on: the two saves on the entry's
  have frameMem : ∀ a, (a < sp.toNat - 32 ∨ sp.toNat ≤ a) →
      ((writeLog e.σ.mem (lookupLog L (lookup_loads e.σ.mem L)))[a]?) = c.σ.mem[a]? := fun a out => by
    rw [frameOn_writeLog _ _ _ log0 a ⟨out, trivial⟩, at0.memory]
  have mem2 : e2.σ.mem = writeLog e.σ.mem (lookupLog L (lookup_loads e.σ.mem L)) := by rw [p2.memory, p1.memory]
  have table2 : Table e2.σ.mem cls := pt.frame _ _ cls h.table fun a ha => by
    rw [mem2, frameMem a (Or.inl (by omega))]
  have pc2 : PCAt pageTableLookupPc e2 := by have := p2.pc; rwa [lookup_call_target] at this
  have link2 : gprGet e2.σ 1 = some lookup_call.link := gholds_lookup _ p2.regs rfl
  obtain ⟨e3, run3, p3⟩ := (pt.call e2 lookup_call.link v cls table2
    ⟨p2.good, p2.image, p2.minstret, link2, by decide, p2.tick⟩ (gholds_lookup _ p2.regs rfl)).run e2 ⟨pc2, rfl⟩
  let I := regsAt e3
  have i10 : I 10 = BitVec.ofNat 64 (cls (v.toNat / 4096)) := regsAt_of p3.result
  have e3_1 : gprGet e3.σ 1 = some lookup_call.link := (p3.saved 1 (by decide)).trans link2
  have e3_2 : gprGet e3.σ 2 = some (L 2 + 18446744073709551584#64) :=
    (p3.saved 2 (by decide)).trans (gholds_lookup _ p2.regs rfl)
  have leaf3 : LeafInput (I 1) e3 := by
    rw [show I 1 = lookup_call.link from regsAt_of e3_1]
    exact ⟨p3.good, p3.image, p3.minstret, e3_1, by decide, p3.tick⟩
  have pc3 : PCAt 0x8000ca3c#64 e3 := by have := p3.pc; rwa [show lookup_call.link = 0x8000ca3c#64 by decide] at this
  have mem3 : e3.σ.mem = writeLog e.σ.mem (lookupLog L (lookup_loads e.σ.mem L)) := by rw [p3.memory, mem2]
  -- the frame's two words
  have sp' (k : Nat) (hk : k ≤ 32) :
      L 2 + 18446744073709551584#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (sp.toNat - 32 + k) := by
    rw [l2]; exact (frame32 frame hk).2
  have savedWords : bytesT (writeLog e.σ.mem (lookupLog L (lookup_loads e.σ.mem L))) (sp.toNat - 32 + 24) 8 = ra ∧
      bytesT (writeLog e.σ.mem (lookupLog L (lookup_loads e.σ.mem L))) (sp.toNat - 32 + 8) 8 = r := by
    have e8 := saveNat 8 (by decide)
    have e24 := saveNat 24 (by decide)
    constructor
    · rw [← l1, ← e24]
      exact Gc.word_writeLog_at _ _ 0 _ _ (by simp [lookupLog]) (by
        simp only [lookupLog, List.drop, OutLRange, e8, e24, and_true]; omega)
    · rw [← l11, ← e8]
      exact Gc.word_writeLog_at _ _ 1 _ _ (by simp [lookupLog]) (by simp [lookupLog, OutLRange])
  have readW (k : Nat) (hk : k + 8 ≤ 32) (al : k % 8 = 0) :
      ReadWindow (L 2 + 18446744073709551584#64 + BitVec.ofNat 64 k) 8 := by
    rw [sp' k (by omega)]
    have w := small.word (off := k) hk al
    rw [show nativeFrameBase sp 32 + k = sp.toNat - 32 + k by unfold nativeFrameBase; rfl] at w
    exact w.read
  have readV (k : Nat) (hk : k ≤ 32) (x : Config) (hx : x.σ.mem = e3.σ.mem) :
      bytesVal .ld (read8 x.σ.mem (L 2 + 18446744073709551584#64 + BitVec.ofNat 64 k).toNat) =
        bytesT (writeLog e.σ.mem (lookupLog L (lookup_loads e.σ.mem L))) (sp.toNat - 32 + k) 8 := by
    rw [read8_value, sp' k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx, mem3]
  have notYoung' : ¬ Young start stop v := fun y => notYoung y.2
  -- the entry's callee-saved registers, gp and output at the lookup's return
  have savedTo3 : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet e3.σ n = gprGet c.σ n := by
    intro n hn
    have hs : n ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega
    have hr : 1 ≤ n ∧ n ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
    rw [p3.saved n hs]
    change gpr e2 n = gprGet c.σ n
    rw [p2.toEffectPost.gpr_frame (by decide) n hr.1 hr.2 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega),
      p1.toEffectPost.gpr_frame (by decide) n hr.1 hr.2 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)]
    exact at0.saved n hn
  have gp3 : gpr e3 3 = gpr c 3 := by
    change gprGet e3.σ 3 = gprGet c.σ 3
    rw [p3.saved 3 (by decide)]
    change gpr e2 3 = gpr c 3
    rw [p2.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide),
      p1.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)]
    exact at0.gp
  have out3 : e3.σ.sailOutput = c.σ.sailOutput := by rw [p3.output, p2.output, p1.output, at0.output]
  have htif3 : e3.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes :=
    p3.htif.trans ((p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans ((p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans at0.htif))
  have low3 : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (e3.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := fun a ha => by
    rw [mem3, frameMem a (Or.inl (by omega))]
  have outside3 : ∀ a, (a < sp.toNat - opStack ∨ sp.toNat ≤ a) → (e3.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 :=
    fun a win => by
      rw [mem3, frameMem a (by unfold opStack at win; omega)]
  have heapAt (x : Config) (hx : ∀ a, (a < sp.toNat - 32 ∨ sp.toNat ≤ a) →
      (x.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) : HeapReady H cap x :=
    OCaml.Vm.Gc.HeapReady.keep_windows h.heap (ws := [⟨sp.toNat - 32, sp.toNat⟩])
      (fun w hw => by
        simp only [List.mem_singleton] at hw
        subst hw
        exact Or.inr (Or.inl (Nat.le_sub_of_add_le
          (Nat.le_trans (Nat.add_le_add_left (by decide : 32 ≤ 768) _) lower))))
      (fun a out => hx a (out _ List.mem_cons_self))
  have e4' (x : Config) (keep2 : gprGet x.σ 2 = gprGet e3.σ 2) (keep1 : gprGet x.σ 1 = gprGet e3.σ 1) :
      gprGet x.σ 2 = some (L 2 + 18446744073709551584#64) ∧ gprGet x.σ 1 = some lookup_call.link :=
    ⟨keep2.trans e3_2, keep1.trans e3_1⟩
  by_cases bit : BitVec.ofNat 64 (cls (v.toNat / 4096)) &&& 1#64 = 0#64
  · -- unfiled: return
    obtain ⟨e4, run4, p4⟩ := (notHeap_fast e3 I leaf3 ⟨gpr_some (gpr_some_of p3.result), trivial⟩
      (by rw [i10]; simp [guardB, bit])).run e3 ⟨pc3, rfl⟩
    obtain ⟨e4_2, e4_1⟩ := e4' e4 (p4.gpr_frame (by decide) 2 (by decide) (by decide) (by decide))
      (p4.gpr_frame (by decide) 1 (by decide) (by decide) (by decide))
    let J := regsAt e4
    have j2 : J 2 = L 2 + 18446744073709551584#64 := regsAt_of e4_2
    have mem4 : e4.σ.mem = e3.σ.mem := by rw [p4.memory, wl_nil]
    have leaf4 : LeafInput (J 1) e4 := by
      rw [show J 1 = lookup_call.link from regsAt_of e4_1]
      exact ⟨p4.good, p4.image, p4.minstret, e4_1, by decide, p4.tick⟩
    have savedRa : bytesVal .ld (read8 e4.σ.mem (J 2 + 24#64).toNat) = ra := by
      rw [j2]; exact (readV 24 (by decide) e4 mem4).trans savedWords.1
    obtain ⟨d, run5, p5⟩ := (heapless_fast e4 ra J leaf4
      ⟨gpr_some (gpr_some_of e4_2), gpr_some (gpr_some_of (gholds_lookup _ p4.regs rfl)), trivial⟩
      (by rw [j2]; exact readW 24 (by decide) (by decide)) savedRa h.leaf.aligned).run e4 ⟨p4.pc, rfl⟩
    have mem5 : d.σ.mem = e3.σ.mem := by rw [p5.memory, wl_nil, mem4]
    have holds_ra : gprGet d.σ 1 = some ra := (gholds_lookup (n := 1) _ p5.regs rfl).trans (congrArg some savedRa)
    have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 10]) : gprGet d.σ n = gprGet e3.σ n :=
      (p5.gpr_frame (by decide) n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega)).trans
        (p4.gpr_frame (by decide) n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega))
    have notOld : ¬ Old start stop cls v := fun o => o.2.2 bit
    refine ⟨d, run.trans (run1.trans (run2.trans (run3.trans (run4.trans run5)))),
      { good := p5.good
        image := p5.image
        minstret := p5.minstret
        tick := p5.tick
        pc := p5.pc
        link := holds_ra
        stack := ?_
        saved := fun n hn => by
          have hr : 1 ≤ n ∧ n ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
          rw [keep n hr.1 hr.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)]
          exact savedTo3 n hn
        gprs := GprsKept.of_steps gprsPersist (run.trans (run1.trans (run2.trans (run3.trans (run4.trans run5)))))
          ((keep 3 (by decide) (by decide) (by decide)).trans gp3)
        output := p5.output.trans (p4.output.trans out3)
        htif := (p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans ((p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans htif3)
        heap := ⟨H, cap, heapAt d fun a out => by rw [mem5, mem3, frameMem a out], fun _ f => Or.inl f⟩
        feet := fun a l => Or.inl (((h.roots.listsFoot_keep (m' := d.σ.mem) ops (fun a' l' => by
          obtain ⟨_, _, _, sh', f⟩ := l'
          rw [mem5]; exact low3 a' (ops.low _ _ _ sh' a' f))) a).1 l)
        roots := ⟨ys, os, (GlobalRoots.keep_low ops h.roots fun a ha => by rw [mem5]; exact low3 a ha).1,
          lists_kept notYoung', lists_kept notOld⟩
        kept := fun a _ _ win _ => by rw [mem5]; exact outside3 a win }⟩
    have st := gholds_lookup (n := 2) _ p5.regs rfl
    rw [st, j2, BitVec.add_assoc, show (18446744073709551584#64 : BitVec 64) + 32#64 = 0#64 by decide,
      BitVec.add_zero, l2]
  · -- `In_heap`: the old list
    obtain ⟨e4, run4, p4⟩ := (inHeap_fast e3 I leaf3 ⟨gpr_some (gpr_some_of p3.result), trivial⟩
      (by rw [i10]; simp [guardB, bit])).run e3 ⟨pc3, rfl⟩
    obtain ⟨e4_2, e4_1⟩ := e4' e4 (p4.gpr_frame (by decide) 2 (by decide) (by decide) (by decide))
      (p4.gpr_frame (by decide) 1 (by decide) (by decide) (by decide))
    let O := regsAt e4
    have o2 : O 2 = L 2 + 18446744073709551584#64 := regsAt_of e4_2
    have mem4 : e4.σ.mem = e3.σ.mem := by rw [p4.memory, wl_nil]
    have leaf4 : LeafInput (O 1) e4 := by
      rw [show O 1 = lookup_call.link from regsAt_of e4_1]
      exact ⟨p4.good, p4.image, p4.minstret, e4_1, by decide, p4.tick⟩
    obtain ⟨e5, run5, p5⟩ := (old_fast e4 O leaf4 ⟨gpr_some (gpr_some_of e4_2), trivial⟩
      (by rw [o2]; exact readW 8 (by decide) (by decide)) (by rw [o2]; exact readW 24 (by decide) (by decide))).run
      e4 ⟨p4.pc, rfl⟩
    have r5 (n : Nat) (x : BitVec 64) (hl : lookupG n (old_regs O (old_loads e4.σ.mem O)) = some x) :
        gprGet e5.σ n = some x := gholds_lookup _ p5.regs hl
    have e5_2 : gprGet e5.σ 2 = some sp := by
      rw [r5 2 _ rfl, o2, BitVec.add_assoc, show (18446744073709551584#64 : BitVec 64) + 32#64 = 0#64 by decide,
        BitVec.add_zero, l2]
    have e5_1 : gprGet e5.σ 1 = some ra := by
      rw [r5 1 _ rfl]
      simp only [old_loads, List.getD_cons_succ, List.getD_cons_zero]
      rw [o2]; exact congrArg some ((readV 24 (by decide) e4 mem4).trans savedWords.1)
    have e5_11 : gprGet e5.σ 11 = some r := by
      rw [r5 11 _ rfl]
      simp only [old_loads, List.getD_cons_zero]
      rw [o2]; exact congrArg some ((readV 8 (by decide) e4 mem4).trans savedWords.2)
    have e5_10 : gprGet e5.σ 10 = some (BitVec.ofNat 64 globalRootsOld) := by rw [r5 10 _ rfl]; rfl
    have e5_12 : gprGet e5.σ 12 = some 0#64 := r5 12 _ rfl
    have mem5 : e5.σ.mem = e3.σ.mem := by rw [p5.memory, wl_nil, mem4]
    have low5 : ∀ a, a < Vsa.Sim.DlHeap.heapEnd → (e5.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 :=
      fun a ha => by rw [mem5]; exact low3 a ha
    have outside5 : ∀ a, (a < sp.toNat - opStack ∨ sp.toNat ≤ a) → (e5.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 :=
      fun a win => by rw [mem5]; exact outside3 a win
    obtain ⟨g5, keep5⟩ := GlobalRoots.keep_low ops h.roots low5
    obtain ⟨co, shc, hc⟩ := h.roots.old
    obtain ⟨sh5, -, ks5⟩ := keep5 _ _ shc
    have heap5 : HeapReady H cap e5 := heapAt e5 fun a out => by rw [mem5, mem3, frameMem a out]
    have pc5 : PCAt insertPc e5 := p5.pc
    obtain ⟨d, run6, ret, co', sho', kin, kold, kout, footIn⟩ := (ops.insert H cap globalRootsOld co r sp ra e5 sh5
      ⟨⟨p5.good, p5.image, p5.minstret, e5_1, h.leaf.aligned, p5.tick⟩, heap5, ⟨e5_2, e5_10, e5_11, e5_12, trivial⟩,
        frame⟩).run e5 ⟨pc5, rfl⟩
    have fr : InsertFrame Shape foot H globalRootsOld co e5.σ.mem d.σ.mem :=
      { live := fun sk cells sh a f => (ops.live _ _ _ sh H cap e5 rfl heap5 a f).1
        seed := fun sk cells sh a f => (ops.live _ _ _ sh H cap e5 rfl heap5 a f).2
        kept := fun a nt nf lo seed => ret.kept a nt nf (Or.inl (by unfold opStack; omega)) seed }
    obtain ⟨g', memOld⟩ := GlobalRoots.insert_old ops g5 ⟨fun x => h.fresh (by simp [x]), fun x => h.fresh (by simp [x])⟩ sh5 (by rw [ks5, hc]) sho' kin kold kout footIn fr
    have isOld : Old start stop cls v := ⟨blk, notYoung, bit⟩
    have keep (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 10, 11, 12]) : gprGet e5.σ n = gprGet e3.σ n :=
      (p5.gpr_frame (by decide) n lo hi out).trans
        (p4.gpr_frame (by decide) n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega))
    refine ⟨d, run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))),
      filed_of_returned ops h (run.trans (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))))
        (Or.inr rfl) shc low5 outside5 ?_ ((keep 3 (by decide) (by decide) (by decide)).trans gp3)
        (p5.output.trans (p4.output.trans out3)) ((p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans ((p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans htif3)) ret
        (g5.feet_old ops sh5 sho' footIn fr)
        ⟨ys, keys d.σ.mem co', g', lists_kept notYoung', fun k => (memOld k).trans
          ⟨fun h => h.elim (fun e => Or.inl ⟨isOld, e⟩) Or.inr, fun h => h.elim (fun p => Or.inl p.2) Or.inr⟩⟩⟩
    intro n hn
    have hr : 1 ≤ n ∧ n ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
    rw [keep n hr.1 hr.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)]
    exact savedTo3 n hn

/-- **`caml_register_generational_global_root(r)`**: an immediate `*r`
returns at once; a young block is filed in `caml_global_roots_young`; any
other block goes to the page table (`lookup_path`). -/
theorem register_root_run {Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop}
    {foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop}
    {Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop} (ops : Ops Shape foot)
    (pt : PageTableLookup Table) {H : List (Nat × Nat)} {cap : Nat} {rs ys os : List (BitVec 64)}
    {cls : Nat → Nat} {D start stop sp ra r : BitVec 64} {c : Config}
    (h : RootInput Shape foot Table H cap rs ys os cls D start stop sp ra r c) :
    FnSummary 0x8000ca04#64 (fun x => x = c) (RootFiled Shape foot H rs ys os cls start stop sp ra r c) := by
  constructor
  intro x ⟨pc, eq⟩
  subst eq
  by_cases imm : rootValue x r &&& 1#64 ≠ 0#64
  · exact imm_path h pc imm
  have blk : rootValue x r &&& 1#64 = 0#64 := Classical.not_not.mp imm
  have frame := h.frame
  have lower : Vsa.Sim.DlHeap.heapEnd + 768 ≤ sp.toNat := frame.lower
  let R := regsAt x
  have r10 : R 10 = r := regsAt_of h.slot
  have value : bytesVal .ld ((isBlock_loads x.σ.mem R).getD 0 []) = (rootValue x r) := by
    simp only [isBlock_loads, List.getD_cons_zero, r10]; rfl
  obtain ⟨c1, run1, p1⟩ := (isBlock_fast x R (by rw [show R 1 = ra from regsAt_of h.leaf.raReg]; exact h.leaf)
    ⟨gpr_some (gpr_some_of h.slot), trivial⟩ (by rw [r10]; exact h.window) (by rw [value]; simp [guardB, blk])).run
    x ⟨pc, rfl⟩
  have mem1 : c1.σ.mem = x.σ.mem := by rw [p1.memory, wl_nil]
  have c1_10 : gprGet c1.σ 10 = some (rootValue x r) := by rw [← value]; exact gholds_lookup _ p1.regs rfl
  have c1_11 : gprGet c1.σ 11 = some r := by rw [← r10]; exact gholds_lookup _ p1.regs rfl
  have c1_1 : gprGet c1.σ 1 = some ra :=
    (p1.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans h.leaf.raReg
  have leafAt (y : Config) (good : GoodState y.σ) (image : ExecutableImage y)
      (minstret : ∃ w, y.σ.regs.get? Register.minstret = some w) (tick : y.tick < 2) (ra1 : gprGet y.σ 1 = some ra) :
      LeafInput (regsAt y 1) y := by
    rw [show regsAt y 1 = ra from regsAt_of ra1]; exact ⟨good, image, minstret, ra1, h.leaf.aligned, tick⟩
  let R1 := regsAt c1
  obtain ⟨c2, run2, p2⟩ := (state_fast c1 R1 (leafAt c1 p1.good p1.image p1.minstret p1.tick c1_1)
    ⟨gpr_some (gpr_some_of c1_10), gpr_some (gpr_some_of c1_11), trivial⟩).run c1 ⟨p1.pc, rfl⟩
  have mem2 : c2.σ.mem = x.σ.mem := by rw [p2.memory, wl_nil, mem1]
  have stateD : bytesVal .ld ((state_loads c1.σ.mem R1).getD 0 []) = D := by
    simp only [state_loads, List.getD_cons_zero]; rw [mem1]; exact h.young.state
  have c2_15 : gprGet c2.σ 15 = some D := by rw [← stateD]; exact gholds_lookup _ p2.regs rfl
  have c2_10 : gprGet c2.σ 10 = some (rootValue x r) := by rw [← regsAt_of c1_10]; exact gholds_lookup _ p2.regs rfl
  have c2_11 : gprGet c2.σ 11 = some r := by rw [← regsAt_of c1_11]; exact gholds_lookup _ p2.regs rfl
  have c2_1 : gprGet c2.σ 1 = some ra := (p2.gpr_frame (by decide) 1 (by decide) (by decide) (by decide)).trans c1_1
  let R2 := regsAt c2
  have r2_15 : R2 15 = D := regsAt_of c2_15
  have r2_10 : R2 10 = (rootValue x r) := regsAt_of c2_10
  have stopV : bytesVal .ld ((belowEnd_loads c2.σ.mem R2).getD 0 []) = stop := by
    simp only [belowEnd_loads, List.getD_cons_zero, r2_15]; rw [mem2]; exact h.young.stopWord
  have regs2 : GHolds c2.σ (belowEnd_input R2) :=
    ⟨gpr_some (gpr_some_of c2_10), gpr_some (gpr_some_of c2_11), gpr_some (gpr_some_of c2_15), trivial⟩
  -- the entry's facts at a state the first blocks reached
  have kept2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 15]) : gprGet c2.σ n = gprGet x.σ n :=
    (p2.gpr_frame (by decide) n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega)).trans
      (p1.gpr_frame (by decide) n lo hi out)
  have atLookup (y : Config) (run : Steps x y) (good : GoodState y.σ) (image : ExecutableImage y)
      (minstret : ∃ w, y.σ.regs.get? Register.minstret = some w) (tick : y.tick < 2) (ypc : PCAt 0x8000ca2c#64 y)
      (mem : y.σ.mem = x.σ.mem) (out : y.σ.sailOutput = c2.σ.sailOutput)
      (hy : y.σ.regs.get? Register.htif_payload_writes = c2.σ.regs.get? Register.htif_payload_writes)
      (keep : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [14, 15] → gprGet y.σ n = gprGet c2.σ n) : AtLookup x y sp ra r :=
    { leaf := ⟨good, image, minstret, (keep 1 (by decide) (by decide) (by decide)).trans c2_1, h.leaf.aligned, tick⟩
      pc := ypc
      stack := (keep 2 (by decide) (by decide) (by decide)).trans
        ((kept2 2 (by decide) (by decide) (by decide)).trans h.stack)
      value := (keep 10 (by decide) (by decide) (by decide)).trans c2_10
      slot := (keep 11 (by decide) (by decide) (by decide)).trans c2_11
      memory := mem
      saved := fun n hn => by
        have hr : 1 ≤ n ∧ n ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
        rw [keep n hr.1 hr.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)]
        exact kept2 n hr.1 hr.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)
      gp := (keep 3 (by decide) (by decide) (by decide)).trans (kept2 3 (by decide) (by decide) (by decide))
      output := out.trans (p2.output.trans p1.output)
      htif := hy.trans ((p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))) }
  cases hEnd : guardB .BGEU (R2 10) ((belowEnd_loads c2.σ.mem R2).getD 0 [] |> bytesVal .ld)
  · -- below `young_end`
    obtain ⟨c3, run3, p3⟩ := (belowEnd_fast c2 R2 (leafAt c2 p2.good p2.image p2.minstret p2.tick c2_1) regs2
      (by rw [r2_15]; exact h.young.stopWin) hEnd).run c2 ⟨p2.pc, rfl⟩
    have below : (rootValue x r).toNat < stop.toNat := by
      have := bgeu_false _ _ hEnd; rwa [r2_10, stopV] at this
    have mem3 : c3.σ.mem = x.σ.mem := by rw [p3.memory, wl_nil, mem2]
    have keep3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [14]) : gprGet c3.σ n = gprGet c2.σ n :=
      p3.gpr_frame (by decide) n lo hi out
    let R3 := regsAt c3
    have r3_15 : R3 15 = D := regsAt_of ((keep3 15 (by decide) (by decide) (by decide)).trans c2_15)
    have r3_10 : R3 10 = (rootValue x r) := regsAt_of ((keep3 10 (by decide) (by decide) (by decide)).trans c2_10)
    have startV : bytesVal .ld ((young_loads c3.σ.mem R3).getD 0 []) = start := by
      simp only [young_loads, List.getD_cons_zero, r3_15]; rw [mem3]; exact h.young.startWord
    have c3_1 := (keep3 1 (by decide) (by decide) (by decide)).trans c2_1
    have regs3 : GHolds c3.σ (young_input R3) :=
      ⟨gpr_some (gpr_some_of ((keep3 10 (by decide) (by decide) (by decide)).trans c2_10)),
        gpr_some (gpr_some_of ((keep3 11 (by decide) (by decide) (by decide)).trans c2_11)),
        gpr_some (gpr_some_of ((keep3 15 (by decide) (by decide) (by decide)).trans c2_15)), trivial⟩
    cases hStart : guardB .BLTU ((young_loads c3.σ.mem R3).getD 0 [] |> bytesVal .ld) (R3 10)
    · -- not above `young_start`: the page table
      obtain ⟨c4, run4, p4⟩ := (notYoung_fast c3 R3 (leafAt c3 p3.good p3.image p3.minstret p3.tick c3_1) regs3
        (by rw [r3_15]; exact h.young.startWin) hStart).run c3 ⟨p3.pc, rfl⟩
      have notAbove : (rootValue x r).toNat ≤ start.toNat := by
        have := bltu_false _ _ hStart; rwa [r3_10, startV] at this
      exact lookup_path ops pt h (run1.trans (run2.trans (run3.trans run4)))
        (atLookup c4 (run1.trans (run2.trans (run3.trans run4))) p4.good p4.image p4.minstret p4.tick p4.pc
          (by rw [p4.memory, wl_nil, mem3]) (p4.output.trans p3.output) ((p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans (p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))
          (fun n lo hi out => (p4.gpr_frame (by decide) n lo hi (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega)).trans
            (keep3 n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega))))
        blk (fun y => by omega)
    · -- young: the young list
      obtain ⟨c4, run4, p4⟩ := (young_fast c3 R3 (leafAt c3 p3.good p3.image p3.minstret p3.tick c3_1) regs3
        (by rw [r3_15]; exact h.young.startWin) hStart).run c3 ⟨p3.pc, rfl⟩
      have above : start.toNat < (rootValue x r).toNat := by
        have := bltu_true _ _ hStart; rwa [r3_10, startV] at this
      have keep4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15]) : gprGet c4.σ n = gprGet c3.σ n :=
        p4.gpr_frame (by decide) n lo hi out
      have c4_1 := (keep4 1 (by decide) (by decide) (by decide)).trans c3_1
      obtain ⟨c5, run5, p5⟩ := (toYoung_fast c4 (regsAt c4) (leafAt c4 p4.good p4.image p4.minstret p4.tick c4_1)
        trivial).run c4 ⟨p4.pc, rfl⟩
      have keepAll (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11, 12, 14, 15]) :
          gprGet c5.σ n = gprGet x.σ n := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at out
        exact (p5.gpr_frame (by decide) n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
          ((keep4 n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
            ((keep3 n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
              (kept2 n lo hi (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega))))
      have c5_11 : gprGet c5.σ 11 = some r :=
        (p5.gpr_frame (by decide) 11 (by decide) (by decide) (by decide)).trans
          ((keep4 11 (by decide) (by decide) (by decide)).trans
            ((keep3 11 (by decide) (by decide) (by decide)).trans c2_11))
      have mem5 : c5.σ.mem = x.σ.mem := by rw [p5.memory, wl_nil, p4.memory, wl_nil, mem3]
      have heap5 : HeapReady H cap c5 := HeapReady.of_mem h.heap mem5
      obtain ⟨cy, shx, hy⟩ := h.roots.young
      have sh5 : Shape c5.σ.mem globalRootsYoung cy := by rw [mem5]; exact shx
      have pc5 : PCAt insertPc c5 := p5.pc
      obtain ⟨d, run6, ret, cy', shy', kin, kold, kout, footIn⟩ := (ops.insert H cap globalRootsYoung cy r sp ra c5 sh5
        ⟨⟨p5.good, p5.image, p5.minstret, (keepAll 1 (by decide) (by decide) (by decide)).trans h.leaf.raReg,
            h.leaf.aligned, p5.tick⟩, heap5,
          ⟨(keepAll 2 (by decide) (by decide) (by decide)).trans h.stack, gholds_lookup _ p5.regs rfl, c5_11,
            gholds_lookup _ p5.regs rfl, trivial⟩, frame⟩).run c5 ⟨pc5, rfl⟩
      have g5 : GlobalRoots Shape foot c5.σ.mem rs ys os := by rw [mem5]; exact h.roots
      have fr : InsertFrame Shape foot H globalRootsYoung cy c5.σ.mem d.σ.mem :=
        { live := fun sk cells sh a f => (ops.live _ _ _ sh H cap c5 rfl heap5 a f).1
          seed := fun sk cells sh a f => (ops.live _ _ _ sh H cap c5 rfl heap5 a f).2
          kept := fun a nt nf lo seed => ret.kept a nt nf (Or.inl (by unfold opStack; omega)) seed }
      obtain ⟨g', memY⟩ := GlobalRoots.insert_young ops g5 ⟨fun x => h.fresh (by simp [x]), fun x => h.fresh (by simp [x])⟩ sh5 (by rw [mem5]; exact hy) shy' kin kold kout
        footIn fr
      have isYoung : Young start stop (rootValue x r) := ⟨blk, below, above⟩
      have notOld : ¬ Old start stop cls (rootValue x r) := fun o => o.2.1 ⟨below, above⟩
      have runs := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
      exact ⟨d, runs, filed_of_returned ops h runs (Or.inl rfl) shx (fun a _ => by rw [mem5])
        (fun a _ => by rw [mem5])
        (fun n hn => by
          have hr : 1 ≤ n ∧ n ≤ 31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
          exact keepAll n hr.1 hr.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega))
        (keepAll 3 (by decide) (by decide) (by decide))
        (p5.output.trans (p4.output.trans (p3.output.trans (p2.output.trans p1.output))))
        ((p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans ((p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans ((p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans ((p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))))) ret
        (g5.feet_young ops sh5 shy' footIn fr)
        ⟨keys d.σ.mem cy', os, g', fun k => (memY k).trans
          ⟨fun h => h.elim (fun e => Or.inl ⟨isYoung, e⟩) Or.inr, fun h => h.elim (fun p => Or.inl p.2) Or.inr⟩,
          lists_kept notOld⟩⟩
  · -- at or above `young_end`: the page table
    obtain ⟨c3, run3, p3⟩ := (aboveEnd_fast c2 R2 (leafAt c2 p2.good p2.image p2.minstret p2.tick c2_1) regs2
      (by rw [r2_15]; exact h.young.stopWin) hEnd).run c2 ⟨p2.pc, rfl⟩
    have above : stop.toNat ≤ (rootValue x r).toNat := by
      have := bgeu_true _ _ hEnd; rwa [r2_10, stopV] at this
    exact lookup_path ops pt h (run1.trans (run2.trans run3))
      (atLookup c3 (run1.trans (run2.trans run3)) p3.good p3.image p3.minstret p3.tick p3.pc
        (by rw [p3.memory, wl_nil, mem2]) p3.output (p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
        (fun n lo hi out => p3.gpr_frame (by decide) n lo hi (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at out ⊢; omega)))
      blk (fun y => by omega)

end OCaml.Vm.Primitives.Named.RegisterRoot
