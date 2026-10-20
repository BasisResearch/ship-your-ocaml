import OCaml.Vm.Gc.ChainScan
import OCaml.Vm.Primitives.Leaf
import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Boot.Startup.HeapReady

/-! # The runtime's skiplists (`caml_global_roots{,_old,_young}`)

`struct skiplist { struct skipcell * forward[17]; int level; }` and
`struct skipcell { uintnat key, data; struct skipcell * forward[]; }`: a cell's
key at `+0`, its level-0 link at `+16`. The level-0 chain (`Chain`) is what
`caml_scan_global_young_roots` walks (`ChainScan`).

`Ops Shape foot` is the named obligation (lane a6-gc) for
`caml_skiplist_insert` and `caml_skiplist_empty`: `Shape m sk cells` is a
well-formed skiplist at header `sk` whose level-0 chain is `cells`, kept by
stores outside its footprint `foot`. Insert allocates a cell
(`caml_stat_alloc`) and advances `random_seed`; empty frees every cell
(`caml_stat_free`) and clears the header. Both thread newlib's heap like
`CustomMemCall` (`HeapReady` in, `∃ HeapReady` out). -/
namespace OCaml.Vm.Gc.Skiplist
open Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives LeanRV64DExecutable
open OCaml.Vm.Boot.Startup (NativeFrame HeapReady)

def insertPc : BitVec 64 := 0x8002aafc#64
def emptyPc : BitVec 64 := 0x8002ade8#64
def removePc : BitVec 64 := 0x8002acd0#64

/-- `caml_global_roots`, `caml_global_roots_old`, `caml_global_roots_young`. -/
def globalRoots : Nat := 0x800684e0
def globalRootsOld : Nat := 0x80068570
def globalRootsYoung : Nat := 0x80068600

/-- A header: 17 forward links and the level. -/
def headerBytes : Nat := 144

/-- `random_level`'s state (a 32-bit word). -/
def randomSeed : Nat := 0x80064d10

/-- The stack an operation may use below `sp` (its frame and the allocator's). -/
def opStack : Nat := 768

/-- The level-0 chain from `first`. -/
def Chain (m : Std.ExtHashMap Nat (BitVec 8)) : BitVec 64 → List (BitVec 64) → Prop
  | p, [] => p = 0#64
  | p, cell :: cells => p = cell ∧ cell ≠ 0#64 ∧ Chain m (ChainScan.next m cell) cells

/-- A level-0 chain from `p` is unique. -/
theorem Chain.unique {m : Std.ExtHashMap Nat (BitVec 8)} :
    ∀ (p : BitVec 64) (xs ys : List (BitVec 64)), Chain m p xs → Chain m p ys → xs = ys
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, hx, ⟨hp, hy, _⟩ => absurd (hp ▸ hx : _ = 0#64) hy
  | _, _ :: _, [], ⟨hp, hx, _⟩, hy => absurd (hp ▸ hy : _ = 0#64) hx
  | p, x :: xs, y :: ys, ⟨hpx, _, rx⟩, ⟨hpy, _, ry⟩ => by
    have : x = y := hpx.symm.trans hpy
    subst this
    rw [Chain.unique _ xs ys rx ry]

theorem Chain.nil_of_zero {m : Std.ExtHashMap Nat (BitVec 8)} {cells : List (BitVec 64)}
    (h : Chain m 0#64 cells) : cells = [] := by
  cases cells with
  | nil => rfl
  | cons x xs => exact absurd h.1.symm h.2.1

/-- The keys (root addresses) of a chain. -/
def keys (m : Std.ExtHashMap Nat (BitVec 8)) (cells : List (BitVec 64)) : List (BitVec 64) :=
  cells.map (ChainScan.key m)

/-- At an operation's call. -/
structure CallInput (H : List (Nat × Nat)) (cap : Nat) (args : GRegs) (sp ra : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  heap : HeapReady H cap c
  regs : GHolds c.σ ((2, sp) :: args)
  frame : NativeFrame sp opStack

/-- An ABI return to `ra` with `sp` and the callee-saved registers kept, and
memory kept outside the stack below `sp`, newlib's own bytes, `random_seed`
and `touched`. -/
structure Returned (H : List (Nat × Nat)) (touched : Nat → Prop) (sp ra : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ x, d.σ.regs.get? Register.minstret = some x
  tick : d.tick < 2
  pc : PCAt ra d
  /-- `ra` restored before `ret` -/
  link : gprGet d.σ 1 = some ra
  stack : gprGet d.σ 2 = some sp
  saved : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet c.σ n
  gprs : GprsKept c d
  output : d.σ.sailOutput = c.σ.sailOutput
  htif : d.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes
  /-- newlib's heap after the call; its free bytes were free or touched before -/
  heap : ∃ H' cap', HeapReady H' cap' d ∧
    ∀ a, VsaIris.VsaHeap.vsaFoot H' a → VsaIris.VsaHeap.vsaFoot H a ∨ touched a
  kept : ∀ a, ¬ touched a → ¬ VsaIris.VsaHeap.vsaFoot H a →
    (a < sp.toNat - opStack ∨ sp.toNat ≤ a) → (a < randomSeed ∨ randomSeed + 4 ≤ a) →
    (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0

/-- **The skiplist operations** (named obligation, lane a6-gc). -/
structure Ops (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop) : Prop where
  level0 : ∀ m sk cells, Shape m sk cells → Chain m (bytesT m sk 8) cells
  /-- one cell per key -/
  nodup : ∀ m sk cells, Shape m sk cells → (keys m cells).Nodup
  /-- stores outside the footprint keep the shape and the footprint -/
  frame : ∀ m m' sk cells, Shape m sk cells → (∀ a, foot m sk cells a → (m'[a]?).getD 0 = (m[a]?).getD 0) →
    Shape m' sk cells ∧ ∀ a, foot m' sk cells a ↔ foot m sk cells a
  /-- the header and each cell's key and link words lie in the footprint -/
  header : ∀ m sk cells, Shape m sk cells → ∀ k < headerBytes, foot m sk cells (sk + k)
  cell : ∀ m sk cells, Shape m sk cells → ∀ x ∈ cells, ∀ k < 24, foot m sk cells (x.toNat + k)
  /-- the footprint is the header and live heap blocks, never newlib's free
  space, globals or `random_seed` -/
  live : ∀ m sk cells, Shape m sk cells → ∀ H cap c, c.σ.mem = m → HeapReady H cap c → ∀ a,
    foot m sk cells a → ¬ VsaIris.VsaHeap.vsaFoot H a ∧ (a < randomSeed ∨ randomSeed + 4 ≤ a)
  /-- the footprint lies above the code (headers in `.bss`, cells in the heap) -/
  high : ∀ m sk cells, Shape m sk cells → ∀ a, foot m sk cells a → tohostAddr ≤ a
  /-- … and below the native stack -/
  low : ∀ m sk cells, Shape m sk cells → ∀ a, foot m sk cells a → a < Vsa.Sim.DlHeap.heapEnd
  /-- an all-zero header in `.bss` is the empty skiplist (`level = 0`, every
  `forward[i] = NULL`); supplied at the startup cut by lane a0-boot -/
  init : ∀ m sk, tohostAddr ≤ sk → sk + headerBytes ≤ Vsa.Sim.DlHeap.heapStart →
    (sk + headerBytes ≤ randomSeed ∨ randomSeed + 4 ≤ sk) →
    (∀ k < headerBytes, (m[sk + k]?).getD 0 = 0) → Shape m sk []
  /-- `caml_skiplist_insert(sk, key, 0)` -/
  insert : ∀ H cap sk cells (key sp ra : BitVec 64) (c : Config), Shape c.σ.mem sk cells →
    CallInput H cap [(10, BitVec.ofNat 64 sk), (11, key), (12, 0#64)] sp ra c →
    FnSummary insertPc (fun d => d = c) (fun d =>
      Returned H (foot c.σ.mem sk cells) sp ra c d ∧
      ∃ cells', Shape d.σ.mem sk cells' ∧ key ∈ keys d.σ.mem cells' ∧
        (∀ k ∈ keys c.σ.mem cells, k ∈ keys d.σ.mem cells') ∧
        (∀ k ∈ keys d.σ.mem cells', k = key ∨ k ∈ keys c.σ.mem cells) ∧
        (∀ a, foot d.σ.mem sk cells' a → foot c.σ.mem sk cells a ∨ VsaIris.VsaHeap.vsaFoot H a))
  /-- `caml_skiplist_remove(sk, key)` -/
  remove : ∀ H cap sk cells (key sp ra : BitVec 64) (c : Config), Shape c.σ.mem sk cells →
    CallInput H cap [(10, BitVec.ofNat 64 sk), (11, key)] sp ra c →
    FnSummary removePc (fun d => d = c) (fun d =>
      Returned H (foot c.σ.mem sk cells) sp ra c d ∧
      ∃ cells', Shape d.σ.mem sk cells' ∧ key ∉ keys d.σ.mem cells' ∧
        (∀ k ∈ keys c.σ.mem cells, k ≠ key → k ∈ keys d.σ.mem cells') ∧
        (∀ k ∈ keys d.σ.mem cells', k ∈ keys c.σ.mem cells) ∧
        (∀ a, foot d.σ.mem sk cells' a → foot c.σ.mem sk cells a))
  /-- `caml_skiplist_empty(sk)` -/
  empty : ∀ H cap sk cells (sp ra : BitVec 64) (c : Config), Shape c.σ.mem sk cells →
    CallInput H cap [(10, BitVec.ofNat 64 sk)] sp ra c →
    FnSummary emptyPc (fun d => d = c) (fun d =>
      Returned H (foot c.σ.mem sk cells) sp ra c d ∧ Shape d.σ.mem sk [] ∧
        (∀ a, foot d.σ.mem sk [] a → foot c.σ.mem sk cells a))

/-- **The global roots**: `caml_global_roots`, `_young` and `_old` are
skiplists whose level-0 keys are exactly `rs`, `ys` and `os`. -/
structure GlobalRoots (Shape : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Prop)
    (foot : Std.ExtHashMap Nat (BitVec 8) → Nat → List (BitVec 64) → Nat → Prop)
    (m : Std.ExtHashMap Nat (BitVec 8)) (rs ys os : List (BitVec 64)) : Prop where
  roots : ∃ cells, Shape m globalRoots cells ∧ keys m cells = rs
  young : ∃ cells, Shape m globalRootsYoung cells ∧ keys m cells = ys
  old : ∃ cells, Shape m globalRootsOld cells ∧ keys m cells = os
  /-- a root is registered once -/
  distinct : (rs ++ ys ++ os).Nodup
  /-- the three lists' footprints are disjoint -/
  apart : ∀ c1 c2 c3 a, Shape m globalRoots c1 → Shape m globalRootsYoung c2 → Shape m globalRootsOld c3 →
    (foot m globalRoots c1 a → ¬ foot m globalRootsYoung c2 a ∧ ¬ foot m globalRootsOld c3 a) ∧
    (foot m globalRootsYoung c2 a → ¬ foot m globalRootsOld c3 a)

end OCaml.Vm.Gc.Skiplist
