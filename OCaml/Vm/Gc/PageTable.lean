import OCaml.Vm.Primitives.Leaf
import Vsa.Sim.FnSummary
import Vsa.Sim.DlHeap

/-! # `caml_page_table_lookup` (named obligation, lane a6-gc)

`int caml_page_table_lookup(void *addr)` hashes `addr`'s page into
`caml_page_table` and returns the page's classification bits (`In_heap`,
`In_young`, `In_static_data`, `In_code_area`), `0` for an unregistered page.
It is a frameless leaf: it reads memory, writes none, and clobbers only
caller-saved registers. `PageTableLookup Table` names its summary over a
page-table shape `Table m cls` (memory `m` classifies page `p` as `cls p`).
Callers: `caml_register_generational_global_root`,
`caml_modify_generational_global_root` (lane a1-prims). `PageTableFrame Table
tfoot` frames the table by its own footprint `tfoot m`. -/
namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim OCaml.Vm Primitives LeanRV64DExecutable

def pageTableLookupPc : BitVec 64 := 0x8000a6b4#64

/-- The lookup returned to `ra` with the classification of `a`'s page. -/
structure PageTablePost (cls : Nat → Nat) (a ra : BitVec 64) (c d : Config) : Prop where
  good : GoodState d.σ
  image : ExecutableImage d
  minstret : ∃ v, d.σ.regs.get? Register.minstret = some v
  tick : d.tick < 2
  pc : PCAt ra d
  result : gprGet d.σ 10 = some (BitVec.ofNat 64 (cls (a.toNat / 4096)))
  memory : d.σ.mem = c.σ.mem
  output : d.σ.sailOutput = c.σ.sailOutput
  saved : ∀ n ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], gprGet d.σ n = gprGet c.σ n
  htif : d.σ.regs.get? Register.htif_payload_writes = c.σ.regs.get? Register.htif_payload_writes

/-- **The page-table lookup** (named obligation, lane a6-gc). -/
structure PageTableLookup (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop) : Prop where
  /-- the table (`caml_page_table` and its hash array) lies below the native stack -/
  frame : ∀ m m' cls, Table m cls → (∀ a, a < Vsa.Sim.DlHeap.heapEnd → (m'[a]?).getD 0 = (m[a]?).getD 0) →
    Table m' cls
  call : ∀ (c : Config) (ra a : BitVec 64) (cls : Nat → Nat), Table c.σ.mem cls → LeafInput ra c →
    gprGet c.σ 10 = some a → FnSummary pageTableLookupPc (fun d => d = c) (PageTablePost cls a ra c)

/-- **The page table's own footprint** (named obligation, lane a6-gc): `tfoot m`
covers `caml_page_table` and its hash array; stores outside it keep the table
and the footprint. A skiplist insertion (heap cells) lies outside it. -/
structure PageTableFrame (Table : Std.ExtHashMap Nat (BitVec 8) → (Nat → Nat) → Prop)
    (tfoot : Std.ExtHashMap Nat (BitVec 8) → Nat → Prop) : Prop where
  frame : ∀ m m' cls, Table m cls → (∀ a, tfoot m a → (m'[a]?).getD 0 = (m[a]?).getD 0) →
    Table m' cls ∧ ∀ a, tfoot m' a ↔ tfoot m a
  low : ∀ m cls, Table m cls → ∀ a, tfoot m a → a < Vsa.Sim.DlHeap.heapEnd

end OCaml.Vm.Gc
