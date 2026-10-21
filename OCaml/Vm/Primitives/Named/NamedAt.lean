import OCaml.Vm.Primitives.Named.NamedTransport
import Vsa.Densify.Transport
import Vsa.Sim.Boot.Bytes

/-!
# The named-value table in the loop invariant

`NamedAt c pl named` is the loop invariant's view of `callback.c`'s table:
the table's memory (`TableCore`) represents `world.named` in the densified
memory `fillZeroMem c.σ.mem`, and its bytes lie in RAM below the arena's end.
Stating it over the densified memory makes it a fact about total reads
(`getD 0`), which is what native paths' frames give (`NamedAt.frame`); at a
C call entry whose RAM is dense, `NamedAt.tableAt` turns it into
`NamedTableAt` of the real memory, with the code pins `strcmp` needs from the
image. `NamedFoot` is the footprint a native path's writes must miss.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.MemRepr OCaml.Bytecode OCaml.Vm OCaml.Vm.Primitives

/-- **The named-value table at a loop head**, with chains `chains`: they
represent `named` in the densified memory, and the table's bytes lie in RAM
below `heapEnd`. The loop invariant holds `∃ chains, NamedAt c pl named chains`. -/
structure NamedAt (c : Config) (pl : Place) (named : List (String × Val))
    (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)) : Prop where
  core : TableCore (Vsa.Densify.fillZeroMem c.σ.mem) pl named chains
  ram : ∀ a, TableFoot chains a → Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Sim.DlHeap.heapEnd

/-- The table's bytes at `c`, for any chains it holds. -/
def NamedFoot (c : Config) (pl : Place) (named : List (String × Val)) (a : Nat) : Prop :=
  ∃ chains, NamedAt c pl named chains ∧ TableFoot chains a

/-- Arbitrary nonzero bytes form a C string, with one character per byte. -/
theorem cstr_of_bytes {m : Mem} {a : Nat} {key : List (BitVec 8)}
    (bytes : ∀ i (hi : i < key.length), m[a + i]? = some key[i] ∧ key[i] ≠ 0)
    (nul : m[a + key.length]? = some 0) :
    CStr m a (key.map fun b => Char.ofNat b.toNat) := by
  induction key generalizing a with
  | nil => exact .nil (by simpa using nul)
  | cons b rest ih =>
    obtain ⟨hb, ne⟩ := bytes 0 (by simp)
    refine .cons (by simpa using hb) (by simpa using ne) b.isLt (ih ?_ ?_)
    · intro i hi
      have hb := bytes (i + 1) (by simpa using hi)
      change m[a + (i + 1)]? = some rest[i] ∧ rest[i] ≠ 0 at hb
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hb
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using nul

/-- The loop node's total reads supply a byte C string in dense RAM. -/
theorem _root_.OCaml.Vm.NamedNode.cstring {c : Config} {pl : Place} {node next : Nat}
    {key : List (BitVec 8)} {v : Val} (h : NamedNode c pl node next key v) :
    CString (Vsa.Densify.fillZeroMem c.σ.mem) (node + 16) (strOf key) := by
  have present (a : Nat) (lo : node ≤ a) (hi : a ≤ node + 16 + key.length) :
      (Vsa.Densify.fillZeroMem c.σ.mem)[a]? = some (byte c a) := by
    have low := h.low
    have high := h.arena
    rw [Vsa.Densify.fillZeroMem_ram c.σ.mem (by
      simp only [Vsa.Sim.DlHeap.heapStart, Vsa.Densify.ramBase] at low ⊢; omega) (by
      simp only [Vsa.Sim.DlHeap.heapEnd, Vsa.Densify.ramBase, Vsa.Densify.ramSize] at high ⊢; omega)]
    rw [byte_total]
  refine ⟨_, cstr_of_bytes (fun i hi => ?_) ?_, rfl⟩
  · exact ⟨(present _ (by omega) (by omega)).trans (congrArg some (h.keyBytes i hi).1),
      (h.keyBytes i hi).2⟩
  · exact (present _ (by omega) (by omega)).trans (congrArg some h.nul)

/-- The loop node supplies the lookup library's memory contract. -/
theorem _root_.OCaml.Vm.NamedNode.nodeAt {c : Config} {pl : Place} {node next : Nat}
    {key : List (BitVec 8)} {v : Val} (h : NamedNode c pl node next key v) :
    NodeAt (Vsa.Densify.fillZeroMem c.σ.mem) pl
      (BitVec.ofNat 64 node) (BitVec.ofNat 64 next) key v := by
  have low := h.low
  have high := h.arena
  have nb : node < 2 ^ 64 := by
    simp only [Vsa.Sim.DlHeap.heapEnd] at high; omega
  have off (k : Nat) (hk : k ≤ 16) :
      (BitVec.ofNat 64 node + BitVec.ofNat 64 k).toNat = node + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Vsa.Sim.DlHeap.heapEnd] at high
    omega
  have wn (a : Nat) : bytesT (Vsa.Densify.fillZeroMem c.σ.mem) a 8 = word c a :=
    Vsa.Sim.Boot.bytesT_memEqv (Vsa.Densify.memEqv_fillZeroMem c.σ.mem).symm a 8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nb] at this
    simp only [Vsa.Sim.DlHeap.heapStart] at low; omega
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nb, wn] using h.value
  · rw [read8_value, off 8 (by decide), wn]
    apply BitVec.eq_of_toNat_eq
    rw [h.next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      rw [← h.next]; exact (word c (node + 8)).isLt)]
  · constructor
    all_goals rw [off 8 (by decide)]
    · simp only [Vsa.Sim.DlHeap.heapStart] at low; omega
    · simp only [Vsa.Sim.DlHeap.heapEnd] at high; omega
    · apply Or.inr
      simp only [Layout.sym_tohost, Vsa.Sim.DlHeap.heapStart] at low ⊢; omega
  · rw [off 16 (by decide)]; exact h.cstring
  · intro cs str
    obtain ⟨ks, str0, eq⟩ := h.cstring
    rw [off 16 (by decide)] at str
    have same := str0.unique str
    have len : cs.length = key.length := by
      have := congrArg String.length eq
      simpa only [strOf_length, String.length_ofList, same] using this.symm
    constructor
    all_goals rw [off 16 (by decide)]
    all_goals try rw [len]
    · simp only [Vsa.Sim.DlHeap.heapStart] at low; omega
    · simp only [Vsa.Sim.DlHeap.heapEnd] at high; omega
    · simp only [Vsa.Sim.DlHeap.heapEnd] at high; omega
    · apply Or.inr
      simp only [Vsa.Sim.DlHeap.heapStart] at low; omega
    · apply Or.inr
      simp only [Vsa.Sim.tohostAddr, Vsa.Sim.LibraryLayout.tohostAddr,
        Vsa.Sim.DlHeap.heapStart] at low ⊢; omega
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nb] using h.arena

/-- Convert node addresses to the lookup library's machine words. -/
def machineNode (e : Nat × List (BitVec 8) × Val) : BitVec 64 × List (BitVec 8) × Val :=
  (BitVec.ofNat 64 e.1, e.2)

theorem _root_.OCaml.Vm.NamedChain.tableChain {c : Config} {pl : Place} {head : Nat}
    {nodes : List (Nat × List (BitVec 8) × Val)} (h : NamedChain c pl head nodes) :
    TableChain (Vsa.Densify.fillZeroMem c.σ.mem) pl (BitVec.ofNat 64 head) (nodes.map machineNode) := by
  -- discipline: allow(O5-run-induction) induction on a chain of heap nodes, not a run
  induction h with
  | nil => exact .nil
  | cons node _ ih => exact .cons node.nodeAt ih

/-- Each loop node occupies a bounded interval of the allocator arena. -/
theorem _root_.OCaml.Vm.NamedChain.bounds {c : Config} {pl : Place} {head : Nat}
    {nodes : List (Nat × List (BitVec 8) × Val)} (h : NamedChain c pl head nodes) :
    ∀ e ∈ nodes, Vsa.Sim.DlHeap.heapStart ≤ e.1 ∧
      e.1 + 16 + e.2.1.length + 1 ≤ Vsa.Sim.DlHeap.heapEnd := by
  -- discipline: allow(O5-run-induction) induction on a chain of heap nodes, not a run
  induction h with
  | nil => intro e he; cases he
  | cons node rest ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | tail
    · exact ⟨node.low, node.arena⟩
    · exact ih e tail

/-- The preserved loop representation supplies the named lookup contract,
including arbitrary byte keys and the exact character-count footprint. -/
theorem _root_.OCaml.Vm.NamedRepr.namedAt {c : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (Nat × List (BitVec 8) × Val)} (h : NamedRepr c pl named chains) :
    NamedAt c pl named (fun b => (chains b).map machineNode) := by
  have wn (a : Nat) : bytesT (Vsa.Densify.fillZeroMem c.σ.mem) a 8 = word c a :=
    Vsa.Sim.Boot.bytesT_memEqv (Vsa.Densify.memEqv_fillZeroMem c.σ.mem).symm a 8
  have bucket (b : Nat) (hb : b < 13) : (bucketAddr b).toNat = Layout.sym_named_value_table + 8 * b := by
    simp only [bucketAddr, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [Layout.sym_named_value_table]; omega
  constructor
  · constructor
    · intro b hb
      constructor
      all_goals rw [bucket b hb]
      · simp only [Layout.sym_named_value_table]; omega
      · simp only [Layout.sym_named_value_table]; omega
      · apply Or.inr
        simp only [Layout.sym_named_value_table, Layout.sym_tohost]; omega
    · intro b hb
      rw [read8_value, bucket b hb, wn]
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using (h.heads b hb).tableChain
    · intro b hb e he
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      exact h.placed b hb e' he'
    · intro k v
      constructor
      · intro mem
        obtain ⟨b, hb, n, kb, hn, eq⟩ := (h.entries k v).1 mem
        exact ⟨b, hb, BitVec.ofNat 64 n, kb, List.mem_map.2 ⟨(n, kb, v), hn, rfl⟩, eq⟩
      · rintro ⟨b, hb, n, kb, hn, eq⟩
        obtain ⟨⟨n', kb', v'⟩, he, e⟩ := List.mem_map.1 hn
        simp only [machineNode, Prod.mk.injEq] at e
        obtain ⟨_, rfl, rfl⟩ := e
        exact (h.entries k v').2 ⟨b, hb, n', kb', he, eq⟩
    · exact h.unique
  · intro a foot
    rcases foot with bucket | ⟨b, hb, e, he, lo, hi⟩
    · simp only [Layout.sym_named_value_table, Vsa.Densify.ramBase, Vsa.Sim.DlHeap.heapEnd] at bucket ⊢
      omega
    · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      obtain ⟨lower, upper⟩ := (h.heads b hb).bounds e' he'
      have lt : e'.1 < 2 ^ 64 := by simp only [Vsa.Sim.DlHeap.heapEnd] at upper; omega
      simp only [machineNode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at lo hi
      simp only [Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd, Vsa.Densify.ramBase] at lower upper ⊢
      omega

/-- Densified memories agree (with presence) on RAM bytes whose total reads agree. -/
theorem agree_fill {m m' : Mem} {a : Nat} (ram : Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Sim.DlHeap.heapEnd)
    (same : (m'[a]?).getD 0 = (m[a]?).getD 0) :
    Agree (Vsa.Densify.fillZeroMem m) (Vsa.Densify.fillZeroMem m') a := by
  have hi : a < Vsa.Densify.ramBase + Vsa.Densify.ramSize := by
    have := ram.2; simp only [Vsa.Sim.DlHeap.heapEnd, Vsa.Densify.ramBase, Vsa.Densify.ramSize] at *; omega
  apply agree_of_eq
  rw [Vsa.Densify.fillZeroMem_ram _ ram.1 hi, Vsa.Densify.fillZeroMem_ram _ ram.1 hi, same]

/-- **The table across a native path** whose total reads agree on the
table's bytes. -/
theorem NamedAt.frame {c c' : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : NamedAt c pl named chains)
    (same : ∀ a, TableFoot chains a → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0) :
    NamedAt c' pl named chains :=
  ⟨h.core.transport fun a t => agree_fill (h.ram a t) (same a t), h.ram⟩

/-- **At a dense C call entry** the table represents `named` in the real
memory, with the image's code pins. -/
theorem NamedAt.tableAt {c : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} (h : NamedAt c pl named chains)
    (dense : ∀ a, Vsa.Densify.ramBase ≤ a → a < Vsa.Densify.ramBase + Vsa.Densify.ramSize →
      (c.σ.mem[a]?).isSome)
    (image : ExecutableImage c) : TableShape c.σ.mem pl named chains := by
  have core := h.core
  rw [Vsa.Densify.fillZeroMem_eq_of_dense dense] at core
  exact { core with code := strcmp_loaded image, mask := mask_pinned image }

end OCaml.Vm.Primitives.Named.NamedValue
