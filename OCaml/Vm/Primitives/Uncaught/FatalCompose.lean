import OCaml.Vm.Primitives.Uncaught.FatalAtExit

/-!
# `caml_fatal_uncaught_exception` from its entry to the `do_at_exit` lookup

`FatalPre` gathers the facts at the entry: the caller's registers and the
named-value table (`FatalInput`), memprof (`MemprofAt`), the allocator
(`FatalHeap`), the exception (`ExnAt`), the domain record's backtrace fields
(`BacktraceAt`), and where memprof's and the save's stores fall relative to
what is read later. `fatal_to_atexit` composes the stages and supplies each
stage's premises from them.
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (regsAt TableShape TableFoot NodeBytes agree_of_getD strcmp_loaded
  mask_pinned)
open OCaml.Vm.Primitives.Uncaught.FormatException (FormatDone)

/-- **The fatal path's entry facts.** -/
structure FatalPre (ra sp exn s0 s1 s2 s3 np : BitVec 64) (name : List (BitVec 8)) (pl : Place)
    (named : List (String × Val)) (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val))
    (H : List (Nat × Nat)) (capacity charge : Nat) (p dom start trig active pos : BitVec 64) (c : Config) : Prop where
  input : FatalInput ra sp exn s0 s1 s2 s3 pl named chains c
  memprof : MemprofAt c.σ.mem p dom start trig
  heap : FatalHeap H capacity charge sp ra name.length p dom start trig c
  thrown : ExnAt c.σ.mem exn np name
  exnApart : ∀ a, ExnBytes exn np name.length a → OutL (memprofStores p dom start trig) a
  backtrace : BacktraceAt H c.σ.mem dom active pos
  /-- memprof's stores miss the backtrace fields -/
  backtraceApart : ∀ a, (dom + 232#64).toNat ≤ a → a < (dom + 232#64).toNat + 16 →
    OutL (memprofStores p dom start trig) a
  /-- memprof's stores and the backtrace clear miss the table -/
  tableApart : ∀ a, TableFoot chains a →
    OutL (memprofStores p dom start trig) a ∧ OutL [((dom + 232#64).toNat, 8, 0#64)] a
  /-- the table's nodes are live blocks' bytes (malloc'd) -/
  tableBlocks : ∀ b, b < 13 → ∀ e ∈ chains b, ∃ q n, (q, n) ∈ H ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧
    q ≤ e.1.toNat ∧ e.1.toNat + 16 + e.2.1.length + 1 ≤ q + n

/-- **`caml_fatal_uncaught_exception` from its entry to the `do_at_exit`
lookup**: the message is formatted (`FormatDone`), the backtrace saved and
the lookup done (`AtExitLooked`). -/
theorem fatal_to_atexit (persist : GprsPersist_Statement) (memPersist : MemPersist_Statement)
    {ra sp exn s0 s1 s2 s3 np : BitVec 64} {name : List (BitVec 8)} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {H : List (Nat × Nat)} {capacity charge : Nat}
    {p dom start trig active pos : BitVec 64} {c0 : Config}
    (pre : FatalPre ra sp exn s0 s1 s2 s3 np name pl named chains H capacity charge p dom start trig active pos c0) :
    ∃ f r res d x, Steps c0 d ∧
      FormatDone H capacity 0x8000dfc8#64 (sp + 18446744073709551568#64) 0#64 exn s2 (regsAt f 20) (regsAt f 21)
        name res f r ∧
      AtExitLooked H capacity sp res dom active pos name.length named chains r x d := by
  obtain ⟨d1, run1, look⟩ := fatal_lookup persist pre.input
  obtain ⟨f, run2, atf⟩ := fatal_suspend pre.input.frame look pre.memprof
  obtain ⟨res, r, run3, done⟩ := fatal_format pre.heap pre.thrown pre.exnApart atf
  have run := run1.trans (run2.trans run3)
  have fromF (a : Nat) (ha : a < heapEnd) (out : OutL (memprofStores p dom start trig) a) :
      (f.σ.mem[a]?).getD 0 = (c0.σ.mem[a]?).getD 0 := by rw [atf.kept a ha out]
  have inBlock (q n a : Nat) (member : (q, n) ∈ H) (lo : heapStart ≤ q) (hi : q + n ≤ heapEnd) (qa : q ≤ a)
      (aq : a < q + n) (out : OutL (memprofStores p dom start trig) a) :
      (r.σ.mem[a]?).getD 0 = (c0.σ.mem[a]?).getD 0 :=
    (done.blocks q n a member lo hi qa aq).trans (fromF a (by omega) out)
  have inLow (a : Nat) (lo : a < heapStart) (ng : ¬ allocGlobal a) (out : OutL (memprofStores p dom start trig) a) :
      (r.σ.mem[a]?).getD 0 = (c0.σ.mem[a]?).getD 0 :=
    (done.globals a lo ng).trans (fromF a (Nat.lt_of_lt_of_le lo (by decide)) out)
  have bt := pre.backtrace
  obtain ⟨q, n, member, qlo, qhi, qa, aq⟩ := bt.block
  have he : heapEnd < 2 ^ 64 := by decide
  have d240 : (dom + 240#64).toNat = (dom + 232#64).toNat + 8 := by
    have e : dom + 240#64 = dom + 232#64 + 8#64 := by rw [BitVec.add_assoc]; rfl
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have stateAddr : (0x80064d08#64 : BitVec 64).toNat = Layout.sym_Caml_state := rfl
  have btR : BacktraceAt H r.σ.mem dom active pos :=
    { domainWord := by
        have w := bt.domainWord
        rw [stateAddr] at w ⊢
        rw [ConsoleWrite.read8_same (m := c0.σ.mem) fun i hi => inLow _
          (by simp only [Layout.sym_Caml_state, heapStart]; omega)
          (by unfold allocGlobal InRange; simp only [Layout.sym_Caml_state]; omega)
          (pre.heap.storesApart _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]
        exact w
      activeWord := by
        rw [ConsoleWrite.read8_same (m := c0.σ.mem) fun i hi => inBlock q n _ member qlo qhi (by omega) (by omega)
          (pre.backtraceApart _ (by omega) (by omega))]
        exact bt.activeWord
      posWord := by
        rw [d240, ConsoleWrite.read8_same (m := c0.σ.mem) fun i hi => inBlock q n _ member qlo qhi (by omega)
          (by omega) (pre.backtraceApart _ (by omega) (by omega)), ← d240]
        exact bt.posWord
      activeWindow := bt.activeWindow
      posWindow := bt.posWindow
      block := bt.block }
  have tableR : TableShape r.σ.mem pl named chains :=
    pre.input.table.transport (fun a foot => agree_of_getD (by
        rcases foot with ⟨lo, hi⟩ | ⟨b, hb, e, hmem, lo, hi⟩
        · exact inLow a (by simp only [Layout.sym_named_value_table, heapStart] at *; omega)
            (by unfold allocGlobal InRange; simp only [Layout.sym_named_value_table] at *; omega)
            (pre.tableApart a (Or.inl ⟨lo, hi⟩)).1
        · obtain ⟨q', n', member', qlo', qhi', qe, eq⟩ := pre.tableBlocks b hb e hmem
          exact inBlock q' n' a member' qlo' qhi' (by omega) (by omega)
            (pre.tableApart a (Or.inr ⟨b, hb, e, hmem, lo, hi⟩)).1)
      (memPersist c0 r run a))
      (strcmp_loaded done.ready.image) (mask_pinned done.ready.image)
  obtain ⟨d, x, run4, ae⟩ := fatal_atexit persist pre.input.frame done btR tableR
    (fun a foot => (pre.tableApart a foot).2)
  exact ⟨f, r, res, d, x, run.trans run4, done, ae⟩

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
