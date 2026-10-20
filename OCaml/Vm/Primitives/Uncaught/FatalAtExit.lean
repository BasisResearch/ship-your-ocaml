import OCaml.Vm.Primitives.Uncaught.FatalFormat

/-!
# `caml_fatal_uncaught_exception`: the backtrace save and the `do_at_exit` lookup

After `msg = caml_format_exception(exn)` (`FormatDone`): the domain record's
`backtrace_active` and `backtrace_pos` are saved in `s3`/`s1` and
`backtrace_active` cleared (`BacktraceAt`), then
`caml_named_value("Pervasives.do_at_exit")` (`rodata_lookup`). The result is
`NULL` when nothing is registered, else the registered node.
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gprReg_ne_htif TableShape TableFoot NamedFound
  strOf agree_of_eq strcmp_loaded mask_pinned)
open OCaml.Vm.Primitives.Uncaught.FormatException (FormatDone ready_transport_framed)

/-- The domain record's backtrace fields at the save. -/
structure BacktraceAt (H : List (Nat × Nat)) (m : Mem) (dom active pos : BitVec 64) : Prop where
  domainWord : bytesVal .ld (read8 m (0x80064d08#64).toNat) = dom
  activeWord : bytesVal .lw (read8 m (dom + 232#64).toNat) = active
  posWord : bytesVal .lw (read8 m (dom + 240#64).toNat) = pos
  activeWindow : WriteWindow (dom + 232#64) 8
  posWindow : ReadWindow (dom + 240#64) 4
  /-- the fields lie in a live block (the domain record) -/
  block : ∃ q n, (q, n) ∈ H ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ (dom + 232#64).toNat ∧
    (dom + 232#64).toNat + 12 ≤ q + n

/-- After the lookup of `Pervasives.do_at_exit`: at `0x8000dff4`. -/
structure AtExitLooked (H : List (Nat × Nat)) (capacity : Nat) (sp res dom active pos : BitVec 64) (len : Nat)
    (named : List (String × Val)) (chains : Nat → List (BitVec 64 × List (BitVec 8) × Val))
    (before : Config) (r : BitVec 64) (d : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, len + 1) :: H) capacity (sp + 18446744073709551568#64)
    0x8000dff4#64 d
  pc : PCAt 0x8000dff4#64 d
  result : gprGet d.σ 10 = some r
  absent : named.lookup "Pervasives.do_at_exit" = none → r = 0#64
  present : ∀ v, named.lookup "Pervasives.do_at_exit" = some v → ∃ kb v',
    (r, kb, v') ∈ chains ((Named.NamedValue.hashBytes atExitName).toNat % 13) ∧ strOf kb = "Pervasives.do_at_exit" ∧
    named.lookup "Pervasives.do_at_exit" = some v'
  stateReg : gprGet d.σ 8 = some 0x80064d08#64
  posReg : gprGet d.σ 9 = some pos
  msgReg : gprGet d.σ 18 = some res
  activeReg : gprGet d.σ 19 = some active
  callee : ∀ k, 20 ≤ k → k ≤ 27 → gprGet d.σ k = gprGet before.σ k
  /-- below `heapEnd` only `backtrace_active` changed, to zero -/
  kept : ∀ a, a < heapEnd → OutL [((dom + 232#64).toNat, 8, 0#64)] a → d.σ.mem[a]? = before.σ.mem[a]?
  cleared : bytesT d.σ.mem (dom + 232#64).toNat 8 = 0#64
  output : Vsa.Machine.output d.σ = Vsa.Machine.output before.σ

/-- **The backtrace save and `caml_named_value("Pervasives.do_at_exit")`.** -/
theorem fatal_atexit (persist : GprsPersist_Statement) {H : List (Nat × Nat)} {capacity : Nat}
    {sp exn s2 s4 s5 res dom active pos : BitVec 64} {name : List (BitVec 8)} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {f r : Config}
    (frame : NativeFrame sp 128)
    (done : FormatDone H capacity 0x8000dfc8#64 (sp + 18446744073709551568#64) 0#64 exn s2 s4 s5 name res f r)
    (bt : BacktraceAt H r.σ.mem dom active pos) (table : TableShape r.σ.mem pl named chains)
    (tableApart : ∀ a, TableFoot chains a → OutL [((dom + 232#64).toNat, 8, 0#64)] a) :
    ∃ d x, Steps r d ∧ AtExitLooked H capacity sp res dom active pos name.length named chains r x d := by
  have leaf0 := done.ready.toLeafInput
  have r1 := regsAt_of leaf0.raReg
  have r10 := regsAt_of done.result
  have l0 : LeafInput (regsAt r 1) r := by rw [r1]; exact leaf0
  obtain ⟨q, n, member, qlo, qhi, qa, aq⟩ := bt.block
  have he : heapEnd < 2 ^ 64 := by decide
  have d240 : (dom + 240#64).toNat = (dom + 232#64).toNat + 8 := by
    have e : dom + 240#64 = dom + 232#64 + 8#64 := by rw [BitVec.add_assoc]; rfl
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have logEq : saveLog (regsAt r) (save_loads r.σ.mem (regsAt r)) = [((dom + 232#64).toNat, 8, 0#64)] := by
    simp only [saveLog, save_loads, List.getD_cons_zero, bt.domainWord]
  have aw := bt.activeWindow
  have hs : heapStart = 2147995968 := rfl
  obtain ⟨c1, run1, p1⟩ := (save_fast r (regsAt r) l0
    (by simp only [save_input, GHolds, r1, r10]; exact ⟨leaf0.raReg, done.result, trivial⟩)
    (by rw [bt.domainWord]; exact ⟨aw.lower, by have := aw.upper; omega, Or.inr (by have := aw.htif; omega)⟩)
    (by rw [bt.domainWord]; exact aw)
    (by rw [bt.domainWord]; exact bt.posWindow)
    (by rw [logEq, bt.domainWord]; simp only [List.take, OutLRange, d240]; exact ⟨Or.inr (by omega), trivial⟩)
    (by
      rw [logEq]
      constructor <;> simp only [OutLRange, Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;>
        exact ⟨Or.inl (by omega), trivial⟩)).run r ⟨done.pc, rfl⟩
  have o1 := p1.regs
  simp only [save_regs, save_loads, List.getD_cons_zero, List.getD_cons_succ, bt.domainWord, bt.activeWord,
    bt.posWord, r10, GHolds] at o1
  obtain ⟨g19, g9, -, g10, g18, -, g8, -, -⟩ := o1
  have k1 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [8, 9, 10, 14, 15, 18, 19]) :
      gprGet c1.σ k = gprGet r.σ k := p1.gpr_frame (by decide) k lo hi out
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary save_call_shape save_call_decode c1 (save_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret
    [(10, 2147833712#64), (9, pos), (8, 2147896584#64), (18, res), (19, active), (2, sp + 18446744073709551568#64)]
    ⟨g10, g9, g8, g18, g19, (k1 2 (by decide) (by decide) (by decide)).trans done.ready.stack, trivial⟩
    (by change KeysOK [10, 9, 8, 18, 19, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c1 ⟨p1.pc, rfl⟩
  have m2 : c2.σ.mem = writeLog r.σ.mem [((dom + 232#64).toNat, 8, 0#64)] := by rw [p2.memory, p1.memory, logEq]
  obtain ⟨d, x, run3, nf, absent, present⟩ := rodata_lookup frame atExitName_rodata
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
    (by have := p2.pc; rw [save_call_target] at this; exact this)
    (gholds_lookup (n := 2) _ p2.regs rfl) (gholds_lookup (n := 10) _ p2.regs rfl)
    (gholds_lookup (n := 8) _ p2.regs rfl) (gholds_lookup (n := 9) _ p2.regs rfl)
    (table.transport (fun a foot => agree_of_eq (by rw [m2]; exact writeLog_out _ _ _ (tableApart a foot)))
      (strcmp_loaded p2.image) (mask_pinned p2.image))
  have run := run1.trans (run2.trans run3)
  have keep (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19]) :
      gprGet d.σ k = gprGet r.σ k :=
    (nf.frame k lo hi (fun m => out (by simp at m; simp; omega))).trans
      ((p2.gpr_frame (by decide) k lo hi (fun m => out (by simp at m; simp [m]))).trans
        (k1 k lo hi (fun m => out (by simp at m; simp; omega))))
  have kept (a : Nat) (ha : a < heapEnd) (out : OutL [((dom + 232#64).toNat, 8, 0#64)] a) :
      d.σ.mem[a]? = r.σ.mem[a]? := by
    rw [nf.memory, low_writeLog frame _ (lookup_saveIn frame _ _ _) a ha, m2, writeLog_out _ _ _ out]
  have keptD (a : Nat) (ha : a < heapEnd) (out : OutL [((dom + 232#64).toNat, 8, 0#64)] a) :
      (d.σ.mem[a]?).getD 0 = (r.σ.mem[a]?).getD 0 := by rw [kept a ha out]
  have order : heapStart ≤ q := qlo
  have lib : LibraryReady d := done.ready.library.carry
    (GprsKept.of_steps persist run (keep 3 (by decide) (by decide) (by decide)))
    (nf.htif.trans ((p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans
      (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))))
  have leafD : LeafInput 0x8000dff4#64 d := ⟨nf.good, nf.image, nf.minstret, nf.returned, by decide, nf.tick⟩
  refine ⟨d, x, run, ?_⟩
  exact
    { ready := ready_transport_framed done.ready leafD lib
        (fun pin hp => by
          have := (allocator_sources pin hp).geometry.high
          exact keptD _ (by omega) ⟨Or.inl (by omega), trivial⟩)
        (fun i hi => keptD _ (by unfold Layout.sym_Caml_state heapEnd; omega)
          ⟨Or.inl (by simp only [Layout.sym_Caml_state] at *; omega), trivial⟩)
        (fun i hi => keptD _ (by unfold Layout.sym_pool heapEnd; omega)
          ⟨Or.inl (by simp only [Layout.sym_pool] at *; omega), trivial⟩)
        (fun a ha => keptD a (allocator_foot_below ha) ⟨by
          show a < (dom + 232#64).toNat ∨ (dom + 232#64).toNat + 8 ≤ a
          rcases allocator_payload_outside (List.mem_cons_of_mem _ member) qlo ha with h | h <;> omega, trivial⟩)
        nf.stack
      pc := nf.pc
      result := nf.result
      absent := fun h => absent (by rw [show strOf atExitName = "Pervasives.do_at_exit" by decide]; exact h)
      present := fun v h => by
        have e : strOf atExitName = "Pervasives.do_at_exit" := by decide
        obtain ⟨kb, v', m, k, l⟩ := present v (by rw [e]; exact h)
        exact ⟨kb, v', m, by rw [k, e], by rw [← e]; exact l⟩
      stateReg := nf.saved0
      posReg := nf.saved1
      msgReg := (nf.frame 18 (by decide) (by decide) (by decide)).trans
          ((p2.gpr_frame (by decide) 18 (by decide) (by decide) (by decide)).trans g18)
      activeReg := (nf.frame 19 (by decide) (by decide) (by decide)).trans
          ((p2.gpr_frame (by decide) 19 (by decide) (by decide) (by decide)).trans g19)
      callee := fun k lo hi => keep k (by omega) (by omega) (by simp; omega)
      kept := kept
      cleared := by
        rw [word_observed (m := writeLog r.σ.mem [((dom + 232#64).toNat, 8, 0#64)]) _ (fun i hi => by
          rw [nf.memory, low_writeLog frame _ (lookup_saveIn frame _ _ _) _ (by omega), m2])]
        exact word_writeLog_at _ _ 0 _ _ rfl trivial
      output := by simp only [Vsa.Machine.output]; rw [nf.output, p2.output, p1.output] }

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
