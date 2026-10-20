import OCaml.Vm.Primitives.Uncaught.FatalAtExit

/-!
# `caml_fatal_uncaught_exception`: `do_at_exit`, the restore and the report call

At `0x8000dff4` (`AtExitLooked`), `beqz a0` skips the callback when nothing is
registered. Otherwise `caml_callback_exn(*at_exit, Val_unit)` runs the
registered closure. The callback re-enters the interpreter, so its return is a
named obligation (`AtExitCallback`). Both branches reach `0x8000e004`
(`AtReport`, `fatal_doAtExit`). There the backtrace fields are restored and
`fprintf(stderr, "Fatal error: exception %s\n", msg)` is called (`fatal_report`,
post `AtFprintf`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gprReg_ne_htif TableShape)
open OCaml.Vm.Primitives.Uncaught.FormatException (ready_transport_framed beq_of_ne)

/-- Apart from the domain record's backtrace fields (`dom + 232`, 16 bytes). -/
def FieldsApart (dom : BitVec 64) (a : Nat) : Prop :=
  a < (dom + 232#64).toNat ∨ (dom + 232#64).toNat + 16 ≤ a

/-- The formatted message at `res`: the name and its terminator. -/
structure MessageAt (m : Mem) (res : BitVec 64) (name : List (BitVec 8)) : Prop where
  bytes : ∀ i (hi : i < name.length), (m[res.toNat + i]?).getD 0 = name[i]
  term : (m[res.toNat + name.length]?).getD 0 = 0#8

theorem MessageAt.transport {m m' : Mem} {res : BitVec 64} {name : List (BitVec 8)} (h : MessageAt m res name)
    (same : ∀ a, res.toNat ≤ a → a ≤ res.toNat + name.length → (m'[a]?).getD 0 = (m[a]?).getD 0) :
    MessageAt m' res name :=
  ⟨fun i hi => by rw [same _ (by omega) (by omega)]; exact h.bytes i hi,
    by rw [same _ (by omega) (Nat.le_refl _)]; exact h.term⟩

/-- newlib's `stderr`: `_impure_ptr` and its `_stderr` field. -/
structure StderrAt (m : Mem) (imp err : BitVec 64) : Prop where
  impureWord : bytesVal .ld (read8 m (0x800648f8#64).toNat) = imp
  stderrWord : bytesVal .ld (read8 m (imp + 24#64).toNat) = err
  window : ReadWindow (imp + 24#64) 8
  high : (imp + 24#64).toNat + 8 ≤ heapEnd

/-- The bytes `StderrAt` reads. -/
def StderrBytes (imp : BitVec 64) (a : Nat) : Prop :=
  (Layout.sym_impure_ptr ≤ a ∧ a < Layout.sym_impure_ptr + 8) ∨
    ((imp + 24#64).toNat ≤ a ∧ a < (imp + 24#64).toNat + 8)

theorem StderrAt.transport {m m' : Mem} {imp err : BitVec 64} (h : StderrAt m imp err)
    (same : ∀ a, StderrBytes imp a → (m'[a]?).getD 0 = (m[a]?).getD 0) : StderrAt m' imp err := by
  have ip : (0x800648f8#64 : BitVec 64).toNat = Layout.sym_impure_ptr := rfl
  refine ⟨?_, ?_, h.window, h.high⟩
  · rw [ConsoleWrite.read8_same (m := m) fun i hi => same _ (Or.inl ⟨by omega, by omega⟩)]
    exact h.impureWord
  · rw [ConsoleWrite.read8_same (m := m) fun i hi => same _ (Or.inr ⟨by omega, by omega⟩)]
    exact h.stderrWord

/-- The low words the path's tail reads: `caml_abort_on_uncaught_exn` and
newlib's atexit list `__atexit`. -/
def TailBytes (a : Nat) : Prop :=
  (Layout.sym_caml_abort_on_uncaught_exn ≤ a ∧ a < Layout.sym_caml_abort_on_uncaught_exn + 8) ∨
    (Layout.sym_atexit ≤ a ∧ a < Layout.sym_atexit + 8)

/-- No abort after the report, and no atexit registrations. -/
structure TailLow (m : Mem) : Prop where
  abort : bytesVal .lw (read8 m Layout.sym_caml_abort_on_uncaught_exn) = 0#64
  noAtexit : bytesVal .ld (read8 m Layout.sym_atexit) = 0#64

theorem TailLow.transport {m m' : Mem} (h : TailLow m)
    (same : ∀ a, TailBytes a → (m'[a]?).getD 0 = (m[a]?).getD 0) : TailLow m' := by
  refine ⟨?_, ?_⟩
  · rw [ConsoleWrite.read8_same (m := m) fun i hi => same _ (Or.inl ⟨by omega, by omega⟩)]
    exact h.abort
  · rw [ConsoleWrite.read8_same (m := m) fun i hi => same _ (Or.inr ⟨by omega, by omega⟩)]
    exact h.noAtexit

/-- What the `do_at_exit` step prints: nothing when no callback is
registered, else the callback's output `printed`. -/
def atExitOutput (named : List (String × Val)) (printed : String) : String :=
  match named.lookup "Pervasives.do_at_exit" with
  | none => ""
  | some _ => printed

/-- What `caml_callback_exn` keeps, from its call to its return to `0x8000e004`:
the callee-saved registers, readiness with the message block first and the
domain record among the other live blocks, the message, `stderr` and the abort flag, and
the console up to what the callback printed. -/
structure CallbackReturned (live : List (Nat × Nat)) (capacity : Nat) (sp ra res dom imp : BitVec 64) (len : Nat)
    (printed : String)
    (before : List (Nat × Nat)) (c e : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, len + 1) :: live) capacity (sp + 18446744073709551568#64) ra e
  pc : PCAt 0x8000e004#64 e
  callee : ∀ k, (k = 8 ∨ k = 9 ∨ (18 ≤ k ∧ k ≤ 27)) → gprGet e.σ k = gprGet c.σ k
  domainLive : ∀ q n, (q, n) ∈ before → q ≤ (dom + 232#64).toNat → (dom + 232#64).toNat + 16 ≤ q + n → (q, n) ∈ live
  message : ∀ a, res.toNat ≤ a → a ≤ res.toNat + len → (e.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0
  stderr : ∀ a, StderrBytes imp a → (e.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0
  tailKept : ∀ a, TailBytes a → (e.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0
  output : Vsa.Machine.output e.σ = Vsa.Machine.output c.σ ++ printed

/-- **Named obligation: `caml_callback_exn(*at_exit, Val_unit)` returns.**
The callee is the registered closure `clo` run by a nested interpreter
(F4), whose effects the uncaught path ignores apart from what
`CallbackReturned` keeps. Supplied by the callback simulation (F4);
`caml_fatal_uncaught_exception` ignores an exception from the callback, so
this covers both outcomes. -/
structure AtExitCallback (live : List (Nat × Nat)) (capacity : Nat) (sp clo res dom imp : BitVec 64) (len : Nat)
    (printed : String) : Prop where
  returns : ∀ c, PCAt 0x800212b8#64 c →
    RuntimeReadyL imageLive ((res.toNat, len + 1) :: live) capacity (sp + 18446744073709551568#64) 0x8000e004#64 c →
    gprGet c.σ 10 = some clo → gprGet c.σ 11 = some 1#64 →
    ∃ e live' capacity' ra, Steps c e ∧ CallbackReturned live' capacity' sp ra res dom imp len printed live c e

/-- At `0x8000e004`, after `do_at_exit` (either branch); the message block
heads the live list. -/
structure AtReport (live : List (Nat × Nat)) (capacity : Nat) (sp ra res dom active pos imp err : BitVec 64)
    (name : List (BitVec 8)) (cbOut : String) (before e : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, name.length + 1) :: live) capacity (sp + 18446744073709551568#64)
    ra e
  pc : PCAt 0x8000e004#64 e
  stateReg : gprGet e.σ 8 = some 0x80064d08#64
  posReg : gprGet e.σ 9 = some pos
  msgReg : gprGet e.σ 18 = some res
  activeReg : gprGet e.σ 19 = some active
  callee : ∀ k, 20 ≤ k → k ≤ 27 → gprGet e.σ k = gprGet before.σ k
  /-- the domain record is a live block -/
  domainBlock : ∃ q n, (q, n) ∈ live ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ (dom + 232#64).toNat ∧
    (dom + 232#64).toNat + 16 ≤ q + n
  message : MessageAt e.σ.mem res name
  stderr : StderrAt e.σ.mem imp err
  tail : TailLow e.σ.mem
  output : Vsa.Machine.output e.σ = Vsa.Machine.output before.σ ++ cbOut

/-- **`if (at_exit != NULL) caml_callback_exn(*at_exit, Val_unit)`**, both
branches to `0x8000e004`. -/
theorem fatal_doAtExit {H : List (Nat × Nat)} {capacity : Nat} {sp res dom active pos imp err x : BitVec 64}
    {name : List (BitVec 8)} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {r d : Config} {printed : String}
    (looked : AtExitLooked H capacity sp res dom active pos name.length named chains r x d)
    (table : TableShape d.σ.mem pl named chains)
    (message : MessageAt r.σ.mem res name) (stderr : StderrAt r.σ.mem imp err) (tail : TailLow r.σ.mem)
    (msgHigh : res.toNat + (name.length + 1) ≤ heapEnd)
    (msgApart : ∀ a, res.toNat ≤ a → a ≤ res.toNat + name.length → FieldsApart dom a)
    (stderrApart : ∀ a, StderrBytes imp a → FieldsApart dom a)
    (domainBlock : ∃ q n, (q, n) ∈ H ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ (dom + 232#64).toNat ∧
      (dom + 232#64).toNat + 16 ≤ q + n)
    (nodeWindows : ∀ b, b < 13 → ∀ e ∈ chains b, ReadWindow e.1 8)
    (callback : ∀ v clo, named.lookup "Pervasives.do_at_exit" = some v → valWord pl v = some clo →
      AtExitCallback H capacity sp clo res dom imp name.length printed) :
    ∃ e live capacity' ra, Steps d e ∧
      AtReport live capacity' sp ra res dom active pos imp err name (atExitOutput named printed) r e := by
  have he : heapEnd < 2 ^ 64 := by decide
  have fromR (a : Nat) (ha : a < heapEnd) (apart : FieldsApart dom a) :
      (d.σ.mem[a]?).getD 0 = (r.σ.mem[a]?).getD 0 := by
    unfold FieldsApart at apart
    rw [looked.kept a ha ⟨show a < (dom + 232#64).toNat ∨ (dom + 232#64).toNat + 8 ≤ a by omega, trivial⟩]
  have msgD : MessageAt d.σ.mem res name :=
    message.transport fun a lo hi => fromR a (by omega) (msgApart a lo hi)
  have errLow (a : Nat) (ha : StderrBytes imp a) : a < heapEnd := by
    have := stderr.high
    unfold StderrBytes Layout.sym_impure_ptr at ha
    unfold heapEnd at *
    omega
  have errD : StderrAt d.σ.mem imp err :=
    stderr.transport fun a ha => fromR a (errLow a ha) (stderrApart a ha)
  obtain ⟨q, n, member, qlo, qhi, qa, aq⟩ := domainBlock
  have abortD : TailLow d.σ.mem := tail.transport fun a ha => fromR a
    (by unfold TailBytes Layout.sym_caml_abort_on_uncaught_exn Layout.sym_atexit at ha; unfold heapEnd; omega)
    (Or.inl (by unfold TailBytes Layout.sym_caml_abort_on_uncaught_exn Layout.sym_atexit at ha; unfold heapStart at qlo; omega))
  have leafD := looked.ready.toLeafInput
  have r1 := regsAt_of leafD.raReg
  have r10 := regsAt_of looked.result
  have l0 : LeafInput (regsAt d 1) d := by rw [r1]; exact leafD
  have regs0 : GHolds d.σ [(10, regsAt d 10)] := by rw [r10]; exact ⟨looked.result, trivial⟩
  by_cases hx : x = 0#64
  · -- nothing registered: `beqz a0` to the report
    obtain ⟨e, run, p⟩ := (atExitNone_fast d (regsAt d) l0 regs0 (by rw [r10, hx]; decide)).run d ⟨looked.pc, rfl⟩
    have me : e.σ.mem = d.σ.mem := p.memory
    have k (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet e.σ n = gprGet d.σ n :=
      p.gpr_frame (by decide) n lo hi (by simp)
    have leafE : LeafInput 0x8000dff4#64 e :=
      ⟨p.good, p.image, p.minstret, (k 1 (by decide) (by decide)).trans leafD.raReg, by decide, p.tick⟩
    refine ⟨e, H, capacity, 0x8000dff4#64, run, ?_⟩
    exact
      { ready := ready_transport_framed looked.ready leafE
          (looked.ready.library.carry p.kept (p.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))
          (fun _ _ => by rw [me]) (fun _ _ => by rw [me]) (fun _ _ => by rw [me]) (fun _ _ => by rw [me])
          ((k 2 (by decide) (by decide)).trans looked.ready.stack)
        pc := p.pc
        stateReg := (k 8 (by decide) (by decide)).trans looked.stateReg
        posReg := (k 9 (by decide) (by decide)).trans looked.posReg
        msgReg := (k 18 (by decide) (by decide)).trans looked.msgReg
        activeReg := (k 19 (by decide) (by decide)).trans looked.activeReg
        callee := fun j lo hi => (k j (by omega) (by omega)).trans (looked.callee j lo hi)
        domainBlock := ⟨q, n, member, qlo, qhi, qa, aq⟩
        message := msgD.transport fun a _ _ => by rw [me]
        stderr := errD.transport fun a _ => by rw [me]
        tail := abortD.transport fun a _ => by rw [me]
        output := by
          have none' : named.lookup "Pervasives.do_at_exit" = none := by
            cases h : named.lookup "Pervasives.do_at_exit" with
            | none => rfl
            | some v =>
              obtain ⟨kb, v', node, -, -⟩ := looked.present v h
              obtain ⟨_, nd⟩ := (table.heads _ (Nat.mod_lt _ (by decide))).node_of_mem _ node
              exact absurd hx nd.nonnull
          simp only [atExitOutput, none', String.append_empty]
          rw [← looked.output]; simp only [Vsa.Machine.output]; rw [p.output] }
  · -- the callback: `ld a0, 0(a0); li a1, 1; call caml_callback_exn`
    have some : ∃ v, named.lookup "Pervasives.do_at_exit" = some v := by
      cases h : named.lookup "Pervasives.do_at_exit" with
      | none => exact absurd (looked.absent h) hx
      | some v => exact ⟨v, rfl⟩
    obtain ⟨v, hv⟩ := some
    obtain ⟨kb, v', node, -, hv'⟩ := looked.present v hv
    have w0 : ReadWindow x 8 := nodeWindows _ (Nat.mod_lt _ (by decide)) _ node
    obtain ⟨c1, run1, p1⟩ := (atExitSome_fast d (regsAt d) l0 regs0 (beq_of_ne (by rw [r10]; exact hx))).run d
      ⟨looked.pc, rfl⟩
    have m1 : c1.σ.mem = d.σ.mem := p1.memory
    have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c1.σ n = gprGet d.σ n :=
      p1.gpr_frame (by decide) n lo hi (by simp)
    have e1 : gprGet c1.σ 1 = some 0x8000dff4#64 := (k1 1 (by decide) (by decide)).trans leafD.raReg
    have e10 : gprGet c1.σ 10 = some x := (k1 10 (by decide) (by decide)).trans looked.result
    have l1 : LeafInput (regsAt c1 1) c1 := by
      rw [regsAt_of e1]; exact ⟨p1.good, p1.image, p1.minstret, e1, by decide, p1.tick⟩
    obtain ⟨c2, run2, p2⟩ := (callback_fast c1 (regsAt c1) l1
      (by simp only [callback_input, GHolds, regsAt_of e1, regsAt_of e10]; exact ⟨e1, e10, trivial⟩)
      (by rw [regsAt_of e10]; exact w0)).run c1 ⟨p1.pc, rfl⟩
    have o2 := p2.regs
    simp only [callback_regs, callback_loads, regsAt_of e1, regsAt_of e10, List.getD_cons_zero, read8_value, m1,
      GHolds] at o2
    obtain ⟨g11, g10, -⟩ := o2
    have m2 : c2.σ.mem = d.σ.mem := by rw [p2.memory, Named.NamedValue.wl_nil, m1]
    have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10, 11]) : gprGet c2.σ n = gprGet c1.σ n :=
      p2.gpr_frame (by decide) n lo hi out
    have g2 : gprGet c2.σ 2 = some (sp + 18446744073709551568#64) :=
      (k2 2 (by decide) (by decide) (by decide)).trans ((k1 2 (by decide) (by decide)).trans looked.ready.stack)
    obtain ⟨c3, run3, p3⟩ := (call_registers_summary callback_call_shape callback_call_decode c2
      (callback_call_pins p2.image) p2.good p2.image p2.tick p2.minstret
      [(10, bytesT d.σ.mem x.toNat 8), (11, 1#64), (2, sp + 18446744073709551568#64)] ⟨g10, g11, g2, trivial⟩
      (by change KeysOK [10, 11, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c2 ⟨p2.pc, rfl⟩
    have m3 : c3.σ.mem = d.σ.mem := by rw [p3.memory, m2]
    have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1]) : gprGet c3.σ n = gprGet c2.σ n :=
      p3.gpr_frame (by decide) n lo hi out
    have via (n : Nat) (lo : 2 ≤ n) (hi : n ≤ 31) (out : n ≠ 10 ∧ n ≠ 11) : gprGet c3.σ n = gprGet d.σ n :=
      (k3 n (by omega) hi (by simp; omega)).trans ((k2 n (by omega) hi (by simp; omega)).trans (k1 n (by omega) hi))
    have leaf3 : LeafInput 0x8000e004#64 c3 :=
      ⟨p3.good, p3.image, p3.minstret, gholds_lookup (n := 1) _ p3.regs rfl, by decide, p3.tick⟩
    have ready3 := ready_transport_framed looked.ready leaf3
      (((looked.ready.library.carry p1.kept (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p2.kept
        (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p3.kept
        (p3.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))
      (fun _ _ => by rw [m3]) (fun _ _ => by rw [m3]) (fun _ _ => by rw [m3]) (fun _ _ => by rw [m3])
      (gholds_lookup (n := 2) _ p3.regs rfl)
    obtain ⟨e, live, capacity', ra, run4, cb⟩ := (callback v' _ hv' (table.value_of_mem (Nat.mod_lt _ (by decide)) node)).returns c3
      (by have := p3.pc; rw [callback_call_target] at this; exact this) ready3
      (gholds_lookup (n := 10) _ p3.regs rfl) (gholds_lookup (n := 11) _ p3.regs rfl)
    have saved (k : Nat) (hk : k = 8 ∨ k = 9 ∨ (18 ≤ k ∧ k ≤ 27)) : gprGet e.σ k = gprGet d.σ k :=
      (cb.callee k hk).trans (via k (by omega) (by omega) (by omega))
    refine ⟨e, live, capacity', ra, run1.trans (run2.trans (run3.trans run4)), ?_⟩
    exact
      { ready := cb.ready
        pc := cb.pc
        stateReg := (saved 8 (by decide)).trans looked.stateReg
        posReg := (saved 9 (by decide)).trans looked.posReg
        msgReg := (saved 18 (by decide)).trans looked.msgReg
        activeReg := (saved 19 (by decide)).trans looked.activeReg
        callee := fun j lo hi => (saved j (by omega)).trans (looked.callee j lo hi)
        domainBlock := ⟨q, n, cb.domainLive q n member qa aq, qlo, qhi, qa, aq⟩
        message := msgD.transport fun a lo hi => by rw [cb.message a lo hi, m3]
        stderr := errD.transport fun a ha => by rw [cb.stderr a ha, m3]
        tail := abortD.transport fun a ha => by rw [cb.tailKept a ha, m3]
        output := by
          simp only [atExitOutput, hv]
          rw [cb.output, ← looked.output]
          simp only [Vsa.Machine.output]
          rw [p3.output, p2.output, p1.output] }

/-- At `fprintf`'s entry: `fprintf(stderr, "Fatal error: exception %s\n", msg)`,
returning to `0x8000e02c`, with the backtrace fields restored. -/
structure AtFprintf (live : List (Nat × Nat)) (capacity : Nat) (sp res dom active pos err : BitVec 64)
    (name : List (BitVec 8)) (cbOut : String) (before g : Config) : Prop where
  ready : RuntimeReadyL imageLive ((res.toNat, name.length + 1) :: live) capacity (sp + 18446744073709551568#64)
    0x8000e02c#64 g
  pc : PCAt 0x8003ee20#64 g
  stream : gprGet g.σ 10 = some err
  format : gprGet g.σ 11 = some 0x80056470#64
  arg : gprGet g.σ 12 = some res
  stateReg : gprGet g.σ 8 = some 0x80064d08#64
  msgReg : gprGet g.σ 18 = some res
  callee : ∀ k, 20 ≤ k → k ≤ 27 → gprGet g.σ k = gprGet before.σ k
  domainBlock : ∃ q n, (q, n) ∈ live ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ (dom + 232#64).toNat ∧
    (dom + 232#64).toNat + 16 ≤ q + n
  message : MessageAt g.σ.mem res name
  activeRestored : bytesT g.σ.mem (dom + 232#64).toNat 8 = active
  posRestored : bytesT g.σ.mem (dom + 240#64).toNat 8 = pos
  tail : TailLow g.σ.mem
  output : Vsa.Machine.output g.σ = Vsa.Machine.output before.σ ++ cbOut

/-- **The restore and the call of `fprintf`**: `backtrace_active` and
`backtrace_pos` are stored back, `stderr` is loaded through `_impure_ptr`. -/
theorem fatal_report {live : List (Nat × Nat)} {capacity : Nat} {sp ra res dom active pos imp err : BitVec 64}
    {name : List (BitVec 8)} {cbOut : String} {r e : Config}
    (at_ : AtReport live capacity sp ra res dom active pos imp err name cbOut r e)
    (domain : dom = firstDomainPtr) (activeWindow : WriteWindow (dom + 232#64) 8)
    (msgApart : ∀ a, res.toNat ≤ a → a ≤ res.toNat + name.length → FieldsApart dom a)
    (stderrApart : ∀ a, StderrBytes imp a → FieldsApart dom a) :
    ∃ g, Steps e g ∧ AtFprintf live capacity sp res dom active pos err name cbOut r g := by
  have he : heapEnd < 2 ^ 64 := by decide
  obtain ⟨q, n, member, qlo, qhi, qa, aq⟩ := at_.domainBlock
  have hs : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  have d240 : (dom + 240#64).toNat = (dom + 232#64).toNat + 8 := by
    have e : dom + 240#64 = dom + 232#64 + 8#64 := by rw [BitVec.add_assoc]; rfl
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have leaf0 := at_.ready.toLeafInput
  have r1 := regsAt_of leaf0.raReg
  have r8 := regsAt_of at_.stateReg
  have r9 := regsAt_of at_.posReg
  have r18 := regsAt_of at_.msgReg
  have r19 := regsAt_of at_.activeReg
  have l0 : LeafInput (regsAt e 1) e := by rw [r1]; exact leaf0
  have stateAddr : (0x80064d08#64 : BitVec 64).toNat = Layout.sym_Caml_state := rfl
  have dw : bytesVal .ld (read8 e.σ.mem (0x80064d08#64).toNat) = dom := by
    rw [read8_value, stateAddr, at_.ready.domainWord, domain]
  have std := at_.stderr
  have posWindow : WriteWindow (dom + 240#64) 8 :=
    ⟨by have := activeWindow.lower; omega, by rw [d240]; omega,
      by have := activeWindow.htif; omega, by have := activeWindow.aligned; omega⟩
  have logEq : reportLog (regsAt e) (report_loads e.σ.mem (regsAt e)) =
      [((dom + 232#64).toNat, 8, active), ((dom + 240#64).toNat, 8, pos)] := by
    simp only [reportLog, report_loads, List.getD_cons_zero, r8, dw, r9, r19]
  have outLog (a : Nat) (apart : FieldsApart dom a) :
      OutL [((dom + 232#64).toNat, 8, active), ((dom + 240#64).toNat, 8, pos)] a := by
    unfold FieldsApart at apart
    show (a < (dom + 232#64).toNat ∨ (dom + 232#64).toNat + 8 ≤ a) ∧
      (a < (dom + 240#64).toNat ∨ (dom + 240#64).toNat + 8 ≤ a) ∧ True
    rw [d240]
    exact ⟨by omega, by omega, trivial⟩
  obtain ⟨g1, run1, p1⟩ := (report_fast e (regsAt e) l0
    (by simp only [report_input, GHolds, r1, r8, r9, r18, r19]
        exact ⟨leaf0.raReg, at_.stateReg, at_.posReg, at_.msgReg, at_.activeReg, trivial⟩)
    (by rw [r8]; exact ⟨by decide, by decide, Or.inr (by decide)⟩)
    (by rw [r8, dw]; exact activeWindow)
    (by rw [r8, dw]; exact posWindow)
    (by rw [std.impureWord]; exact std.window)
    (by
      rw [logEq, std.impureWord]
      have h1 := stderrApart _ (Or.inr ⟨Nat.le_refl _, by omega⟩)
      have h2 := stderrApart ((imp + 24#64).toNat + 7) (Or.inr ⟨by omega, by omega⟩)
      unfold FieldsApart at h1 h2
      show ((imp + 24#64).toNat + 8 ≤ (dom + 232#64).toNat ∨ (dom + 232#64).toNat + 8 ≤ (imp + 24#64).toNat) ∧
        ((imp + 24#64).toNat + 8 ≤ (dom + 240#64).toNat ∨ (dom + 240#64).toNat + 8 ≤ (imp + 24#64).toNat) ∧ True
      rw [d240]
      exact ⟨by omega, by omega, trivial⟩)
    (by
      rw [logEq]
      constructor <;> simp only [OutLRange, Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;>
        exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩)).run e ⟨at_.pc, rfl⟩
  have o1 := p1.regs
  simp only [report_regs, report_loads, List.getD_cons_zero, List.getD_cons_succ, r1, r8, r9, r18, r19, dw,
    std.impureWord, std.stderrWord, GHolds] at o1
  obtain ⟨g11, g10, g12, -, -, -, g8, -, g18, -, -⟩ := o1
  have k1 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10, 11, 12, 14, 15]) : gprGet g1.σ k = gprGet e.σ k :=
    p1.gpr_frame (by decide) k lo hi out
  obtain ⟨g, run2, p2⟩ := (call_registers_summary report_call_shape report_call_decode g1
    (report_call_pins p1.image) p1.good p1.image p1.tick p1.minstret
    [(10, err), (11, 2147837040#64), (12, res), (8, 0x80064d08#64), (18, res), (2, sp + 18446744073709551568#64)]
    ⟨g10, g11, g12, g8, g18, (k1 2 (by decide) (by decide) (by decide)).trans at_.ready.stack, trivial⟩
    (by change KeysOK [10, 11, 12, 8, 18, 2]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run g1 ⟨p1.pc, rfl⟩
  have mg : g.σ.mem = writeLog e.σ.mem [((dom + 232#64).toNat, 8, active), ((dom + 240#64).toNat, 8, pos)] := by
    rw [p2.memory, p1.memory, logEq]
  have keep (a : Nat) (apart : FieldsApart dom a) : (g.σ.mem[a]?).getD 0 = (e.σ.mem[a]?).getD 0 := by
    rw [mg, writeLog_out _ _ _ (outLog a apart)]
  have low (a : Nat) (ha : a < heapStart) : FieldsApart dom a := Or.inl (by omega)
  have leafG : LeafInput 0x8000e02c#64 g :=
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
  refine ⟨g, run1.trans run2, ?_⟩
  exact
    { ready := ready_transport_framed at_.ready leafG
        ((at_.ready.library.carry p1.kept (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p2.kept
          (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide)))
        (fun pin hp => keep _ (low _ (by have := (allocator_sources pin hp).geometry.high; omega)))
        (fun i hi => keep _ (low _ (by unfold Layout.sym_Caml_state; omega)))
        (fun i hi => keep _ (low _ (by unfold Layout.sym_pool; omega)))
        (fun a ha => keep a (by
          unfold FieldsApart
          rcases allocator_payload_outside (List.mem_cons_of_mem _ member) qlo ha with h | h <;> omega))
        (gholds_lookup (n := 2) _ p2.regs rfl)
      pc := by have := p2.pc; rw [report_call_target] at this; exact this
      stream := gholds_lookup (n := 10) _ p2.regs rfl
      format := gholds_lookup (n := 11) _ p2.regs rfl
      arg := gholds_lookup (n := 12) _ p2.regs rfl
      stateReg := gholds_lookup (n := 8) _ p2.regs rfl
      msgReg := gholds_lookup (n := 18) _ p2.regs rfl
      callee := fun k lo hi => (p2.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
        ((k1 k (by omega) (by omega) (by simp; omega)).trans (at_.callee k lo hi))
      domainBlock := ⟨q, n, member, qlo, qhi, qa, aq⟩
      message := at_.message.transport fun a lo hi => keep a (msgApart a lo hi)
      activeRestored := by
        rw [mg]
        exact word_writeLog_at _ _ 0 _ _ rfl (by simp only [List.drop, OutLRange, d240]; exact ⟨Or.inl (by omega), trivial⟩)
      posRestored := by rw [mg]; exact word_writeLog_at _ _ 1 _ _ rfl trivial
      tail := at_.tail.transport fun a ha => keep a (low a (by
        unfold TailBytes Layout.sym_caml_abort_on_uncaught_exn Layout.sym_atexit at ha; omega))
      output := by
        rw [← at_.output]
        simp only [Vsa.Machine.output]
        rw [p2.output, p1.output] }

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
