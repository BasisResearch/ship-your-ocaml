import OCaml.Vm.Primitives.Named.NamedFront
import OCaml.Vm.Boot.Startup.LookupHead

/-!
# `caml_named_value`'s bucket chain walk

From a node of the bucket's chain, the walk compares the node's name with
the query (`strcmp`, the startup lookup's `compare_names`) and either stops
at the match or follows `next`; a null `next` ends the walk with `NULL`.
`ChainAt` is the chain in memory; `chainFind` its first node named like the
query.
-/

namespace OCaml.Vm.Primitives.Named.NamedValue
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim
open OCaml.Vm.Boot.Startup

/-- A bucket chain from `head`: each node is nonzero, its name (at `node + 16`)
compares with the query by `strcmp` (`NameMemory`), and its `next` word
(at `node + 8`) is readable and leads to the rest. -/
inductive ChainAt (m : Mem) (q : BitVec 64) (qs : String) : BitVec 64 → List (BitVec 64 × String) → Prop where
  | nil : ChainAt m q qs 0#64 []
  | cons {node next : BitVec 64} {key : String} {rest : List (BitVec 64 × String)} :
      node ≠ 0#64 → NameMemory q (node + 16#64) qs key m → ReadWindow (node + 8#64) 8 →
      bytesVal .ld (read8 m (node + 8#64).toNat) = next → ChainAt m q qs next rest →
      ChainAt m q qs node ((node, key) :: rest)

/-- The first node of a chain named `qs`, or `NULL`. -/
def chainFind (qs : String) : List (BitVec 64 × String) → BitVec 64
  | [] => 0#64
  | (n, k) :: rest => if qs = k then n else chainFind qs rest

/-- The registers the walk may change. -/
def walkWrites : List Nat := [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]

/-- The walk's common facts at a block boundary. -/
structure WalkState (base : Config) (q : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  link : ∃ r : BitVec 64, gprGet c.σ 1 = some r ∧ r.toNat % 4 = 0
  a0 : (gprGet c.σ 10).isSome
  query : gprGet c.σ 9 = some q
  memory : c.σ.mem = base.σ.mem
  output : c.σ.sailOutput = base.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ walkWrites → gprGet c.σ n = gprGet base.σ n
  htif : c.σ.regs.get? Register.htif_payload_writes = base.σ.regs.get? Register.htif_payload_writes

theorem WalkState.leaf {base c : Config} {q : BitVec 64} (h : WalkState base q c) :
    LeafInput (regsAt c 1) c := by
  obtain ⟨r, hr, al⟩ := h.link
  rw [regsAt_of hr]; exact ⟨h.good, h.image, h.minstret, hr, al, h.tick⟩

/-- `strcmp`'s register frame as a noise-and-writes frame. -/
theorem strcmp_gpr {before after : Config} {g : (r : Register) → Option (RegisterType r)}
    (frame : ∀ r, NotWrittenStrcmp r → after.σ.regs.get? r = g r)
    (pin : ∀ r, NotWrittenStrcmp r → before.σ.regs.get? r = g r)
    (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15]) :
    gprGet after.σ n = gprGet before.σ n := by
  apply Umoddi3.gpr_of_frame (W := [5, 6, 7, 10, 11, 12, 13, 14, 15]) (by decide) ?_ n lo hi out
  intro r hn hw
  have nw : NotWrittenStrcmp r :=
    ⟨hw 5 (by decide), hw 6 (by decide), hw 7 (by decide), hw 10 (by decide), hw 11 (by decide),
     hw 12 (by decide), hw 13 (by decide), hw 14 (by decide), hw 15 (by decide),
     hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide),
     hn _ (by decide), hn _ (by decide)⟩
  exact (frame r nw).trans (pin r nw).symm

/-- **A copy of the chain walk**: the `next` load at `nextPc` (on to `cmpPc`,
or to `miss` at `NULL`), the comparison block at `cmpPc` and its `strcmp`
call returning to `ret`, and the test there (back to `nextPc` on a
difference, on to `found` on a match). -/
structure WalkCode (call : CallInstr) (nextPc cmpPc ret found miss : BitVec 64) : Prop where
  cmp : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (cmp_input R) →
    FnSummary cmpPc (fun d => d = c)
      (WriteRegistersPost [10, 11] [] c call.pc (R 9) (cmp_regs R (cmp_loads c.σ.mem R)))
  shape : CallShape call
  decode : CallDecode call
  pins : ∀ {c : Config}, ExecutableImage c → CallPins call c
  target : call.target = 0x80042b20#64
  link : call.link = ret
  aligned : ret.toNat % 4 = 0
  differ : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (differ_input R) →
    guardB .BNE (R 10) (0#64) = true →
    FnSummary ret (fun d => d = c)
      (WriteRegistersPost [] [] c nextPc (R 10) (differ_regs R (differ_loads c.σ.mem R)))
  same : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (match_input R) →
    guardB .BNE (R 10) (0#64) = false →
    FnSummary ret (fun d => d = c)
      (WriteRegistersPost [] [] c found (R 10) (match_regs R (match_loads c.σ.mem R)))
  last : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (nextEnd_input R) →
    ReadWindow (R 8 + 8#64) 8 →
    guardB .BEQ (bytesVal .ld ((nextEnd_loads c.σ.mem R).getD 0 [])) (0#64) = true →
    FnSummary nextPc (fun d => d = c)
      (WriteRegistersPost [8] [] c miss (R 10) (nextEnd_regs R (nextEnd_loads c.σ.mem R)))
  more : ∀ (c : Config) (R : Nat → BitVec 64), LeafInput (R 1) c → GHolds c.σ (nextMore_input R) →
    ReadWindow (R 8 + 8#64) 8 →
    guardB .BEQ (bytesVal .ld ((nextMore_loads c.σ.mem R).getD 0 [])) (0#64) = false →
    FnSummary nextPc (fun d => d = c)
      (WriteRegistersPost [8] [] c cmpPc (R 10) (nextMore_regs R (nextMore_loads c.σ.mem R)))

/-- `caml_named_value`'s copy: both exits are the return block. -/
theorem walkCode :
    WalkCode cmp_call 0x80021570#64 0x80021578#64 0x80021584#64 0x80021588#64 0x80021588#64 :=
  ⟨cmp_fast, cmp_call_shape, cmp_call_decode, cmp_call_pins, cmp_call_target, by decide, by decide,
    differ_fast, match_fast, nextEnd_fast, nextMore_fast⟩

/-- After a comparison: back at `ret` with `strcmp`'s answer in `a0`. -/
structure Compared (ret : BitVec 64) (base : Config) (q node : BitVec 64) (qs key : String) (c : Config) : Prop where
  state : WalkState base q c
  pc : PCAt ret c
  node : gprGet c.σ 8 = some node
  result : ∃ x : BitVec 64, gprGet c.σ 10 = some x ∧ (x = 0#64 ↔ qs = key)

/-- **One comparison** of the node's name with the query. -/
theorem walk_compare {call : CallInstr} {nextPc cmpPc ret found miss : BitVec 64}
    (code : WalkCode call nextPc cmpPc ret found miss) {base c : Config} {q node : BitVec 64} {qs key : String}
    (h : WalkState base q c) (pc : PCAt cmpPc c) (at8 : gprGet c.σ 8 = some node)
    (names : NameMemory q (node + 16#64) qs key c.σ.mem) :
    ∃ d, Steps c d ∧ Compared ret base q node qs key d := by
  have r8 := regsAt_of at8
  have r9 := regsAt_of h.query
  have regs : GHolds c.σ (cmp_input (regsAt c)) := by
    simp only [cmp_input, GHolds]
    obtain ⟨r, hr, -⟩ := h.link
    exact ⟨gpr_some (by rw [hr]; rfl), gpr_some (by rw [at8]; rfl), gpr_some (by rw [h.query]; rfl),
      gpr_some h.a0, trivial⟩
  obtain ⟨c1, run1, p1⟩ := (code.cmp c (regsAt c) h.leaf regs).run c ⟨pc, rfl⟩
  have args : GHolds c1.σ [(10, q), (11, node + 16#64), (8, node), (9, q)] := by
    apply holds_project p1.regs
    simp [cmp_regs, cmp_loads, lookupG, r8, r9]
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary code.shape code.decode c1 (code.pins p1.image)
    p1.good p1.image p1.tick p1.minstret _ args (by change KeysOK [10, 11, 8, 9]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl).run c1 ⟨p1.pc, rfl⟩
  have m2 : c2.σ.mem = c.σ.mem := by rw [p2.memory, p1.memory, wl_nil]
  have pre : StrcmpEntryCond (fun r => c2.σ.regs.get? r) q (node + 16#64) ret qs key
      c2.σ.mem c2.σ.sailOutput c2 :=
    { good := p2.good, loaded := by rw [m2]; exact names.code, mem := rfl, out := rfl
      pc := by have := p2.pc; rw [code.target] at this; exact this
      a0 := gholds_lookup (n := 10) _ p2.regs rfl
      a1 := gholds_lookup (n := 11) _ p2.regs rfl
      ra := gholds_lookup (n := 1) _ p2.regs (by simp [lookupG, code.link])
      minstret := p2.minstret, tick := p2.tick, ralign := code.aligned
      cstra := by rw [m2]; exact names.left
      cstrb := by rw [m2]; exact names.right
      maskpin := by rw [m2]; exact names.mask
      wrega := by rw [m2]; exact names.leftWindow
      wregb := by rw [m2]; exact names.rightWindow
      frame := fun _ _ => rfl }
  obtain ⟨d, run3, post⟩ := compare_names _ q (node + 16#64) ret qs key _ _ c2 pre
  have md : d.σ.mem = c.σ.mem := post.mem.trans m2
  have keepS := strcmp_gpr (before := c2) post.frame (fun _ _ => rfl)
  obtain ⟨x, hx, iff⟩ := post.result
  refine ⟨d, run1.trans (run2.trans run3), ⟨?_, post.pc, ?_, ⟨x, hx, iff⟩⟩⟩
  · exact
      { good := post.good
        image := ⟨by simpa only [md] using h.image.text, by simpa only [md] using h.image.rodata, by simpa only [md] using h.image.impure⟩
        minstret := post.good.minstret, tick := post.tick
        link := ⟨_, post.ra, code.aligned⟩
        a0 := by change (d.σ.regs.get? Register.x10).isSome; rw [hx]; rfl
        query := (keepS 9 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 9) _ p2.regs rfl)
        memory := md.trans h.memory
        output := by rw [post.out, p2.output, p1.output, h.output]
        frame := fun n lo hi out => by
          simp only [walkWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
          exact (keepS n lo hi (by simp; omega)).trans
            ((p2.gpr_frame (by decide) n lo hi (by simp; omega)).trans
            ((p1.gpr_frame (by decide) n lo hi (by simp; omega)).trans (h.frame n lo hi (by
              simp [walkWrites]; omega))))
        htif := by
          rw [post.frame _ (by decide), p2.frame _ (by decide) (by decide), p1.frame _ (by decide) (by decide)]
          exact h.htif }
  · exact (keepS 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ p2.regs rfl)

/-- A read-only walk block keeps the walk state. -/
theorem WalkState.after_block {base c d : Config} {q pc v : BitVec 64} {writes : List Nat} {regs : GRegs}
    (h : WalkState base q c) (p : WriteRegistersPost writes [] c pc v regs d) (keys : KeysOK writes)
    (sub : ∀ n ∈ writes, n ∈ walkWrites) (no1 : 1 ∉ writes) (no9 : 9 ∉ writes)
    (a0 : (gprGet d.σ 10).isSome) : WalkState base q d :=
  { good := p.good, image := p.image, minstret := p.minstret, tick := p.tick
    link := by
      obtain ⟨r, hr, al⟩ := h.link
      exact ⟨r, (p.gpr_frame keys 1 (by decide) (by decide) no1).trans hr, al⟩
    a0 := a0
    query := (p.gpr_frame keys 9 (by decide) (by decide) no9).trans h.query
    memory := by rw [p.memory, wl_nil, h.memory]
    output := p.output.trans h.output
    frame := fun n lo hi out =>
      (p.gpr_frame keys n lo hi (fun m => out (sub n m))).trans (h.frame n lo hi out)
    htif := (p.frame _ (fun n _ => gprReg_ne_htif n) (by decide)).trans h.htif }

/-- The walk has stopped with its answer in `s0`: at `found` on a match, at
`miss` at the chain's end. -/
structure WalkDone (found miss : BitVec 64) (base : Config) (q result : BitVec 64) (c : Config) : Prop where
  state : WalkState base q c
  pc : PCAt (if result = 0#64 then miss else found) c
  result : gprGet c.σ 8 = some result

/-- **The chain walk**, from a nonnull node to the first match or `NULL`. -/
theorem walk {call : CallInstr} {nextPc cmpPc ret found miss : BitVec 64}
    (code : WalkCode call nextPc cmpPc ret found miss) {base : Config} {q : BitVec 64} {qs : String} :
    ∀ (l : List (BitVec 64 × String)) (node : BitVec 64) (c : Config),
      ChainAt base.σ.mem q qs node l → node ≠ 0#64 → WalkState base q c → PCAt cmpPc c →
      gprGet c.σ 8 = some node → ∃ d, Steps c d ∧ WalkDone found miss base q (chainFind qs l) d := by
  intro l
  induction l with
  | nil => intro node c ch nz; cases ch; exact absurd rfl nz
  | cons e rest ih =>
    intro node c ch nz h pc at8
    cases ch with
    | @cons _ nxt key _ _ names window nextVal tail =>
    obtain ⟨c1, run1, p1⟩ := walk_compare code h pc at8 (by rw [h.memory]; exact names)
    obtain ⟨x, hx, iff⟩ := p1.result
    have r10 := regsAt_of hx
    have regs10 : GHolds c1.σ [(10, regsAt c1 10)] := ⟨by rw [r10]; exact hx, trivial⟩
    by_cases same : qs = key
    · have zero : x = 0#64 := iff.mpr same
      obtain ⟨c2, run2, p2⟩ := (code.same c1 (regsAt c1) p1.state.leaf regs10
        (by rw [r10, zero]; decide)).run c1 ⟨p1.pc, rfl⟩
      refine ⟨c2, run1.trans run2, ⟨p1.state.after_block p2 (by decide) (by decide) (by decide) (by decide)
        (gpr_some_of ((p2.gpr_frame (by decide) 10 (by decide) (by decide) (by simp)).trans hx)), ?_, ?_⟩⟩
      · simp only [chainFind, same, ite_true, nz, ite_false]; exact p2.pc
      simp only [chainFind, same, ite_true]
      exact (p2.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans p1.node
    · have nz0 : x ≠ 0#64 := fun z => same (iff.mp z)
      obtain ⟨c2, run2, p2⟩ := (code.differ c1 (regsAt c1) p1.state.leaf regs10
        (by rw [r10]; simp [guardB, nz0])).run c1 ⟨p1.pc, rfl⟩
      have s2 := p1.state.after_block p2 (by decide) (by decide) (by decide) (by decide)
        (gpr_some_of ((p2.gpr_frame (by decide) 10 (by decide) (by decide) (by simp)).trans hx))
      have at8' : gprGet c2.σ 8 = some node :=
        (p2.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans p1.node
      have r8 := regsAt_of at8'
      have regs2 : GHolds c2.σ [(8, regsAt c2 8), (10, regsAt c2 10)] :=
        ⟨by rw [r8]; exact at8', gpr_some s2.a0, trivial⟩
      have word : bytesVal .ld (read8 c2.σ.mem (regsAt c2 8 + 8#64).toNat) = nxt := by
        rw [r8, s2.memory]; exact nextVal
      have find : chainFind qs ((node, key) :: rest) = chainFind qs rest := by
        simp only [chainFind, same, ite_false]
      by_cases last : nxt = 0#64
      · obtain ⟨c3, run3, p3⟩ := (code.last c2 (regsAt c2) s2.leaf regs2 (by rw [r8]; exact window)
          (by simp only [nextEnd_loads, List.getD_cons_zero, word, last]; decide)).run c2 ⟨p2.pc, rfl⟩
        have o3 := p3.regs
        simp only [nextEnd_regs, nextEnd_loads, List.getD_cons_zero, word, last, GHolds] at o3
        refine ⟨c3, run1.trans (run2.trans run3), ⟨s2.after_block p3 (by decide) (by decide) (by decide)
          (by decide) (gpr_some_of o3.2.1), ?_, ?_⟩⟩
        · rw [find]; subst last; cases tail
          · rw [show chainFind qs ([] : List (BitVec 64 × String)) = 0#64 from rfl, if_pos rfl]; exact p3.pc
          · exact absurd rfl (by assumption : (0#64 : BitVec 64) ≠ 0#64)
        rw [find]
        subst last
        cases tail
        · exact o3.1
        · exact absurd rfl (by assumption : (0#64 : BitVec 64) ≠ 0#64)
      · obtain ⟨c3, run3, p3⟩ := (code.more c2 (regsAt c2) s2.leaf regs2 (by rw [r8]; exact window)
          (by simp only [nextMore_loads, List.getD_cons_zero, word]; simp [guardB, last])).run c2
          ⟨p2.pc, rfl⟩
        have o3 := p3.regs
        simp only [nextMore_regs, nextMore_loads, List.getD_cons_zero, word, GHolds] at o3
        have s3 := s2.after_block p3 (by decide) (by decide) (by decide) (by decide) (gpr_some_of o3.2.1)
        obtain ⟨d, run4, done⟩ := ih nxt c3 tail last s3 p3.pc o3.1
        exact ⟨d, run1.trans (run2.trans (run3.trans run4)), by rw [find]; exact done⟩

end OCaml.Vm.Primitives.Named.NamedValue
