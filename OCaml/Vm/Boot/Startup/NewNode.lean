import OCaml.Vm.Boot.Startup.NewNodeSteps
import OCaml.Vm.Boot.Startup.MallocReady
import OCaml.Vm.Boot.Startup.MemcpyFresh
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.NativeNested
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  VsaIris.Memcpy OCaml.Vm.Primitives

/-- Where the name `new_node` copies lies: above the arena, below the callee's frames. -/
structure NewNodeName (sp name : BitVec 64) (k : Nat) : Prop where
  low : heapEnd ≤ name.toNat
  high : name.toNat + k ≤ nativeFrameBase sp (64 + allocHeadroom)

theorem NewNodeName.htif {sp name k} (h : NewNodeName sp name k) :
    name.toNat + k ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 16 ≤ name.toNat :=
  Or.inr (by have := h.low; unfold heapEnd Layout.sym_tohost at *; omega)

theorem NewNodeName.ram {sp name k} (h : NewNodeName sp name k) : 0x80000000 ≤ name.toNat := by
  have := h.low; unfold heapEnd at this; omega

theorem byte_writeLog_last (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry) (A : Nat) (dv : BitVec 64)
    (out : OutL log2 A) : ((writeLog m (log1 ++ (A, 1, dv) :: log2))[A]?).getD 0 = sbData dv := by
  rw [pin1_of_writeLog m log1 log2 A dv out]; rfl

theorem word_writeLog_last (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry) (A : Nat) (v : BitVec 64)
    (out : OutLRange log2 A 8) : bytesT (writeLog m (log1 ++ (A, 8, v) :: log2)) A 8 = v := by
  rw [writeLog_append]
  show bytesT (writeLog (writeLog (writeLog m log1) [(A, 8, v)]) log2) A 8 = v
  rw [bytesT_writeLog_out _ out, word_writeLog]

theorem log_split {l : List WEntry} {i : Nat} {e : WEntry} (hi : l[i]? = some e) :
    l = l.take i ++ e :: l.drop (i + 1) := by
  obtain ⟨lt, get⟩ := List.getElem?_eq_some_iff.mp hi
  conv => lhs; rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons lt, get]

theorem byte_writeLog_at (m : Std.ExtHashMap Nat (BitVec 8)) (l : List WEntry) (i A : Nat) (dv : BitVec 64)
    (hi : l[i]? = some (A, 1, dv)) (out : OutL (l.drop (i + 1)) A) :
    ((writeLog m l)[A]?).getD 0 = sbData dv := by
  rw [log_split hi]
  exact byte_writeLog_last m _ _ A dv out

theorem word_writeLog_at (m : Std.ExtHashMap Nat (BitVec 8)) (l : List WEntry) (i A : Nat) (v : BitVec 64)
    (hi : l[i]? = some (A, 8, v)) (out : OutLRange (l.drop (i + 1)) A 8) :
    bytesT (writeLog m l) A 8 = v := by
  rw [log_split hi]
  exact word_writeLog_last m _ _ A v out

/-- Bytes `new_node` never writes. -/
structure NewNodeKept (H : List (Nat × Nat)) (sp node : BitVec 64) (k : Nat) (x : Nat) : Prop where
  stack : x < nativeFrameBase sp (64 + allocHeadroom) ∨ sp.toNat ≤ x
  foot : ¬ vsaFoot H x
  slot : x < slotOne ∨ slotOne + 56 ≤ x
  block : ¬ InExt (node.toNat, k + 1) x

/-- `new_node(d, name, k, dir)` returning node 1. -/
structure NewNodeDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 d name k dir : BitVec 64)
    (before after : Config) where
  node : BitVec 64
  pc : PCAt ra after
  result : gprGet after.σ 10 = some 1#64
  regs : GHolds after.σ [(2, sp), (8, s0), (9, s1), (18, s2), (19, s3)]
  ready : RuntimeReady ((node.toNat, k.toNat + 1) :: H) capacity sp ra after
  fresh : heapStart ≤ node.toNat ∧ node.toNat + (k.toNat + 1) ≤ heapEnd
  disjoint : ∀ e ∈ H, ∀ a, InExt (node.toNat, k.toNat + 1) a → ¬ InExt e a
  copied : ∀ j, j < k.toNat → (after.σ.mem[node.toNat + j]?).getD 0 = (before.σ.mem[name.toNat + j]?).getD 0
  terminated : (after.σ.mem[node.toNat + k.toNat]?).getD 0 = 0#8
  used : (after.σ.mem[slotOne]?).getD 0 = 1#8
  dirByte : (after.σ.mem[slotOne + 1]?).getD 0 = sbData dir
  linked : (after.σ.mem[slotOne + 2]?).getD 0 = 1#8
  parent : Pin4 after.σ.mem (slotOne + 4) (swData d)
  namePtr : bytesT after.σ.mem (slotOne + 8) 8 = node
  length : bytesT after.σ.mem (slotOne + 16) 8 = k
  zeros : ∀ off ∈ [24, 32, 40, 48], bytesT after.σ.mem (slotOne + off) 8 = 0#64
  kept : ∀ x, NewNodeKept H sp node k.toNat x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0

/-- The allocator's read-only bytes lie below htif.c's `files` table. -/
theorem allocator_pin_below_files {pin : Nat × BitVec 8} (hp : pin ∈ allocText) : pin.1 < slotOne := by
  have source := allocator_sources pin hp
  unfold AllocatorByteSource at source
  split at source <;> simp only [Image.textBase, Image.textSize, allocatorImpureAddr, slotOne, Layout.sym_files] at * <;>
    omega

theorem new_node_slot1 (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 s3 d name k dir : BitVec 64)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp (64 + allocHeadroom))
    (regs : GHolds c.σ (newNodeInput sp ra s0 d name k dir ++ [(9, s1), (18, s2), (19, s3)]))
    (free : (c.σ.mem[slotOne]?).getD 0 = 0#8) (nameAt : NewNodeName sp name k.toNat)
    (small : k.toNat + 1 < 2 ^ 32) (charged : vsaChg (k.toNat + 1) charge) :
    FnSummary 0x800000f0#64 (fun e => e = c)
      (fun after => Nonempty (NewNodeDone H capacity sp ra s0 s1 s2 s3 d name k dir c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame64 := frame.resize (small := 64) (by decide) (by decide)
  have inner : NativeFrame (nativeStack sp 64) allocHeadroom := frame.nested (front := 64) (by decide)
  have baseNat := frame64.stack_nat
  have lower := frame.lower
  -- save ra and s0; slot 1 is free
  obtain ⟨a, run1, saved⟩ := (new_node_save c sp ra s0 d name k dir ready.toLeafInput frame64
    ⟨ready.stack, gholds_lookup (n := 8) _ regs (by rfl), ready.raReg, gholds_lookup (n := 10) _ regs (by rfl),
      gholds_lookup (n := 11) _ regs (by rfl), gholds_lookup (n := 12) _ regs (by rfl),
      gholds_lookup (n := 13) _ regs (by rfl), trivial⟩).run c ⟨pc, rfl⟩
  have readyA := ready.stack_log saved (by decide) (by simp only [newNodeSaved, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ saved.regs (by rfl)) (gholds_lookup (n := 1) _ saved.regs (by rfl)) ready.aligned
    frame64 (newNodeLog_inside frame64)
  have slotA : (a.σ.mem[slotOne]?).getD 0 = 0#8 := by
    rw [saved.memory, frameOn_writeLog _ _ _ (newNodeLog_inside frame64) _ ⟨Or.inl (by
      show slotOne < nativeFrameBase sp 64
      unfold slotOne Layout.sym_files nativeFrameBase heapEnd allocHeadroom at *
      omega), trivial⟩]
    exact free
  obtain ⟨b, run2, found⟩ := (new_node_free a sp ra d name k dir readyA.toLeafInput saved.regs slotA).run a
    ⟨saved.pc, rfl⟩
  have readyB := readyA.stack_log found (by decide) (by simp only [newNodeFound, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ found.regs (by rfl)) (gholds_lookup (n := 1) _ found.regs (by rfl)) ready.aligned
    frame64 (by simp only [LogInW])
  -- save s1–s3 and the name; malloc(k + 1)
  have keepB (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [14, 15] ∧ n ∉ [2, 15, 8, 16])
      (hv : gprGet c.σ n = some v) : gprGet b.σ n = some v :=
    (found.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans
      ((saved.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2).trans hv)
  obtain ⟨m0, run3, call⟩ := (new_node_alloc_call b sp d name k dir s1 s2 s3 _ readyB.toLeafInput frame64
    ⟨gholds_lookup (n := 15) _ found.regs (by rfl), gholds_lookup (n := 14) _ found.regs (by rfl),
      gholds_lookup (n := 16) _ found.regs (by rfl), gholds_lookup (n := 8) _ found.regs (by rfl),
      gholds_lookup (n := 2) _ found.regs (by rfl), gholds_lookup (n := 10) _ found.regs (by rfl),
      gholds_lookup (n := 11) _ found.regs (by rfl), gholds_lookup (n := 12) _ found.regs (by rfl),
      gholds_lookup (n := 13) _ found.regs (by rfl),
      keepB 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ regs (by rfl)),
      keepB 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ regs (by rfl)),
      keepB 19 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ regs (by rfl)), trivial⟩).run b
    ⟨found.pc, rfl⟩
  have readyM := readyB.stack_log call (by decide) (by simp only [newNodeAllocated, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ call.regs (by rfl)) (gholds_lookup (n := 1) _ call.regs (by rfl)) (by decide)
    frame64 (newNodeAllocLog_inside frame64)
  have request : (k + 1#64).toNat = k.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨m, run4, ⟨M⟩⟩ := (malloc_ready m0 H capacity charge (k + 1#64) (nativeStack sp 64)
    jal_80000144_call.link readyM inner (gholds_lookup (n := 10) _ call.regs (by rfl))
    (by rw [request]; exact charged)).run m0 ⟨call.pc, rfl⟩
  obtain ⟨pNonzero, pLow, pHigh, pDisjoint⟩ := M.fresh
  rw [request] at pHigh pDisjoint
  have readyP := M.ready
  rw [request] at readyP
  have slotWord (off : Nat) (value : BitVec 64) (member : (off, value) ∈ newNodeAllocSlots s1 s2 s3 name) :
      bytesT m0.σ.mem (nativeFrameBase sp 64 + off) 8 = value := by
    rw [call.memory]
    apply frame64.word_log_read
    · intro k v hk
      simp only [newNodeAllocSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp [newNodeAllocSlots]
    · exact member
  have callerM (x : Nat) (above : nativeFrameBase sp 64 ≤ x) : (m.σ.mem[x]?).getD 0 = (m0.σ.mem[x]?).getD 0 :=
    M.caller_byte inner (by rw [baseNat]; exact above)
  have nameM : bytesT m.σ.mem (nativeFrameBase sp 64 + 8) 8 = name := by
    rw [word_observed (m := m0.σ.mem) _ (fun i _ => callerM _ (by omega))]
    exact slotWord 8 name (by simp [newNodeAllocSlots])
  have kM : gprGet m.σ 9 = some k :=
    (M.saved_gpr readyM.platform (by decide)).trans (gholds_lookup (n := 9) _ call.regs (by rfl))
  obtain ⟨x, run5, copy⟩ := (new_node_copy_call m sp (vsaReg m 10) name k _ M.ready.toLeafInput frame64
    ⟨M.result, M.ready.stack, kM, trivial⟩ (fun h => pNonzero (by rw [h]; rfl)) nameM).run m ⟨M.pc, rfl⟩
  have readyX := readyP.stack_log copy (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ copy.regs (by rfl)) (gholds_lookup (n := 1) _ copy.regs (by rfl)) (by decide)
    frame64 (frame64.word_log_inside (slots := [(8, vsaReg m 10)]) (fun off value member => by simp at member; omega))
  -- memcpy(p, name, k)
  have apart (j : Nat) (hj : j < k.toNat) : ¬ InExt ((vsaReg m 10).toNat, k.toNat) (name.toNat + j) := by
    intro inside
    unfold InExt at inside
    have := nameAt.low
    omega
  have length : gprGet x.σ 12 = some (BitVec.ofNat 64 k.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact gholds_lookup (n := 12) _ copy.regs (by rfl)
  have sourceHigh : name.toNat + k.toNat ≤ 0x100000000 := by
    have top := frame.upper
    have := nameAt.high
    unfold nativeFrameBase Layout.sym_stack_top at *; omega
  obtain ⟨y, run6, Y⟩ := (memcpy_fresh x _ capacity (nativeStack sp 64) jal_80000158_call.link (vsaReg m 10) name
    k.toNat (k.toNat + 1) readyX (List.mem_cons_self ..) (by omega)
    ⟨gholds_lookup (n := 10) _ copy.regs (by rfl), gholds_lookup (n := 11) _ copy.regs (by rfl), length, trivial⟩
    apart nameAt.ram sourceHigh nameAt.htif).run x ⟨copy.pc, rfl⟩
  -- initialize slot 1 and the name's terminator
  have reg (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (member : n ∈ vsaSaved)
      (copyOut : n ∉ [11, 12] ++ [1]) (memOut : n ∉ mRegs) (hv : gprGet m0.σ n = some v) : gprGet y.σ n = some v :=
    (Y.registers n lower upper memOut).trans ((copy.toEffectPost.gpr_frame (by decide) n lower upper copyOut).trans
      ((M.saved_gpr readyM.platform member).trans hv))
  have pNat : ((vsaReg m 10) + k).toNat = (vsaReg m 10).toNat + k.toNat := by
    rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    unfold heapEnd at pHigh
    omega
  have pY : bytesT y.σ.mem (nativeFrameBase sp 64 + 8) 8 = vsaReg m 10 := by
    rw [word_observed (m := x.σ.mem) _ (fun i _ => Y.kept _ (fun inside => by
      unfold InExt at inside; unfold nativeFrameBase heapEnd allocHeadroom at *; omega)), copy.memory]
    exact frame64.word_log_read (slots := [(8, vsaReg m 10)]) (by simp) (by simp) _ (by simp)
  obtain ⟨z, run7, init⟩ := (new_node_init y sp (vsaReg m 10) k d dir _ Y.ready.toLeafInput frame64
    ⟨reg 8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ call.regs (by rfl)),
      Y.ready.stack,
      reg 9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ call.regs (by rfl)),
      reg 18 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ call.regs (by rfl)),
      reg 19 _ (by decide) (by decide) (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ call.regs (by rfl)),
      Y.result, trivial⟩ pY (by rw [pNat]; exact ⟨by omega, by omega⟩)).run y ⟨Y.pc, rfl⟩
  have windows : LogInW [⟨slotOne, slotOne + 56⟩, ⟨((vsaReg m 10) + k).toNat, ((vsaReg m 10) + k).toNat + 1⟩]
      (newNodeInitLog (vsaReg m 10) k d dir) := by
    simp only [newNodeInitLog, LogInW, InsideW]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> simp
  have pkLow : heapStart ≤ ((vsaReg m 10) + k).toNat := by rw [pNat]; omega
  have filesLow : slotOne + 56 ≤ heapStart := by decide
  have readyZ := Y.ready.window_log init (by decide) (by simp only [newNodeInitRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ init.regs (by rfl))
    ((init.frame .x1 (by decide) (by decide)).trans Y.ready.raReg) (by decide) windows
    (fun pin hp => by
      have := allocator_pin_below_files hp
      exact ⟨Or.inl this, Or.inl (by dsimp only; omega), trivial⟩)
    (by
      have : Layout.sym_Caml_state + 8 ≤ slotOne := by decide
      exact ⟨Or.inl (by dsimp only; omega), Or.inl (by dsimp only; omega), trivial⟩)
    (by
      have : Layout.sym_pool + 8 ≤ slotOne := by decide
      exact ⟨Or.inl (by dsimp only; omega), Or.inl (by dsimp only; omega), trivial⟩)
    (fun a owned => by
      rcases owned with global | ⟨lo, hi, apartAll⟩
      · unfold allocGlobal InRange at global
        have below : a < heapStart := by unfold heapStart; omega
        have slotBelow : a < slotOne ∨ slotOne + 56 ≤ a := by unfold slotOne Layout.sym_files; omega
        exact ⟨slotBelow, Or.inl (by dsimp only; omega), trivial⟩
      · refine ⟨Or.inr (by dsimp only; omega), ?_, trivial⟩
        dsimp only
        rcases Nat.lt_or_ge a ((vsaReg m 10) + k).toNat with h | h
        · exact Or.inl h
        · rcases Nat.lt_or_ge a (((vsaReg m 10) + k).toNat + 1) with g | g
          · exact absurd ⟨by rw [pNat] at h; omega, by rw [pNat] at g; omega⟩
              (apartAll _ (List.mem_cons_self ..))
          · exact Or.inr g)
  -- the saved words, from both save logs through every later effect
  have savedM0 (off : Nat) (value : BitVec 64)
      (member : (off, value) ∈ [(56, ra), (48, s0), (40, s1), (32, s2), (24, s3)]) :
      bytesT m0.σ.mem (nativeFrameBase sp 64 + off) 8 = value := by
    rw [call.memory, show b.σ.mem = a.σ.mem from found.memory, saved.memory, ← writeLog_append, newNodeLog,
      newNodeAllocLog, nativeWordLog, nativeWordLog, ← List.map_append, ← nativeWordLog]
    apply frame64.word_log_read (slots := newNodeSlots ra s0 ++ newNodeAllocSlots s1 s2 s3 name)
    · intro k v hk
      simp only [newNodeSlots, newNodeAllocSlots, List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false] at hk
      omega
    · simp [newNodeSlots, newNodeAllocSlots]
    · have sub : ∀ e ∈ [(56, ra), (48, s0), (40, s1), (32, s2), (24, s3)],
          e ∈ newNodeSlots ra s0 ++ newNodeAllocSlots s1 s2 s3 name := by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [newNodeSlots, newNodeAllocSlots]
      exact sub _ member
  have keepZ (x : Nat) (lo : nativeFrameBase sp 64 + 16 ≤ x) (hi : x < sp.toNat) :
      (z.σ.mem[x]?).getD 0 = (m0.σ.mem[x]?).getD 0 := by
    have slot8 : (nativeStack sp 64 + BitVec.ofNat 64 8).toNat = nativeFrameBase sp 64 + 8 := by
      rw [nativeStack, frame64.address 8 (by decide), frame64.slot_nat (off := 8) (by decide)]
    rw [init.memory, writeLog_out _ _ _ ?_, Y.kept _ (fun inside => by
        unfold InExt at inside; unfold nativeFrameBase heapEnd allocHeadroom at *; omega),
      copy.memory, writeLog_out _ _ _ (show OutL (newNodeCopyLog sp (vsaReg m 10)) x from by
        simp only [newNodeCopyLog, nativeWordLog, List.map, OutL]
        exact ⟨Or.inr (by rw [slot8]; omega), trivial⟩), callerM _ (by omega)]
    have heapHigh : (vsaReg m 10 + k).toNat + 1 ≤ nativeFrameBase sp 64 := by
      rw [pNat]; unfold nativeFrameBase heapEnd allocHeadroom at *; omega
    simp only [newNodeInitLog, OutL, slotOne, Layout.sym_files]
    unfold nativeFrameBase heapEnd allocHeadroom at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
  obtain ⟨done, run8, returned⟩ := (new_node_return z sp ra s0 s1 s2 s3 1#64 _ readyZ.toLeafInput frame64
    ⟨gholds_lookup (n := 2) _ init.regs (by rfl), gholds_lookup (n := 8) _ init.regs (by rfl), trivial⟩
    (fun off value member => by
      have range : 24 ≤ off ∧ off + 8 ≤ 64 := by
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        omega
      rw [word_observed (m := m0.σ.mem) _ (fun i _ => keepZ _ (by omega) (by
        have := frame64.lower; unfold nativeFrameBase at *; omega))]
      exact savedM0 off value member) ready.aligned).run z ⟨init.pc, rfl⟩
  have readyDone := readyZ.stack_log returned (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ returned.regs (by rfl)) (gholds_lookup (n := 1) _ returned.regs (by rfl))
    ready.aligned frame64 (by simp only [LogInW])
  have memDone : done.σ.mem = writeLog y.σ.mem (newNodeInitLog (vsaReg m 10) k d dir) :=
    (show done.σ.mem = z.σ.mem from returned.memory).trans init.memory
  have pk := pNat
  have slotHigh : slotOne + 56 ≤ heapStart := by decide
  have keepAll (q : Nat) (h : NewNodeKept H sp (vsaReg m 10) k.toNat q) :
      (done.σ.mem[q]?).getD 0 = (c.σ.mem[q]?).getD 0 := by
    have stackOut : q < nativeFrameBase sp 64 ∨ sp.toNat ≤ q := by
      rcases h.stack with l | r
      · left; unfold nativeFrameBase at *; omega
      · exact Or.inr r
    have blk := h.block
    unfold InExt at blk
    have e1 : (done.σ.mem[q]?).getD 0 = (y.σ.mem[q]?).getD 0 := by
      rw [memDone, frameOn_writeLog _ _ _ windows q ⟨h.slot, by dsimp only; rw [pNat]; omega, trivial⟩]
    have e2 : (y.σ.mem[q]?).getD 0 = (x.σ.mem[q]?).getD 0 :=
      Y.kept q (fun inside => by unfold InExt at inside; omega)
    have e3 : (x.σ.mem[q]?).getD 0 = (m.σ.mem[q]?).getD 0 := by
      rw [copy.memory, newNodeCopyLog, frameOn_writeLog _ _ _ (frame64.word_log_inside (slots := [(8, vsaReg m 10)])
        (fun off value member => by simp at member; omega)) q ⟨stackOut, trivial⟩]
    have e4 : (m.σ.mem[q]?).getD 0 = (m0.σ.mem[q]?).getD 0 := by
      have unowned : ¬ mS H (nativeStack sp 64) q := by
        rintro (scratch | heap)
        · unfold stackWin InExt at scratch
          rw [baseNat] at scratch
          rcases h.stack with l | r
          · unfold nativeFrameBase at *; omega
          · unfold nativeFrameBase at *; omega
        · exact h.foot heap
      exact M.allocation.memory q unowned
    have e5 : (m0.σ.mem[q]?).getD 0 = (c.σ.mem[q]?).getD 0 := by
      rw [call.memory, frameOn_writeLog _ _ _ (newNodeAllocLog_inside frame64) q ⟨stackOut, trivial⟩,
        show b.σ.mem = a.σ.mem from found.memory, saved.memory,
        frameOn_writeLog _ _ _ (newNodeLog_inside frame64) q ⟨stackOut, trivial⟩]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have nameKept (j : Nat) (hj : j < k.toNat) : NewNodeKept H sp (vsaReg m 10) k.toNat (name.toNat + j) := by
    have lo := nameAt.low
    have hi := nameAt.high
    refine ⟨Or.inl (by omega), fun foot => ?_, Or.inr (by unfold heapEnd slotOne Layout.sym_files at *; omega),
      fun inside => by unfold InExt at inside; omega⟩
    have := allocator_foot_below foot
    omega
  have initOut (q : Nat) (slot : q < slotOne ∨ slotOne + 56 ≤ q) (byte : q ≠ (vsaReg m 10 + k).toNat) :
      (done.σ.mem[q]?).getD 0 = (y.σ.mem[q]?).getD 0 := by
    rw [memDone, frameOn_writeLog _ _ _ windows q ⟨slot, by dsimp only; omega, trivial⟩]
  have doneLog (q : Nat) : (done.σ.mem[q]?).getD 0 = ((writeLog y.σ.mem (newNodeInitLog (vsaReg m 10) k d dir))[q]?).getD 0 := by
    rw [memDone]
  have doneWord (q : Nat) : bytesT done.σ.mem q 8 = bytesT (writeLog y.σ.mem (newNodeInitLog (vsaReg m 10) k d dir)) q 8 := by
    rw [memDone]
  have heapByte : slotOne + 56 ≤ (vsaReg m 10 + k).toNat := by rw [pNat]; omega
  refine ⟨done, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))),
    ⟨{ node := vsaReg m 10
       pc := returned.pc
       result := gholds_lookup (n := 10) _ returned.regs (by rfl)
       regs := ⟨gholds_lookup (n := 2) _ returned.regs (by rfl), gholds_lookup (n := 8) _ returned.regs (by rfl),
         gholds_lookup (n := 9) _ returned.regs (by rfl), gholds_lookup (n := 18) _ returned.regs (by rfl),
         gholds_lookup (n := 19) _ returned.regs (by rfl), trivial⟩
       ready := readyDone
       fresh := ⟨pLow, pHigh⟩
       disjoint := pDisjoint
       copied := fun j hj => ?_
       terminated := ?_
       used := ?_
       dirByte := ?_
       linked := ?_
       parent := ?_
       namePtr := ?_
       length := ?_
       zeros := ?_
       kept := keepAll }⟩⟩
  · have inBlock : ¬ InExt ((vsaReg m 10).toNat, k.toNat) (name.toNat + j) := apart j hj
    have lo := nameAt.low
    have nameSlot : slotOne + 56 ≤ name.toNat + j := by
      have : slotOne + 56 ≤ heapEnd := by decide
      omega
    have nameByte : name.toNat + j ≠ (vsaReg m 10 + k).toNat := by rw [pNat]; omega
    have xName : (x.σ.mem[name.toNat + j]?).getD 0 = (c.σ.mem[name.toNat + j]?).getD 0 :=
      (Y.kept _ inBlock).symm.trans ((initOut _ (Or.inr nameSlot) nameByte).symm.trans
        (keepAll _ (nameKept j hj)))
    have blockSlot : slotOne + 56 ≤ (vsaReg m 10).toNat + j := by omega
    have blockByte : (vsaReg m 10).toNat + j ≠ (vsaReg m 10 + k).toNat := by rw [pNat]; omega
    rw [initOut _ (Or.inr blockSlot) blockByte, Y.bytes j hj]
    exact xName
  · rw [← pNat, doneLog]
    refine (byte_writeLog_at _ _ 9 _ _ rfl ?_).trans (by decide)
    simp only [newNodeInitLog, List.drop, OutL]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  · rw [doneLog]
    refine (byte_writeLog_at _ _ 10 _ _ rfl ?_).trans (by decide)
    simp only [newNodeInitLog, List.drop, OutL]
    refine ⟨?_, trivial⟩; omega
  · rw [doneLog]
    refine byte_writeLog_at _ _ 1 _ _ rfl ?_
    simp only [newNodeInitLog, List.drop, OutL]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
  · rw [doneLog]
    refine (byte_writeLog_at _ _ 11 _ _ rfl ?_).trans (by decide)
    simp only [newNodeInitLog, List.drop, OutL]
  · rw [memDone, log_split (l := newNodeInitLog (vsaReg m 10) k d dir) (i := 6) (e := (slotOne + 4, 4, d)) rfl]
    apply pin4_of_writeLog
    simp only [newNodeInitLog, List.drop, OutLRange]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
  · rw [doneWord]
    refine word_writeLog_at _ _ 7 _ _ rfl ?_
    simp only [newNodeInitLog, List.drop, OutLRange]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> omega
  · rw [doneWord]
    refine word_writeLog_at _ _ 8 _ _ rfl ?_
    simp only [newNodeInitLog, List.drop, OutLRange]
    refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
  · intro off member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [doneWord]
    rcases member with rfl | rfl | rfl | rfl
    · refine word_writeLog_at _ _ 2 _ _ rfl ?_
      simp only [newNodeInitLog, List.drop, OutLRange]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
    · refine word_writeLog_at _ _ 3 _ _ rfl ?_
      simp only [newNodeInitLog, List.drop, OutLRange]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
    · refine word_writeLog_at _ _ 4 _ _ rfl ?_
      simp only [newNodeInitLog, List.drop, OutLRange]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
    · refine word_writeLog_at _ _ 5 _ _ rfl ?_
      simp only [newNodeInitLog, List.drop, OutLRange]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
end OCaml.Vm.Boot.Startup
