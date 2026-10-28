import OCaml.Vm.Boot.Startup.InitStackSteps
import OCaml.Vm.Boot.Startup.StatChecked
import OCaml.Vm.Boot.Startup.CallerFrame
import OCaml.Vm.Boot.Startup.MainArgv
import OCaml.Vm.Boot.Startup.StatCheckedFrame
import OCaml.Vm.Boot.Startup.GcMessageReady
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.MakeFree
import OCaml.Vm.Boot.Startup.InitMerge
import OCaml.Vm.Boot.Startup.BlockCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! **caml_init_stack(max_size)** from caml_main at `parameterStack`: allocate the
32 KiB interpreter stack, record its bounds in the domain record and
`caml_max_stack_size`, and report quietly. -/

/-- caml_init_stack's entry. -/
structure InitStackCall (H : List (Nat × Nat)) (capacity charge : Nat) (ra s0 s1 s2 mx : BitVec 64) (c : Config) :
    Prop where
  pc : PCAt 0x80004064#64 c
  regs : GHolds c.σ [(2, parameterStack), (8, s0), (9, s1), (1, ra), (18, s2), (10, mx)]
  ready : RuntimeReady H (capacity + charge) parameterStack ra c
  charged : vsaChg 32768 charge
  domainOwned : (firstDomainPtr.toNat, 928) ∈ H
  domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr
  quiet : LPins8 c.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)

/-- caml_init_stack returned: the stack block `p` is live and recorded. -/
structure InitStackDone (H : List (Nat × Nat)) (capacity : Nat) (ra s0 s1 s2 mx p : BitVec 64) (before after : Config) :
    Prop where
  highKept : ∀ x, EmbedByte x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  pc : PCAt ra after
  regs : GHolds after.σ [(2, parameterStack), (1, ra), (8, s0), (9, s1), (18, s2)]
  ready : RuntimeReady ((p.toNat, 32768) :: H) capacity parameterStack ra after
  fresh : FreshBlock vsaLayoutP H p.toNat 32768
  stored : ∀ a v, (a, v) ∈ initStackCells p mx → bytesT after.σ.mem a 8 = v
  /-- Memory below the arena's end, outside the allocator and the stores. -/
  kept : ∀ x, x < heapEnd → ¬ vsaFoot H x → OutL (initStackFieldsLog p mx) x →
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  caller : CallerFrame parameterStack before after

/-- Caml_state is outside the allocator's footprint. -/
theorem caml_state_not_foot {H : List (Nat × Nat)} (i : Nat) (hi : i < 8) : ¬ vsaFoot H (Layout.sym_Caml_state + i) := by
  rintro (g | ⟨lo, _⟩)
  · unfold allocGlobal InRange at g; unfold Layout.sym_Caml_state at g; omega
  · unfold heapStart Layout.sym_Caml_state at lo; omega

/-- The windows of caml_init_stack's stores: the domain record and `caml_max_stack_size`. -/
def initStackWindows : List W :=
  [⟨firstDomainPtr.toNat, firstDomainPtr.toNat + 928⟩, ⟨camlMaxStackSizeAddr, camlMaxStackSizeAddr + 8⟩]

theorem initStackFields_inside (p mx : BitVec 64) : LogInW initStackWindows (initStackFieldsLog p mx) := by
  simp only [initStackFieldsLog, initStackCells, List.map, initStackWindows, LogInW, InsideW, domainField,
    camlMaxStackSizeAddr]
  decide

theorem initStackCells_separate (p mx : BitVec 64) :
    (initStackCells p mx).Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) :=
  (List.pairwise_map (l := initStackCells p mx) (f := Prod.fst) (R := fun a b => a + 8 ≤ b ∨ b + 8 ≤ a)).mp
    (by
      show List.Pairwise _ [domainField 136, domainField 152, domainField 144, domainField 160, domainField 168,
        domainField 176, camlMaxStackSizeAddr]
      simp only [domainField, camlMaxStackSizeAddr]
      decide)

theorem caml_init_stack (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (ra s0 s1 s2 mx : BitVec 64)
    (A : InitStackCall H capacity charge ra s0 s1 s2 mx c) :
    ∃ p after, Steps c after ∧ InitStackDone H capacity ra s0 s1 s2 mx p c after := by
  have frame := initStack_frame
  have sp1 : NativeFrame (nativeStack parameterStack 32) 544 := by constructor <;> decide
  have aligned := A.ready.aligned
  -- save
  obtain ⟨c1, run1, p1⟩ := (init_stack_save c parameterStack ra s0 s1 s2 mx A.ready.toLeafInput frame A.regs).run c
    ⟨A.pc, rfl⟩
  have inside1 : LogInW [⟨nativeFrameBase parameterStack 32, parameterStack.toNat⟩] (initStackSaveLog parameterStack ra s0 s1 s2) :=
    frame.word_log_inside fun off value member => by simp [initStackSlots] at member; omega
  have ready1 := A.ready.stack_log p1 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p1.regs rfl) (gholds_lookup (n := 1) _ p1.regs rfl) aligned frame inside1
  have low1 (x : Nat) (hx : x < nativeFrameBase parameterStack 32) : (c1.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [p1.memory, frameOn_writeLog _ _ _ inside1 x ⟨Or.inl hx, trivial⟩]
  have domain1 : bytesT c1.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr :=
    (word_observed _ fun i hi => low1 _ (by
      have : Layout.sym_Caml_state + 8 ≤ nativeFrameBase parameterStack 32 := by decide
      omega)).trans A.domain
  -- s0 = max, s1 = &Caml_state, s2 = Caml_state; caml_stat_alloc(Stack_size)
  have g1 := GprsSame.of_post p1 (by decide)
  obtain ⟨c2, run2, p2⟩ := (block_then_call c1 jal_8000408c_call_shape jal_8000408c_call_decode
    (fun _ h => jal_8000408c_call_pins h)
    (init_stack_state c1 ra mx ready1.toLeafInput ⟨gholds_lookup (n := 10) _ p1.regs rfl, trivial⟩
      domain1) (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl).run c1 ⟨p1.pc, rfl⟩
  have g2 := GprsSame.of_post p2 (by decide)
  have sp2 : gprGet c2.σ 2 = some (nativeStack parameterStack 32) :=
    g2.get (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ p1.regs rfl)
  have ready2 := ready1.stack_log p2 (by decide) (by simp only [keysG]; decide) (by decide) sp2
    (gholds_lookup (n := 1) _ p2.regs rfl) (by decide) frame (by simp only [LogInW])
  have pc2 : PCAt 0x8000bb2c#64 c2 := by have := p2.pc; rwa [jal_8000408c_call_target] at this
  obtain ⟨c3, run3, ⟨w⟩⟩ := (stat_checked c2 H capacity charge (nativeStack parameterStack 32) jal_8000408c_call.link
    mx 0x8000#64 ready2 sp1 (gholds_lookup (n := 8) _ p2.regs rfl) (gholds_lookup (n := 10) _ p2.regs rfl)
    A.charged).run c2 ⟨pc2, rfl⟩
  -- store the bounds
  have domain2 : bytesT c2.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr := by
    rw [show c2.σ.mem = c1.σ.mem from p2.memory]; exact domain1
  have domain3 : bytesT c3.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr :=
    (word_observed _ fun i hi => w.framed_byte sp1 (by unfold heapEnd Layout.sym_Caml_state; omega)
      (caml_state_not_foot i hi)).trans domain2
  have pc3 : PCAt 0x80004090#64 c3 := w.returned.pc
  obtain ⟨c4, run4, p4⟩ := (init_stack_fields c3 jal_8000408c_call.link (vsaReg w.allocated 10) mx w.ready.toLeafInput
    ⟨w.keep_saved (by decide) (gholds_lookup (n := 9) _ p2.regs rfl),
      w.keep_saved (by decide) (gholds_lookup (n := 18) _ p2.regs rfl),
      gholds_lookup (n := 10) _ w.returned.regs rfl, gholds_lookup (n := 8) _ w.returned.regs rfl, trivial⟩
    domain3).run c3 ⟨pc3, rfl⟩
  have g4 := GprsSame.of_post p4 (by decide)
  have windows : WindowsOk (((vsaReg w.allocated 10).toNat, (0x8000#64).toNat) :: H) initStackWindows :=
    (ownedWindow_ok (q := firstDomainPtr.toNat) (n := 928) (by decide) (List.mem_cons_of_mem _ A.domainOwned)
      (Nat.le_refl _) (Nat.le_refl _)).cons
      (globalWindow_ok (by decide) (by decide) (by decide)
        (fun a lo hi => by unfold camlMaxStackSizeAddr at lo hi; unfold allocGlobal InRange; omega)
        (by decide) (by decide))
  have ready4 := w.ready.window_log p4 (by decide) (by simp only [keysG]; decide) (by decide)
    (g4.get (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ w.returned.regs rfl))
    (g4.get (by decide) (by decide) (by decide) (gholds_lookup (n := 1) _ w.returned.regs rfl)) (by decide)
    (initStackFields_inside _ _) windows.pins windows.domain windows.pool windows.heap
  -- memory below the arena's end and above it, carried from the entry
  have base : nativeFrameBase parameterStack 32 = (nativeStack parameterStack 32).toNat := by decide
  have callerW := w.caller_frame sp1
  have outW (x : Nat) (h : x < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ x)
      (g : x < camlMaxStackSizeAddr ∨ camlMaxStackSizeAddr + 8 ≤ x) :
      (c4.σ.mem[x]?).getD 0 = (c3.σ.mem[x]?).getD 0 := by
    rw [p4.memory, frameOn_writeLog _ _ _ (initStackFields_inside _ _) x ⟨h, g, trivial⟩]
  have slot4 (off : Nat) (value : BitVec 64) (member : (off, value) ∈ initStackSlots ra s0 s1 s2) :
      bytesT c4.σ.mem (nativeFrameBase parameterStack 32 + off) 8 = value := by
    have range : off + 8 ≤ 32 := by simp [initStackSlots] at member; omega
    have above : firstDomainPtr.toNat + 928 ≤ nativeFrameBase parameterStack 32 := by decide
    have aboveG : camlMaxStackSizeAddr + 8 ≤ nativeFrameBase parameterStack 32 := by decide
    rw [word_observed (m := c1.σ.mem) _ fun i hi => by
      have grow : nativeFrameBase parameterStack 32 ≤ nativeFrameBase parameterStack 32 + off + i :=
        Nat.le_trans (Nat.le_add_right _ off) (Nat.le_add_right _ i)
      rw [outW _ (Or.inr (Nat.le_trans above grow)) (Or.inr (Nat.le_trans aboveG grow)),
        callerW.byte _ (by rw [← base]; exact grow),
        show c2.σ.mem = c1.σ.mem from p2.memory], p1.memory]
    exact frame.word_log_read (by simp [initStackSlots]; omega) (by simp [initStackSlots]) _ member
  obtain ⟨c5, run5, p5⟩ := (init_stack_return c4 parameterStack ra s0 s1 s2 (mx >>> 10) jal_8000408c_call.link
    ready4.toLeafInput frame
    ⟨g4.get (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ w.returned.regs rfl),
      gholds_lookup (n := 12) _ p4.regs rfl, trivial⟩ slot4).run c4 ⟨p4.pc, rfl⟩
  have ready5 := ready4.stack_log p5 (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ p5.regs rfl) (gholds_lookup (n := 1) _ p5.regs rfl) aligned frame (by simp only [LogInW])
  -- low memory below the arena's end, carried from the entry
  have deep : heapEnd ≤ nativeFrameBase parameterStack 80 := by decide
  have frame80 : NativeFrame parameterStack 80 := by constructor <;> decide
  have low5 (x : Nat) (hx : x < heapEnd) (foot : ¬ vsaFoot H x) (out : OutL (initStackFieldsLog (vsaReg w.allocated 10) mx) x) :
      (c5.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have b32 : x < nativeFrameBase parameterStack 32 := Nat.lt_of_lt_of_le hx (by decide)
    rw [show c5.σ.mem = c4.σ.mem from p5.memory, p4.memory, writeLog_out _ _ _ out,
      w.framed_byte sp1 hx foot, show c2.σ.mem = c1.σ.mem from p2.memory]
    exact low1 x b32
  have quiet5 : LPins8 c5.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8) :=
    lpins8_observed A.quiet fun i hi => low5 _ (by unfold Layout.sym_caml_verb_gc heapEnd; omega)
      (fun f => by
        rcases f with g | ⟨lo, _⟩
        · unfold allocGlobal InRange Layout.sym_caml_verb_gc at g; omega
        · unfold heapStart Layout.sym_caml_verb_gc at lo; omega)
      (by
        have : (0x80064930 : Nat) + 8 ≤ firstDomainPtr.toNat := by decide
        simp only [initStackFieldsLog, initStackCells, List.map, OutL, domainField, camlMaxStackSizeAddr,
          Layout.sym_caml_verb_gc, and_true]
        omega)
  obtain ⟨c6, run6, Q⟩ := ready_gc_message c5 _ capacity parameterStack ra 8#64 p5.pc ready5 frame80
    (gholds_lookup (n := 10) _ p5.regs rfl) quiet5
  have last (x : Nat) (hx : x < nativeFrameBase parameterStack 80 ∨ parameterStack.toNat ≤ x) :
      (c6.σ.mem[x]?).getD 0 = (c5.σ.mem[x]?).getD 0 := by
    rw [Q.memory, frameOn_writeLog _ _ _ (gcMessageLog_inside frame80) x ⟨hx, trivial⟩]
  have gQ := Q.same
  have g5 := GprsSame.of_post p5 (by decide)
  refine ⟨vsaReg w.allocated 10, c6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), {
    pc := Q.pc
    regs := ⟨gholds_lookup (n := 2) _ Q.regs rfl, gholds_lookup (n := 1) _ Q.regs rfl,
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ p5.regs rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ p5.regs rfl),
      gQ.get (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ p5.regs rfl), trivial⟩
    ready := Q.ready
    fresh := w.allocation.allocation.result.fresh
    stored := fun a v member => by
      have b : a + 8 ≤ nativeFrameBase parameterStack 80 := by
        simp only [initStackCells, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        rcases member with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      rw [word_observed (m := c4.σ.mem) _ fun i hi => by
        rw [last _ (Or.inl (by omega)), show c5.σ.mem = c4.σ.mem from p5.memory], p4.memory]
      exact OCaml.Vm.Gc.word_writeLog_cells _ _ (initStackCells_separate _ _) member
    highKept := fun x hx => by
      have high : 0x86800000 ≤ x := hx.1
      have below := hx.stack_room
      rw [last x (Or.inl (by unfold nativeFrameBase; omega)),
        show c5.σ.mem = c4.σ.mem from p5.memory,
        outW x (Or.inr (Nat.le_trans (show firstDomainPtr.toNat + 928 ≤ heapEnd by decide) hx.1))
          (Or.inr (Nat.le_trans (show camlMaxStackSizeAddr + 8 ≤ heapEnd by decide) hx.1)),
        w.framed_byte_below sp1 (by
          change x + 544 < (nativeStack parameterStack 32).toNat
          have stack : (nativeStack parameterStack 32).toNat = parameterStack.toNat - 32 := by decide
          rw [stack]; omega) (KeptByte.not_foot (Or.inl hx)),
        show c2.σ.mem = c1.σ.mem from p2.memory]
      exact low1 x (by unfold nativeFrameBase; omega)
    kept := fun x hx foot out => by
      rw [last x (Or.inl (Nat.lt_of_lt_of_le hx deep))]
      exact low5 x hx foot out
    caller := ⟨fun x hx => by
      have hsp : (nativeStack parameterStack 32).toNat ≤ parameterStack.toNat := by decide
      have dom : firstDomainPtr.toNat + 928 ≤ parameterStack.toNat := by decide
      have glob : camlMaxStackSizeAddr + 8 ≤ parameterStack.toNat := by decide
      rw [last x (Or.inr hx), show c5.σ.mem = c4.σ.mem from p5.memory,
        outW x (Or.inr (Nat.le_trans dom hx)) (Or.inr (Nat.le_trans glob hx)),
        callerW.byte x (Nat.le_trans hsp hx), show c2.σ.mem = c1.σ.mem from p2.memory, p1.memory,
        frameOn_writeLog _ _ _ inside1 x ⟨Or.inr hx, trivial⟩]⟩ }⟩
/-- The executed stack initializer preserves HTIF's file records and fd positions. -/
theorem InitStackDone.htif {H capacity ra s0 s1 s2 mx p before after}
    (S : InitStackDone H capacity ra s0 s1 s2 mx p before after) (x : Nat) (h : HtifByte x) :
    (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0 := by
  have b := h.bounds
  apply S.kept x (by simp only [Layout.sym_files, heapEnd] at b ⊢; omega)
    (KeptByte.not_foot (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩ <;>
    simp only [Layout.sym_fs_ready, Layout.sym_impure_ptr, Layout.sym_files, Layout.sym_print_config, Layout.sym_fds,
      initStackFieldsLog, initStackCells, List.map, OutL, domainField, firstDomainPtr, heapStart, camlMaxStackSizeAddr,
      BitVec.toNat_ofNat, and_true] at * <;> omega

/-- Stack initialization keeps selected original blocks outside the domain record. -/
theorem InitStackDone.selected_live {H capacity ra s0 s1 s2 mx p before after K}
    (S : InitStackDone H capacity ra s0 s1 s2 mx p before after)
    (sub : ∀ e ∈ K, e ∈ H)
    (bounds : ∀ e ∈ K, heapStart ≤ e.1 ∧ e.1 + e.2 ≤ heapEnd)
    (domain : ∀ e ∈ K, e.1 + e.2 ≤ firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ e.1) :
    LiveFrame K before after := by
  apply LiveFrame.of_foot_arena bounds
  intro x lo hi foot
  obtain ⟨e, he, inside⟩ := owned_of_not_foot lo hi foot
  have apart := domain e he
  unfold InExt at inside
  apply S.kept x hi (fun h => foot (vsaFoot_subset sub h))
  simp only [initStackFieldsLog, initStackCells, List.map, OutL, domainField, camlMaxStackSizeAddr, and_true]
  unfold heapStart at lo
  omega

end OCaml.Vm.Boot.Startup
