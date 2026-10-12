import OCaml.Vm.Boot.Startup.SearchInPath
import OCaml.Vm.Boot.Startup.BlockCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.Logic VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
  VsaIris.MallocFast LeanRV64DExecutable OCaml.Vm.Primitives

/-- A C string of `len` bytes whose first character is `/`. -/
structure RootedName (m : Vsa.MemRepr.Mem) (p : BitVec 64) (len : Nat) : Prop where
  bytes : CBytes m p.toNat len
  region : ReadWindow p (len + 1)
  slash : imgM m (p.toNat + 0) = 47#8

theorem RootedName.transport {m m' : Vsa.MemRepr.Mem} {p : BitVec 64} {len : Nat} (h : RootedName m p len)
    (same : ∀ i, i ≤ len → (m'[p.toNat + i]?).getD 0 = (m[p.toNat + i]?).getD 0) : RootedName m' p len where
  bytes := h.bytes.transport same
  region := h.region
  slash := by change (m'[_]?).getD 0 = _; rw [same 0 (Nat.zero_le _)]; exact h.slash

/-- The current character is `/`: `caml_stat_strdup(name)`. -/
theorem search_scan_slash (c : Config) (ra cursor name a0 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (scanStepInput cursor 47#8 a0 ++ [(19, name)])) :
    FnSummary 0x8002543c#64 (fun d => d = c)
      (WriteRegistersPost ([10, 14] ++ [1]) [] c jal_80025448_call.target name
        ((1, jal_80025448_call.link) :: [(10, name), (14, cursor + 1#64), (15, nameByteWord 47#8), (13, 47#64),
          (19, name)])) := by
  apply block_then_call c jal_80025448_call_shape jal_80025448_call_decode (fun _ h => jal_80025448_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_search_in_pathX543cFSeg ++ searchInPathDupSave) 0x8002543c#64
        (scanStepInput cursor 47#8 a0 ++ [(19, name)]) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 15, 13, 10, 19]; decide
      shape := by change ChainOK _ [14, 15, 13, 10, 19] _; decide
      tick := leaf.tick
      facts := by
        have code := searchInPathScan_code leaf.image
        have dup := searchInPathDup_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
        change guardB bop.BNE (nameByteWord 47#8) 47#64 = false
        decide }))
  · rfl
  · rfl
  · change [(10, name + 0#64), (14, cursor + 1#64), (15, nameByteWord 47#8), (13, 47#64), (19, name)] = _
    rw [BitVec.add_zero]
  · rfl
  · decide

/-- `caml_search_in_path(tbl, name)` for a name starting with `/`: a fresh copy
of `name`, without consulting the table. -/
theorem search_in_path_rooted (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 s3 tbl name : BitVec 64) (len : Nat)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp (176 + (48 + allocHeadroom)))
    (regs : GHolds c.σ [(8, s0), (9, s1), (18, s2), (19, s3), (10, tbl), (11, name)])
    (rooted : RootedName c.σ.mem name len)
    (source : ∀ k, k ≤ len → StrdupKept H (nativeStack sp 176) (name.toNat + k))
    (outside : ∀ k, k ≤ len → name.toNat + k < nativeFrameBase sp 176 ∨ sp.toNat ≤ name.toNat + k)
    (sourceGeo : name.toNat + (len + 1) ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 16 ≤ name.toNat)
    (small : len + 1 < 2 ^ 32) (charged : vsaChg (len + 1) charge) :
    FnSummary 0x80025404#64 (fun d => d = c)
      (fun after => Nonempty (SearchInPathDone H capacity sp ra s0 s1 s2 s3 name len c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame176 := frame.resize (small := 176) (by decide) (by decide)
  have inner : NativeFrame (nativeStack sp 176) (48 + allocHeadroom) := frame.nested (front := 176) (by decide)
  have baseNat := frame176.stack_nat
  -- prologue
  obtain ⟨a, run1, saved⟩ := (search_in_path_prefix c sp ra s0 s2 s3 tbl name ready.toLeafInput frame176
    ⟨ready.stack, gholds_lookup (n := 18) _ regs (by rfl), gholds_lookup (n := 19) _ regs (by rfl), ready.raReg,
      gholds_lookup (n := 8) _ regs (by rfl), gholds_lookup (n := 10) _ regs (by rfl),
      gholds_lookup (n := 11) _ regs (by rfl), trivial⟩).run
    c ⟨pc, rfl⟩
  have readyA := ready.stack_log saved (by decide) (by simp only [searchInPathSaved, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ saved.regs (by rfl)) (gholds_lookup (n := 1) _ saved.regs (by rfl)) ready.aligned
    frame176 (searchInPathLog_inside frame176)
  have keepA (x : Nat) (out : x < nativeFrameBase sp 176 ∨ sp.toNat ≤ x) :
      (a.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    rw [saved.memory, frameOn_writeLog _ _ _ (searchInPathLog_inside frame176) x
      ⟨by rcases out with h | h; exact Or.inl h; exact Or.inr h, trivial⟩]
  have rootedA : RootedName a.σ.mem name len := rooted.transport (fun i hi => keepA _ (outside i hi))
  -- the first character is '/'
  obtain ⟨b, run2, firstPost⟩ := (search_in_path_first a ra tbl name (imgM a.σ.mem (name.toNat + 0))
    (saved.leaf (by rfl) ready.aligned)
    ⟨gholds_lookup (n := 11) _ saved.regs (by rfl), gholds_lookup (n := 10) _ saved.regs (by rfl), trivial⟩
    (name_window rootedA.region (Nat.zero_le _) |> fun w => by simpa [nameCursor] using w) rfl
    (by rw [rootedA.slash]; decide)).run a ⟨saved.pc, rfl⟩
  have readyB := readyA.effect firstPost (by decide)
    (by simp only [searchInPathScanRegs, keysG, List.cons_append, List.nil_append]; decide) (by decide)
    ((firstPost.frame .x2 (by decide) (by decide)).trans readyA.stack)
    ((firstPost.frame .x1 (by decide) (by decide)).trans readyA.raReg) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have memB : b.σ.mem = a.σ.mem := firstPost.memory
  obtain ⟨f, run3, dup⟩ := (search_scan_slash b ra name name tbl readyB.toLeafInput
    ⟨gholds_lookup (n := 14) _ firstPost.regs (by rfl),
      by rw [← rootedA.slash]; exact gholds_lookup (n := 15) _ firstPost.regs (by rfl),
      gholds_lookup (n := 13) _ firstPost.regs (by rfl), gholds_lookup (n := 10) _ firstPost.regs (by rfl),
      gholds_lookup (n := 19) _ firstPost.regs (by rfl), trivial⟩).run b ⟨firstPost.pc, rfl⟩
  have readyF := readyB.effect dup (by decide) (by simp only [keysG]; decide) (by decide)
    ((dup.frame .x2 (by decide) (by decide)).trans readyB.stack)
    (gholds_lookup (n := 1) _ dup.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have memF : f.σ.mem = a.σ.mem := (show f.σ.mem = b.σ.mem from dup.memory).trans memB
  have keepReg (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [2, 15, 19, 18, 14, 13, 10, 1])
      (v : BitVec 64) (hv : gprGet c.σ n = some v) : gprGet f.σ n = some v := by
    have s1 := saved.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    have s2 := firstPost.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    have s4 := dup.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    exact s4.trans (s2.trans (s1.trans hv))
  have stringF : CBytes f.σ.mem name.toNat len := by rw [memF]; exact rootedA.bytes
  obtain ⟨g, run5, ⟨S⟩⟩ := (strdup_full f H capacity charge (nativeStack sp 176) _ s0 s1 name len readyF inner
    ⟨keepReg 9 (by decide) (by decide) (by decide) s1 regs.2.1,
      keepReg 8 (by decide) (by decide) (by decide) s0 regs.1, gholds_lookup (n := 10) _ dup.regs (by rfl), trivial⟩
    stringF source sourceGeo small charged).run f ⟨dup.pc, rfl⟩
  have savedWord (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(144, s2), (136, s3), (168, ra), (160, s0)]) :
      bytesT g.σ.mem (nativeFrameBase sp 176 + off) 8 = value := by
    have bound : off + 8 ≤ 176 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
    rw [word_observed (m := f.σ.mem) _ (fun i hi => S.kept _ (Or.inl (by rw [baseNat]; omega))), memF,
      saved.memory]
    apply frame176.word_log_read (slots := [(144, s2), (136, s3), (168, ra), (160, s0)])
    · intro k v hk
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp
    · exact member
  obtain ⟨after, run6, returned⟩ := (search_in_path_return g sp ra s0 s2 s3 S.copy _ S.ready.toLeafInput frame176
    ⟨S.result, S.stack, trivial⟩ (savedWord 168 ra (by simp)) (savedWord 160 s0 (by simp))
    (savedWord 144 s2 (by simp)) (savedWord 136 s3 (by simp)) ready.aligned).run g ⟨S.pc, rfl⟩
  have readyR := S.ready.effect returned (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ returned.regs (by rfl)) (gholds_lookup (n := 1) _ returned.regs (by rfl))
    ready.aligned (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have memR : after.σ.mem = g.σ.mem := returned.memory
  refine ⟨after, run1.trans (run2.trans (run3.trans (run5.trans run6))), ⟨⟨S.copy,
    gholds_lookup (n := 10) _ returned.regs (by rfl), returned.pc, gholds_lookup (n := 2) _ returned.regs (by rfl),
    gholds_lookup (n := 8) _ returned.regs (by rfl),
    (returned.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans S.saved1,
    gholds_lookup (n := 18) _ returned.regs (by rfl), gholds_lookup (n := 19) _ returned.regs (by rfl),
    fun k lo hi => (returned.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
      ((S.upper k lo hi).trans ((dup.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
        ((firstPost.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
          (saved.toEffectPost.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega))))),
    readyR, S.fresh, S.disjoint, ?_, ?_, S.aligned⟩⟩⟩
  · intro k hk
    rw [memR, S.bytes k hk]
    change (f.σ.mem[_]?).getD 0 = (c.σ.mem[_]?).getD 0
    rw [memF]
    exact keepA _ (outside k hk)
  · intro x kept out
    rw [memR, S.kept x kept, memF]
    exact keepA x out
end OCaml.Vm.Boot.Startup
