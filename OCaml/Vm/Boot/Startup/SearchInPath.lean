import OCaml.Vm.Boot.Startup.SearchInPathScan
import OCaml.Vm.Boot.Startup.Strdup
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.Logic VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap
  VsaIris.MallocFast LeanRV64DExecutable OCaml.Vm.Primitives

/-- `caml_search_in_path(tbl, name)` for an empty table and a slash-free name:
a fresh copy of `name`. -/
structure SearchInPathDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 s2 s3 name : BitVec 64) (len : Nat)
    (before after : Config) where
  copy : BitVec 64
  result : gprGet after.σ 10 = some copy
  pc : PCAt ra after
  stack : gprGet after.σ 2 = some sp
  saved0 : gprGet after.σ 8 = some s0
  saved1 : gprGet after.σ 9 = some s1
  saved2 : gprGet after.σ 18 = some s2
  saved3 : gprGet after.σ 19 = some s3
  ready : RuntimeReady ((copy.toNat, len + 1) :: H) capacity sp ra after
  fresh : heapStart ≤ copy.toNat ∧ copy.toNat + (len + 1) ≤ heapEnd
  disjoint : ∀ e ∈ H, ∀ a, InExt (copy.toNat, len + 1) a → ¬ InExt e a
  bytes : ∀ k, k ≤ len → (after.σ.mem[copy.toNat + k]?).getD 0 = imgM before.σ.mem (name.toNat + k)
  kept : ∀ a, StrdupKept H (nativeStack sp 176) a → (a < nativeFrameBase sp 176 ∨ sp.toNat ≤ a) →
    (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  aligned : copy.toNat % 16 = 0

theorem search_in_path_plain (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra s0 s1 s2 s3 tbl name : BitVec 64) (len : Nat)
    (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp (176 + (48 + allocHeadroom)))
    (regs : GHolds c.σ [(8, s0), (9, s1), (18, s2), (19, s3), (10, tbl), (11, name)])
    (plain : PlainName c.σ.mem name len)
    (source : ∀ k, k ≤ len → StrdupKept H (nativeStack sp 176) (name.toNat + k))
    (outside : ∀ k, k ≤ len → name.toNat + k < nativeFrameBase sp 176 ∨ sp.toNat ≤ name.toNat + k)
    (sourceGeo : name.toNat + (len + 1) ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 16 ≤ name.toNat)
    (table : ReadWindow tbl 4) (tableHigh : sp.toNat ≤ tbl.toNat)
    (empty : LPins4 c.σ.mem tbl.toNat (List.replicate 4 0#8))
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
  have plainA : PlainName a.σ.mem name len :=
    { bytes := plain.bytes.transport (fun i hi => keepA _ (outside i hi))
      region := plain.region
      noSlash := fun k hk => by
        change (a.σ.mem[_]?).getD 0 ≠ _
        rw [keepA _ (outside k (by omega))]
        exact plain.noSlash k hk
      positive := plain.positive }
  -- first character
  have first0 : imgM a.σ.mem (name.toNat + 0) ≠ 0#8 := plainA.bytes.nz 0 plainA.positive
  obtain ⟨b, run2, firstPost⟩ := (search_in_path_first a ra tbl name (imgM a.σ.mem (name.toNat + 0))
    (saved.leaf (by rfl) ready.aligned)
    ⟨gholds_lookup (n := 11) _ saved.regs (by rfl), gholds_lookup (n := 10) _ saved.regs (by rfl), trivial⟩
    (name_window plainA.region (Nat.zero_le _) |> fun w => by simpa [nameCursor] using w) rfl first0).run
    a ⟨saved.pc, rfl⟩
  have memB : b.σ.mem = a.σ.mem := firstPost.memory
  have plainB : PlainName b.σ.mem name len := by rw [memB]; exact plainA
  have readyB := readyA.effect firstPost (by decide)
    (by simp only [searchInPathScanRegs, keysG, List.cons_append, List.nil_append]; decide) (by decide)
    ((firstPost.frame .x2 (by decide) (by decide)).trans readyA.stack)
    ((firstPost.frame .x1 (by decide) (by decide)).trans readyA.raReg) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  -- slash scan
  obtain ⟨e, run3, scanned⟩ := (slash_scan b name ra tbl len plainB readyB.toLeafInput
    ⟨gholds_lookup (n := 14) _ firstPost.regs (by rfl),
      by rw [memB]; exact gholds_lookup (n := 15) _ firstPost.regs (by rfl),
      gholds_lookup (n := 13) _ firstPost.regs (by rfl), gholds_lookup (n := 10) _ firstPost.regs (by rfl),
      trivial⟩).run b ⟨firstPost.pc, rfl⟩
  have readyE := readyB.effect scanned (by decide) (by simp only [keysG]; decide) (by decide)
    ((scanned.frame .x2 (by decide) (by decide)).trans readyB.stack)
    ((scanned.frame .x1 (by decide) (by decide)).trans readyB.raReg) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have memE : e.σ.mem = a.σ.mem := scanned.memory.trans memB
  -- empty table: duplicate the name
  have sizeE : LPins4 e.σ.mem tbl.toNat (List.replicate 4 0#8) := by
    have keep (i : Nat) : (e.σ.mem[tbl.toNat + i]?).getD 0 = (c.σ.mem[tbl.toNat + i]?).getD 0 := by
      rw [memE]; exact keepA _ (Or.inr (by omega))
    obtain ⟨e0, e1, e2, e3⟩ := empty
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := keep 0; simp only [Nat.add_zero] at this; rw [this]; exact e0
    · rw [keep 1]; exact e1
    · rw [keep 2]; exact e2
    · rw [keep 3]; exact e3
  obtain ⟨f, run4, dup⟩ := (search_in_path_dup e ra tbl name tbl readyE.toLeafInput
    ⟨(scanned.frame .x18 (by decide) (by decide)).trans (gholds_lookup (n := 18) _ firstPost.regs (by rfl)),
      (scanned.frame .x19 (by decide) (by decide)).trans (gholds_lookup (n := 19) _ firstPost.regs (by rfl)),
      gholds_lookup (n := 10) _ scanned.regs (by rfl), trivial⟩ table sizeE).run e ⟨scanned.pc, rfl⟩
  have readyF := readyE.effect dup (by decide) (by simp only [keysG]; decide) (by decide)
    ((dup.frame .x2 (by decide) (by decide)).trans readyE.stack)
    (gholds_lookup (n := 1) _ dup.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have memF : f.σ.mem = a.σ.mem := (show f.σ.mem = e.σ.mem from dup.memory).trans memE
  -- s0 and s1 are untouched since entry
  have keepReg (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [2, 15, 19, 18, 14, 13, 10, 1])
      (v : BitVec 64) (hv : gprGet c.σ n = some v) : gprGet f.σ n = some v := by
    have s1 := saved.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    have s2 := firstPost.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    have s3 := scanned.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    have s4 := dup.toEffectPost.gpr_frame (by decide) n lower upper (by simp at unwritten ⊢; omega)
    exact s4.trans (s3.trans (s2.trans (s1.trans hv)))
  have stringF : CBytes f.σ.mem name.toNat len := by rw [memF]; exact plainA.bytes
  obtain ⟨g, run5, ⟨S⟩⟩ := (strdup_full f H capacity charge (nativeStack sp 176) _ s0 s1 name len readyF inner
    ⟨keepReg 9 (by decide) (by decide) (by decide) s1 regs.2.1,
      keepReg 8 (by decide) (by decide) (by decide) s0 regs.1, gholds_lookup (n := 10) _ dup.regs (by rfl), trivial⟩
    stringF source sourceGeo small charged).run f ⟨dup.pc, rfl⟩
  -- the saved words survive the copy
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
  refine ⟨after, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), ⟨⟨S.copy,
    gholds_lookup (n := 10) _ returned.regs (by rfl), returned.pc, gholds_lookup (n := 2) _ returned.regs (by rfl),
    gholds_lookup (n := 8) _ returned.regs (by rfl),
    (returned.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans S.saved1,
    gholds_lookup (n := 18) _ returned.regs (by rfl), gholds_lookup (n := 19) _ returned.regs (by rfl),
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
