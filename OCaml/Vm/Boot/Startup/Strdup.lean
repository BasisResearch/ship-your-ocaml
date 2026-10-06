import OCaml.Vm.Boot.Startup.StrdupMeasure
import OCaml.Vm.Boot.Startup.StrdupSteps
import OCaml.Vm.Boot.Startup.StatAllocReady
import OCaml.Vm.Boot.Startup.BlockReady
import OCaml.Vm.Boot.Startup.NativeNested
import OCaml.Vm.Primitives.LibraryMemcpy
import OCaml.Vm.Primitives.StringCopyFinish
import OCaml.Vm.Boot.Startup.MemcpyFresh
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  VsaIris.Memcpy OCaml.Vm.Primitives

/-- Bytes caml_stat_strdup never writes: its caller's frame, memory well below
its native frames, low globals outside the allocator, and live blocks. -/
def StrdupKept (H : List (Nat × Nat)) (sp : BitVec 64) (a : Nat) : Prop :=
  sp.toNat ≤ a ∨ (heapEnd ≤ a ∧ a + 48 + allocHeadroom < sp.toNat) ∨ (a < heapStart ∧ ¬ allocGlobal a) ∨
    (∃ q m, (q, m) ∈ H ∧ heapStart ≤ q ∧ q + m ≤ heapEnd ∧ q ≤ a ∧ a < q + m)

theorem StrdupKept.not_mS {H sp a} (h : StrdupKept H sp a) (frame : NativeFrame sp (48 + allocHeadroom)) :
    ¬ mS H (nativeStack sp 48) a := by
  have short := frame.resize (small := 48) (by decide) (by decide)
  have base := short.stack_nat
  have lower := frame.lower
  intro owned
  change stackWin (nativeStack sp 48) allocHeadroom a ∨ vsaFoot H a at owned
  rcases owned with stack | foot
  · unfold stackWin InExt at stack
    rw [base] at stack
    unfold nativeFrameBase at stack
    dsimp only at stack
    rcases h with h | h | h | ⟨q, m, member, low, high, qa, aq⟩ <;> simp only [heapStart, heapEnd, allocHeadroom, nativeFrameBase] at * <;> omega
  · rcases h with h | h | h | ⟨q, m, member, low, high, qa, aq⟩
    · have := allocator_foot_below foot; unfold heapEnd at *; omega
    · have := allocator_foot_below foot; omega
    · rcases foot with g | ⟨hs, _, _⟩
      · exact h.2 g
      · omega
    · rcases allocator_payload_outside member low foot with x | x <;> omega

theorem StrdupKept.out_frame {H sp a} (h : StrdupKept H sp a) (frame : NativeFrame sp (48 + allocHeadroom)) :
    a < nativeFrameBase sp 48 ∨ sp.toNat ≤ a := by
  have lower := frame.lower
  rcases h with h | h | h | ⟨q, m, member, low, high, qa, aq⟩
  · exact Or.inr h
  · left; unfold nativeFrameBase; simp only [allocHeadroom] at *; omega
  · left; unfold nativeFrameBase; simp only [heapStart, heapEnd, allocHeadroom] at *; omega
  · left; unfold nativeFrameBase; simp only [heapEnd, allocHeadroom] at *; omega

/-- A complete successful `caml_stat_strdup` of a `len`-byte string at `name`. -/
structure StrdupDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 name : BitVec 64) (len : Nat)
    (before after : Config) where
  copy : BitVec 64
  result : gprGet after.σ 10 = some copy
  pc : PCAt ra after
  stack : gprGet after.σ 2 = some sp
  saved0 : gprGet after.σ 8 = some s0
  saved1 : gprGet after.σ 9 = some s1
  saved23 : ∀ k ∈ [18, 19], gprGet after.σ k = gprGet before.σ k
  ready : RuntimeReady ((copy.toNat, len + 1) :: H) capacity sp ra after
  fresh : heapStart ≤ copy.toNat ∧ copy.toNat + (len + 1) ≤ heapEnd
  disjoint : ∀ e ∈ H, ∀ a, InExt (copy.toNat, len + 1) a → ¬ InExt e a
  bytes : ∀ k, k ≤ len → (after.σ.mem[copy.toNat + k]?).getD 0 = imgM before.σ.mem (name.toNat + k)
  kept : ∀ a, StrdupKept H sp a → (after.σ.mem[a]?).getD 0 = (before.σ.mem[a]?).getD 0
  aligned : copy.toNat % 16 = 0

theorem strdup_full (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat) (sp ra s0 s1 name : BitVec 64)
    (len : Nat) (ready : RuntimeReady H (capacity + charge) sp ra c) (frame : NativeFrame sp (48 + allocHeadroom))
    (saved : GHolds c.σ [(9, s1), (8, s0), (10, name)]) (string : CBytes c.σ.mem name.toNat len)
    (source : ∀ k, k ≤ len → StrdupKept H sp (name.toNat + k))
    (sourceGeo : name.toNat + (len + 1) ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 16 ≤ name.toNat)
    (small : len + 1 < 2 ^ 32) (charged : vsaChg (len + 1) charge) :
    FnSummary 0x8000bdf4#64 (fun d => d = c)
      (fun after => Nonempty (StrdupDone H capacity sp ra s0 s1 name len c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have frame48 := frame.resize (small := 48) (by decide) (by decide)
  have frameA : NativeFrame (nativeStack sp 48) allocHeadroom := frame.nested (front := 48) (by decide)
  have baseNat := frame48.stack_nat
  have lower := frame.lower
  -- strlen
  have outside : name.toNat + len + 1 ≤ nativeFrameBase sp 48 ∨ sp.toNat ≤ name.toNat := by
    rcases (source 0 (Nat.zero_le _)).out_frame frame with h | h
    · left
      rcases Nat.lt_or_ge (name.toNat + len) (nativeFrameBase sp 48) with g | g
      · omega
      · have := (source (nativeFrameBase sp 48 - name.toNat) (by omega)).out_frame frame
        have := frame.lower
        unfold nativeFrameBase at *
        omega
    · right; simpa using h
  obtain ⟨m, run1, ⟨M⟩⟩ := (strdup_measure c H (capacity + charge) sp ra s0 s1 name len ready frame48 saved
    string outside).run c ⟨pc, rfl⟩
  have lenReg : gprGet m.σ 10 = some (BitVec.ofNat 64 len) := M.measured.result
  -- store len + 1 and call caml_stat_alloc_noexc
  obtain ⟨a, run2, A⟩ := (strdup_alloc_call m sp (BitVec.ofNat 64 len) _ M.ready.toLeafInput frame48
    ⟨lenReg, M.ready.stack, trivial⟩).run m ⟨M.measured.pc, rfl⟩
  have readyA := M.ready.stack_log A (by decide) (by simp only [strdupAllocArgs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ A.regs (by rfl)) (gholds_lookup (n := 1) _ A.regs (by rfl)) (by decide)
    frame48 (strdupSizeLog_inside frame48)
  have sizeNat : (BitVec.ofNat 64 len + 1#64).toNat = len + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  obtain ⟨b, run3, ⟨B⟩⟩ := (stat_alloc_ready a H capacity charge (BitVec.ofNat 64 len + 1#64) _ _ readyA frameA
    (gholds_lookup (n := 10) _ A.regs (by rfl)) (by rw [sizeNat]; exact charged)).run a ⟨A.pc, rfl⟩
  -- the fresh buffer
  obtain ⟨pNonzero, pLow, pHigh, pDisjoint⟩ := B.allocation.result.fresh.destruct
  change (vsaReg b 10).toNat ≠ 0 at pNonzero
  change heapStart ≤ (vsaReg b 10).toNat at pLow
  change (vsaReg b 10).toNat + (BitVec.ofNat 64 len + 1#64).toNat ≤ heapEnd at pHigh
  rw [sizeNat] at pHigh
  have pReg : gprGet b.σ 10 = some (vsaReg b 10) := library_gpr B.ready.platform (by decide) (by decide) rfl
  have nameM : gprGet m.σ 9 = some name :=
    (M.measured.registers 9 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 9) _ M.opening.regs (by rfl))
  have nameA : gprGet a.σ 9 = some name :=
    (A.toEffectPost.gpr_frame (by decide) 9 (by decide) (by decide) (by decide)).trans nameM
  have nameB : gprGet b.σ 9 = some name := (B.saved_gpr (k := 9) (by decide)).trans nameA
  have sizeA : bytesT a.σ.mem (nativeFrameBase sp 48 + 8) 8 = BitVec.ofNat 64 len + 1#64 := by
    rw [A.memory]
    exact frame48.word_log_read (slots := [(8, BitVec.ofNat 64 len + 1#64)]) (by simp) (by simp) _ (by simp)
  have sizeB : bytesT b.σ.mem (nativeFrameBase sp 48 + 8) 8 = BitVec.ofNat 64 len + 1#64 := by
    rw [word_observed (m := a.σ.mem) _ (fun i _ => B.caller_byte frameA (by rw [baseNat]; omega))]
    exact sizeA
  -- reload the size and call memcpy
  obtain ⟨c3, run4, C⟩ := (strdup_copy_call b sp (vsaReg b 10) _ name _ B.ready.toLeafInput frame48
    ⟨pReg, B.ready.stack, nameB, trivial⟩ (fun h => pNonzero (by rw [h]; rfl)) sizeB).run b ⟨library_pc B.allocation.good B.allocation.result.frame.pc, rfl⟩
  have readyC := B.ready.effect C (by decide) (by simp only [strdupCopyArgs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ C.regs (by rfl)) (gholds_lookup (n := 1) _ C.regs (by rfl)) (by decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have sizeEq : BitVec.ofNat 64 len + 1#64 = BitVec.ofNat 64 (len + 1) := by
    rw [BitVec.ofNat_add]
  -- a source byte is never inside the fresh buffer
  have notBlock (x : Nat) (kept : StrdupKept H sp x) : ¬ InExt ((vsaReg b 10).toNat, len + 1) x := by
    intro inside
    unfold InExt at inside
    have := frame.lower
    rcases kept with h | h | h | ⟨q, m', member, low, high, qa, aq⟩
    · simp only [heapEnd, allocHeadroom] at *; omega
    · omega
    · omega
    · rw [← sizeNat] at inside
      exact pDisjoint (q, m') member x inside ⟨qa, aq⟩
  have geometry : Geo (vsaReg b 10) name jal_8000be2c_call.link (len + 1) :=
    { dlo := by have : 0x80000000 ≤ heapStart := by decide
                omega
      dhi := by have : heapEnd ≤ 0x100000000 := by decide
                omega
      dhtif := by have : Layout.sym_tohost + 16 ≤ heapStart := by decide
                  omega
      slo := string.lo
      shi := by have := string.hi; omega
      shtif := sourceGeo
      ral := by decide }
  have imageSep : ImageSeparate (InExt ((vsaReg b 10).toNat, len + 1)) := by
    have bounds : Image.textBase + Image.textSize ≤ heapStart ∧ Image.rodataBase + Image.rodataSize ≤ heapStart := by
      decide
    constructor <;> intro i hi inside <;> unfold InExt at inside <;> omega
  have separate : LocalSeparation [] (mText ++ srcText name.toNat (len + 1) (imgM c3.σ.mem)) mRegs
      (InExt ((vsaReg b 10).toNat, len + 1)) := by
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with code | src
    · have := memcpy_text_low code
      intro inside
      unfold InExt at inside
      omega
    · obtain ⟨lo, hi, -⟩ := mem_srcText src
      have := notBlock x.1 (by have k := source (x.1 - name.toNat) (by omega); rwa [show name.toNat + (x.1 - name.toNat) = x.1 by omega] at k)
      exact this
  have readOnly : ROHolds (vsaModel startupLive) c3 [] (mText ++ srcText name.toNat (len + 1) (imgM c3.σ.mem)) := by
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with code | src
    · change (c3.σ.mem[x.1]?).getD 0 = x.2
      rw [memcpy_text_loaded readyC.image x code]; rfl
    · obtain ⟨-, -, value⟩ := mem_srcText src
      rw [value]; rfl
  obtain ⟨d, run5, D⟩ := (memcpy_summary c3 memcpy_text_live geometry readyC.platform C.image startup_image_live
    imageSep separate readOnly (observed_register (by decide) (gholds_lookup (n := 1) _ C.regs (by rfl)))
    (observed_register (by decide) (gholds_lookup (n := 10) _ C.regs (by rfl)))
    (observed_register (by decide) (gholds_lookup (n := 11) _ C.regs (by rfl)))
    (by rw [← sizeEq]; exact observed_register (by decide) (gholds_lookup (n := 12) _ C.regs (by rfl)))).run c3
    ⟨C.pc, rfl⟩
  rw [sizeNat] at readyC
  have regD (k : Nat) (lower : 1 ≤ k) (upper : k ≤ 31) (unwritten : k ∉ mRegs) : gprGet d.σ k = gprGet c3.σ k :=
    library_register_frame readyC.platform D.observations.good lower upper (D.observations.registers k unwritten)
  have stackD := (regD 2 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 2) _ C.regs (by rfl))
  have readyD := readyC.of_block_frame D.observations (by decide) D.toLeafInput stackD (List.mem_cons_self ..) pLow
  -- every kept byte is unchanged from the entry through memcpy
  have keptC3 (x : Nat) (kept : StrdupKept H sp x) : (c3.σ.mem[x]?).getD 0 = (c.σ.mem[x]?).getD 0 := by
    have out := kept.out_frame frame
    have notStack : x < nativeFrameBase sp 48 ∨ sp.toNat ≤ x := out
    have lowerF := frame48.lower
    have c3b : c3.σ.mem = b.σ.mem := C.memory
    rw [c3b]
    have ba := B.allocation.memory x (kept.not_mS frame)
    change (b.σ.mem[x]?).getD 0 = (B.atMalloc.σ.mem[x]?).getD 0 at ba
    have sizeSlot : (nativeStack sp 48 + 8#64).toNat = nativeFrameBase sp 48 + 8 := by
      rw [nativeStack, frame48.address 8 (by decide), frame48.slot_nat (by decide)]
    rw [ba, B.dispatch.memory, A.memory, writeLog_out _ _ _ (show OutL (strdupSizeLog sp _) x from ⟨by
      show x < (nativeStack sp 48 + 8#64).toNat ∨ (nativeStack sp 48 + 8#64).toNat + 8 ≤ x
      rw [sizeSlot]
      have := frame48.lower
      unfold nativeFrameBase at *
      omega, trivial⟩)]
    have mEq := M.measured.memory x
    simp only [Std.ExtHashMap.get?_eq_getElem?] at mEq
    rw [mEq, M.opening.memory, frameOn_writeLog _ _ _ (strdupLog_inside frame48) x
      ⟨by rcases notStack with h | h; exact Or.inl h; exact Or.inr h, trivial⟩]
  -- caml_stat_strdup's saved words survive up to its return
  have slot (off : Nat) (h16 : 16 ≤ off) (h48 : off + 8 ≤ 48) :
      bytesT d.σ.mem (nativeFrameBase sp 48 + off) 8 = bytesT M.entered.σ.mem (nativeFrameBase sp 48 + off) 8 := by
    apply word_observed
    intro i hi
    have high := frame48.lower
    have dc3 := D.observations.memory (nativeFrameBase sp 48 + off + i) (by
      intro inside; unfold InExt at inside; unfold nativeFrameBase at *; omega)
    change (d.σ.mem[_]?).getD 0 = (c3.σ.mem[_]?).getD 0 at dc3
    have c3b : c3.σ.mem = b.σ.mem := C.memory
    have sizeSlot : (nativeStack sp 48 + 8#64).toNat = nativeFrameBase sp 48 + 8 := by
      rw [nativeStack, frame48.address 8 (by decide), frame48.slot_nat (by decide)]
    rw [dc3, c3b, B.caller_byte frameA (by rw [baseNat]; omega), A.memory,
      writeLog_out _ _ _ (show OutL (strdupSizeLog sp _) (nativeFrameBase sp 48 + off + i) from ⟨by
        show _ < (nativeStack sp 48 + 8#64).toNat ∨ (nativeStack sp 48 + 8#64).toNat + 8 ≤ _
        rw [sizeSlot]
        omega, trivial⟩)]
    have mEq := M.measured.memory (nativeFrameBase sp 48 + off + i)
    simp only [Std.ExtHashMap.get?_eq_getElem?] at mEq
    exact mEq
  have savedWord (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(40, ra), (24, s1), (32, s0)]) :
      bytesT d.σ.mem (nativeFrameBase sp 48 + off) 8 = value := by
    have bound : 16 ≤ off ∧ off + 8 ≤ 48 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega
    rw [slot off bound.1 bound.2, M.opening.memory]
    apply frame48.word_log_read (slots := [(40, ra), (24, s1), (32, s0)])
    · intro k v hk
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp
    · exact member
  obtain ⟨after, run6, E⟩ := (strdup_return d sp ra s0 s1 (vsaReg b 10) _ D.toLeafInput frame48
    ⟨stackD, (regD 8 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 8) _ C.regs (by rfl)), trivial⟩
    (savedWord 40 ra (by simp)) (savedWord 32 s0 (by simp)) (savedWord 24 s1 (by simp)) ready.aligned).run d
    ⟨D.pc, rfl⟩
  have readyE := readyD.effect E (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ E.regs (by rfl)) (gholds_lookup (n := 1) _ E.regs (by rfl)) ready.aligned
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h)
  have sameE : after.σ.mem = d.σ.mem := E.memory
  have keep23 (k : Nat) (hk : k ∈ [18, 19]) : gprGet after.σ k = gprGet c.σ k := by
    have cases : k = 18 ∨ k = 19 := by simpa using hk
    rcases cases with rfl | rfl <;>
    exact (E.toEffectPost.gpr_frame (by decide) _ (by decide) (by decide) (by decide)).trans
      ((regD _ (by decide) (by decide) (by decide)).trans
        ((C.toEffectPost.gpr_frame (by decide) _ (by decide) (by decide) (by decide)).trans
          ((B.saved_gpr (by decide)).trans ((A.toEffectPost.gpr_frame (by decide) _ (by decide) (by decide)
            (by decide)).trans ((M.measured.registers _ (by decide) (by decide) (by decide)).trans
              (M.opening.toEffectPost.gpr_frame (by decide) _ (by decide) (by decide) (by decide)))))))
  refine ⟨after, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), ⟨⟨vsaReg b 10,
    gholds_lookup (n := 10) _ E.regs (by rfl), E.pc, gholds_lookup (n := 2) _ E.regs (by rfl),
    gholds_lookup (n := 8) _ E.regs (by rfl), gholds_lookup (n := 9) _ E.regs (by rfl), keep23, readyE,
    ⟨pLow, pHigh⟩, fun e member a inside => pDisjoint e member a (by rw [sizeNat]; exact inside), ?_, ?_,
    B.allocation.result.align⟩⟩⟩
  · intro k hk
    rw [sameE]
    have copied := D.bytes k (by omega)
    rw [byte_total] at copied
    rw [copied]
    exact keptC3 _ (source k hk)
  · intro x kept
    rw [sameE]
    have dc3 := D.observations.memory x (notBlock x kept)
    change (d.σ.mem[x]?).getD 0 = (c3.σ.mem[x]?).getD 0 at dc3
    rw [dc3]
    exact keptC3 x kept
end OCaml.Vm.Boot.Startup
