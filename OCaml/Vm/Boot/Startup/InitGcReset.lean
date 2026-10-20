import OCaml.Vm.Boot.Startup.CamlInitGcArgs
import OCaml.Vm.Boot.Startup.ReadSectionsReset
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- caml_init_domain's record and the minor ref tables as caml_init_gc reads
them: the record is owned, `young_limit` equals `young_trigger`, there is no
minor heap and no major heap yet, and the three tables are empty. -/
structure DomainKept (H : List (Nat × Nat)) (m : Std.ExtHashMap Nat (BitVec 8)) (t1 t2 t3 : BitVec 64) : Prop where
  owned : (firstDomainPtr.toNat, 928) ∈ H
  idle : bytesT m (domainField 8) 8 = bytesT m (domainField 56) 8
  noYoung : bytesT m (domainField 32) 8 = 0#64
  noHeap : bytesT m (domainField 336) 8 = 0#64
  refs : RefTablesPre H m t1 t2 t3

/-- The record and the tables survive any change that keeps the memory below the arena's end. -/
theorem DomainKept.of_low {H : List (Nat × Nat)} {m m' : Std.ExtHashMap Nat (BitVec 8)} {t1 t2 t3 : BitVec 64}
    (h : DomainKept H m t1 t2 t3) (f : ∀ x, x < heapEnd → (m'[x]?).getD 0 = (m[x]?).getD 0) :
    DomainKept H m' t1 t2 t3 := by
  have word (a : Nat) (ha : a + 8 ≤ heapEnd) : bytesT m' a 8 = bytesT m a 8 :=
    word_observed _ fun i hi => f _ (by omega)
  have field (off : Nat) (hoff : off + 8 ≤ 928) : bytesT m' (domainField off) 8 = bytesT m (domainField off) 8 :=
    word _ (by
      have : firstDomainPtr.toNat + 928 ≤ heapEnd := by decide
      unfold domainField; omega)
  have table {t : BitVec 64} (spot : RefTableSpot t) : bytesT m' t.toNat 8 = bytesT m t.toNat 8 :=
    word _ (by have := spot.high; omega)
  have R := h.refs
  exact ⟨h.owned, (field 8 (by decide)).trans (h.idle.trans (field 56 (by decide)).symm),
    (field 32 (by decide)).trans h.noYoung, (field 336 (by decide)).trans h.noHeap,
    { R with
      ptr1 := (field 104 (by decide)).trans R.ptr1
      ptr2 := (field 112 (by decide)).trans R.ptr2
      ptr3 := (field 120 (by decide)).trans R.ptr3
      empty1 := (table R.spot1).trans R.empty1
      empty2 := (table R.spot2).trans R.empty2
      empty3 := (table R.spot3).trans R.empty3 }⟩

/-- Eight zero `.bss` bytes of caml_init_gc's globals. -/
theorem GcInitImage.zero {c : Config} (h : GcInitImage c) (a : Nat) (ha : ∀ i, i < 8 → GcBssByte (a + i)) :
    Primitives.read8 c.σ.mem a = List.replicate 8 0#8 := by
  have b0 := h.bss _ (ha 0 (by decide))
  simp only [Nat.add_zero] at b0
  simp only [Primitives.read8, b0, h.bss _ (ha 1 (by decide)), h.bss _ (ha 2 (by decide)), h.bss _ (ha 3 (by decide)),
    h.bss _ (ha 4 (by decide)), h.bss _ (ha 5 (by decide)), h.bss _ (ha 6 (by decide)), h.bss _ (ha 7 (by decide))]
  rfl

theorem GcInitImage.word {c : Config} (h : GcInitImage c) (a : Nat) (ha : ∀ i, i < 8 → GcBssByte (a + i)) :
    bytesT c.σ.mem a 8 = 0#64 := by
  rw [← read8_value, h.zero a ha]; rfl

/-- The credits caml_init_gc's five allocations take: page table, minor heap,
major heap, and two `caml_stat_alloc`s. -/
def initGcCredits : Nat := 16384 + 2101248 + 1019968 + 32 + 32768
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives Startup

/-- The blocks owned once the section table is read. -/
abbrev ResetReadSections.blocks {initial after} (w : ResetReadSections initial after) : List (Nat × Nat) :=
  (w.blk.toNat, 56) :: attemptBlocks w.attempt.opened

/-- caml_main from the section table to caml_init_gc's entry, with the
default parameters. `dom` is caml_init_domain's record, which every step
since keeps (supplied by `ResetDomainKept_Statement`). -/
theorem reset_init_gc_call {initial sections : Config} (w : ResetReadSections initial sections)
    {t1 t2 t3 : BitVec 64} (dom : DomainKept w.blocks sections.σ.mem t1 t2 t3) :
    ∃ after, Steps (Vsa.Densify.fillZero initial) after ∧
      InitGcCall w.blocks (startupAllocatorCredits - 656 - initGcCredits) 32 32768 1019968 2101248 16384
        parameterStack jal_80004e6c_call.link 3#64 argvPtr (vsaReg w.attempt.opened.call.atRetry 18)
        (vsaReg sections 19) (vsaReg sections 20) (vsaReg sections 21) (vsaReg sections 22) (vsaReg sections 23)
        (vsaReg sections 24) (vsaReg sections 25) t1 t2 t3 (bytesT sections.σ.mem flCurWszAddr 8) after := by
  have D := w.done
  obtain ⟨after, run, post⟩ := (caml_init_gc_call sections jal_80004e10_call.link D.ready.toLeafInput
    ⟨gholds_lookup (n := 2) _ D.regs rfl, trivial⟩ w.gc).run sections ⟨D.pc, rfl⟩
  have frame := camlInitGcArgs_frame
  have inside : LogInW [⟨nativeFrameBase (parameterStack + 16#64) 16, (parameterStack + 16#64).toNat⟩]
      camlInitGcArgsLog :=
    frame.word_log_inside fun off value member => by simp [camlInitGcArgSlots] at member; omega
  have low (x : Nat) (hx : x < heapEnd) : (after.σ.mem[x]?).getD 0 = (sections.σ.mem[x]?).getD 0 := by
    rw [post.memory, frameOn_writeLog _ _ _ inside x ⟨Or.inl ?_, trivial⟩]
    show x < nativeFrameBase (parameterStack + 16#64) 16
    have : heapEnd ≤ nativeFrameBase (parameterStack + 16#64) 16 := by decide
    omega
  have dom' := dom.of_low low
  have gc : GcInitImage after := w.gc.of_bytes fun a ha => low a (by
    have r := ha.late.range
    unfold heapEnd; omega)
  have keep (n : Nat) (v : BitVec 64) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [14, 15, 17, 16, 13, 12, 11, 10] ++ [1])
      (hv : gprGet sections.σ n = some v) : gprGet after.σ n = some v :=
    (post.toEffectPost.gpr_frame (by decide) n lo hi out).trans hv
  have saved (n : Nat) (lo : 19 ≤ n) (hi : n ≤ 25) : gprGet after.σ n = some (vsaReg sections n) :=
    keep n _ (by omega) (by omega) (by simp; omega) (gpr_of_ready D.ready n (by omega) (by omega))
  have credits : startupAllocatorCredits - 656 - initGcCredits + 32768 + 32 + 1019968 + 2101248 + 16384 =
      startupAllocatorCredits - 656 := by decide
  have arg (off : Nat) (value : BitVec 64) (member : (off, value) ∈ camlInitGcArgSlots) :
      bytesT after.σ.mem (nativeFrameBase (parameterStack + 16#64) 16 + off) 8 = value := by
    rw [post.memory]
    exact frame.word_log_read (by simp [camlInitGcArgSlots]; omega) (by simp [camlInitGcArgSlots]) _ member
  have bss (a : Nat) (lo hi : Nat) (inside : lo ≤ a ∧ a + 8 ≤ hi) (window : ∀ x, lo ≤ x → x < hi → GcBssByte x) :
      bytesT after.σ.mem a 8 = 0#64 :=
    gc.word a fun i _ => window _ (by omega) (by omega)
  refine ⟨after, w.run.trans run, {
    pc := by have := post.pc; rwa [jal_80004e6c_call_target] at this
    regs := ⟨gholds_lookup (n := 2) _ post.regs rfl,
      keep 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ D.regs rfl),
      keep 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ D.regs rfl),
      saved 19 (by decide) (by decide), saved 20 (by decide) (by decide), saved 21 (by decide) (by decide),
      saved 22 (by decide) (by decide), saved 23 (by decide) (by decide), saved 24 (by decide) (by decide),
      saved 25 (by decide) (by decide), gholds_lookup (n := 1) _ post.regs rfl,
      keep 8 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ D.regs rfl),
      gholds_lookup (n := 10) _ post.regs rfl, gholds_lookup (n := 12) _ post.regs rfl,
      gholds_lookup (n := 13) _ post.regs rfl, gholds_lookup (n := 14) _ post.regs rfl,
      gholds_lookup (n := 15) _ post.regs rfl, gholds_lookup (n := 16) _ post.regs rfl,
      gholds_lookup (n := 17) _ post.regs rfl, gholds_lookup (n := 11) _ post.regs rfl, trivial⟩
    ready := by
      rw [credits]
      exact D.ready.stack_log post (by decide) (by simp only [keysG]; decide) (by decide)
        (gholds_lookup (n := 2) _ post.regs rfl) (gholds_lookup (n := 1) _ post.regs rfl) (by decide) frame inside
    frame := by constructor <;> decide
    argWindow0 := by constructor <;> decide
    argWindow8 := by constructor <;> decide
    arg0 := by
      have := arg 0 8192#64 (by simp [camlInitGcArgSlots])
      rwa [show nativeFrameBase (parameterStack + 16#64) 16 + 0 = parameterStack.toNat by decide] at this
    arg1 := by
      have := arg 8 2#64 (by simp [camlInitGcArgSlots])
      rwa [show nativeFrameBase (parameterStack + 16#64) 16 + 8 = (parameterStack + 8#64).toNat by decide] at this
    chargedP := ⟨by decide, by decide⟩
    chargedM := ⟨by decide, by decide⟩
    chargedA := ⟨by decide, by decide⟩
    charged1 := ⟨by decide, by decide⟩
    charged2 := ⟨by decide, by decide⟩
    domainOwned := dom'.owned
    idle := dom'.idle
    noYoung := dom'.noYoung
    noHeap := dom'.noHeap
    refs := dom'.refs
    lambdaOff := bss _ 0x80064cf0 0x80064cf8 ⟨by omega, by omega⟩ fun x lo hi => by unfold GcBssByte; omega
    memprofIdle := by
      rw [gc.zero 0x80064b30 fun i hi => by unfold GcBssByte; omega]; rfl
    huge := bss _ 0x80064b08 0x80064b10 ⟨by omega, by omega⟩ fun x lo hi => by unfold GcBssByte; omega
    lists := fun j hj => by
      have addr := smallList_nat j hj 0 (by decide)
      rw [BitVec.add_zero] at addr
      rw [addr]
      exact bss _ 0x800662e8 0x800663e8 ⟨by omega, by omega⟩ fun x lo hi => by unfold GcBssByte; omega
    tree := bss _ 0x800649f0 0x80064a00 ⟨by unfold largeTreeAddr; omega, by unfold largeTreeAddr; omega⟩
      fun x lo hi => by unfold GcBssByte; omega
    least := bss _ 0x800649f0 0x80064a00 ⟨by unfold largeLeastAddr; omega, by unfold largeLeastAddr; omega⟩
      fun x lo hi => by unfold GcBssByte; omega
    curWsz := word_observed _ fun i hi => low _ (by unfold flCurWszAddr heapEnd; omega)
    quiet := by
      have b (i : Nat) (hi : i < 8) : (after.σ.mem[Layout.sym_caml_verb_gc + i]?).getD 0 = 0#8 :=
        gc.bss _ (by unfold GcBssByte Layout.sym_caml_verb_gc; omega)
      exact ⟨by simpa using b 0 (by decide), b 1 (by decide), b 2 (by decide), b 3 (by decide), b 4 (by decide),
        b 5 (by decide), b 6 (by decide), b 7 (by decide)⟩ }⟩

/-- Named obligation: caml_init_domain's record and the minor ref tables
(`DomainKept`) hold when the section table is read. Supplied by an owned-block
frame from `DomainHistory` through every later startup step. -/
def ResetDomainKept_Statement : Prop :=
  ∀ initial sections (w : ResetReadSections initial sections),
    ∃ t1 t2 t3 : BitVec 64, DomainKept w.blocks sections.σ.mem t1 t2 t3

/-- The reset run reaches caml_init_gc's entry with its precondition, given the domain obligation. -/
theorem reset_init_gc_exists (domain : ResetDomainKept_Statement) :
    ∃ initial after H cap c1 c2 cA cM cP, Steps (Vsa.Densify.fillZero initial) after ∧
      ∃ sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur,
        InitGcCall H cap c1 c2 cA cM cP sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t1 t2 t3 cur after := by
  obtain ⟨initial, sections, ⟨w⟩⟩ := reset_read_sections_exists
  obtain ⟨t1, t2, t3, dom⟩ := domain initial sections w
  obtain ⟨after, run, call⟩ := reset_init_gc_call w dom
  exact ⟨initial, after, _, _, _, _, _, _, _, run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, call⟩
end OCaml.Vm.Boot.WhileMinElfParse
