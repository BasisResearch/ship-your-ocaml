import OCaml.Vm.Boot.Startup.StrdupPrefixNormalized
import OCaml.Vm.Boot.Startup.StrdupPrefixCallInterface
import OCaml.Vm.Boot.Startup.LibraryText
import OCaml.Vm.Boot.Startup.RuntimeStack
import OCaml.Vm.Boot.Startup.MallocReturn
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.LibraryStrlenCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.Sym VsaIris.MallocFast
  LeanRV64DExecutable OCaml.Vm.Primitives

/-- A library call that leaves memory unchanged and the global pointer intact
keeps startup readiness. -/
theorem RuntimeReady.of_same_memory {H capacity sp ra oldsp oldra before after}
    (ready : RuntimeReady H capacity oldsp oldra before) (leaf : LeafInput ra after)
    (good : VsaOk startupLive after) (memory : Vsa.Densify.MemEqv after.σ.mem before.σ.mem)
    (globalPointer : gpr after 3 = gpr before 3) (stack : gprGet after.σ 2 = some sp) :
    RuntimeReady H capacity sp ra after := by
  have same : (vsaModel startupLive).mem after = (vsaModel startupLive).mem before := by
    funext a
    exact memory a
  refine ⟨leaf, good, ?_, ?_, stack, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro p hp
      simp only [roR, List.mem_singleton] at hp
      subst hp
      have := ready.readOnly.1 (gp, gpV) (by simp [roR])
      change vsaReg after 3 = gpV
      change vsaReg before 3 = gpV at this
      rw [vsaReg_gpr (by decide)] at this ⊢
      change (gpr after 3).getD 0 = gpV
      rw [globalPointer]; exact this
    · intro p hp
      have := ready.readOnly.2 p hp
      change (vsaModel startupLive).mem after p.1 = p.2
      rw [same]; exact this
  · rw [same]; exact ready.room
  · rw [word_observed (m := before.σ.mem) _ (fun i _ => memory _)]
    exact ready.domainWord
  · exact lpins8_observed ready.poolZero (fun i _ => memory _)

theorem snp_text_live : ∀ p ∈ snpText, startupLive p.1 := by
  apply forall_piecesText (P := fun a _ => startupLive a)
  intro q hq a ha
  simp only [snpPieces, List.mem_singleton] at hq
  subst hq
  obtain ⟨r, hr, low, high⟩ := inRangesB_iff.1 ha
  have bounds : ∀ r ∈ snpCodeRanges, Vsa.Densify.ramBase ≤ r.1 ∧
      r.2 ≤ Vsa.Densify.ramBase + Vsa.Densify.ramSize := by decide
  have := bounds r hr
  exact ⟨by omega, by omega⟩

def strdupLog (sp ra s0 s1 : BitVec 64) : List WEntry := nativeWordLog sp 48 [(40, ra), (24, s1), (32, s0)]
def strdupInput (sp ra s0 s1 name : BitVec 64) : GRegs := [(2, sp), (1, ra), (9, s1), (8, s0), (10, name)]
def strdupPrefixRegs (sp ra s0 name : BitVec 64) : GRegs :=
  [(9, name), (2, nativeStack sp 48), (1, ra), (8, s0), (10, name)]
def strdupStrlenArgs (sp s0 name : BitVec 64) : GRegs :=
  [(9, name), (2, nativeStack sp 48), (8, s0), (10, name)]

theorem strdupLog_inside {sp ra s0 s1} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (strdupLog sp ra s0 s1) := by
  apply frame.word_log_inside
  intro off value member
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

/-- caml_stat_strdup's prologue and its call of strlen on the source string. -/
theorem strdup_prefix (c : Config) (sp ra s0 s1 name : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ (strdupInput sp ra s0 s1 name)) :
    FnSummary 0x8000bdf4#64 (fun d => d = c)
      (WriteRegistersPost [2, 9, 1] (strdupLog sp ra s0 s1) c jal_8000be08_call.target name
        ((1, jal_8000be08_call.link) :: strdupStrlenArgs sp s0 name)) := by
  have front : FnSummary 0x8000bdf4#64 (fun d => d = c)
      (WriteRegistersPost [2, 9] (strdupLog sp ra s0 s1) c jal_8000be08_call.pc name
        (strdupPrefixRegs sp ra s0 name)) := by
    apply registers_of_blocks leaf.image (frame.image_outside (strdupLog_inside frame))
      (block_summary _ _ _ _ _ (show BlockInput strdupPrefixSave 0x8000bdf4#64 (strdupInput sp ra s0 s1 name) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [2, 1, 9, 8, 10]; decide
        shape := by change ChainOK _ [2, 1, 9, 8, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := strdupPrefix_code leaf.image
          have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
              WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
            rw [nativeStack, frame.address _ (by omega)]
            exact frame.word bound aligned
          chain_facts code with "Vsa.Sim.Code.caml_stat_strdup_at_"
          · exact (slot 40 (by decide) (by decide)).sd rfl rfl
          · exact (slot 24 (by decide) (by decide)).sd rfl rfl
          · exact (slot 32 (by decide) (by decide)).sd rfl rfl }))
    · rfl
    · rfl
    · change [(9, name + 0#64), (2, nativeStack sp 48), (1, ra), (8, s0), (10, name)] = _
      rw [BitVec.add_zero]
      rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  have args : GHolds request.σ (strdupStrlenArgs sp s0 name) :=
    holds_project setup.regs (by simp [strdupStrlenArgs, strdupPrefixRegs, lookupG])
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_8000be08_call_shape jal_8000be08_call_decode request
    (jal_8000be08_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ args
    (by change KeysOK [9, 2, 8, 10]; decide) (by simp only [KeysAvoidRa, strdupStrlenArgs, keysG]; decide)
    (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.Sym VsaIris.MallocFast
  OCaml.Vm.Primitives

/-- A NUL-terminated string at `a` of length `len` in total-byte memory. -/
structure CBytes (m : Vsa.MemRepr.Mem) (a len : Nat) : Prop where
  nz : ∀ i, i < len → imgM m (a + i) ≠ 0
  nul : imgM m (a + len) = 0
  lo : 0x80000000 ≤ a
  hi : a + len + 8 ≤ 0x100000000
  htif : a + len + 8 ≤ 0x80061fc0 ∨ 0x80061fc8 ≤ a

theorem CBytes.read {m : Vsa.MemRepr.Mem} {a len : Nat} (h : CBytes m a len) :
    StrRead m (List.range' a (len + 1)) (fun _ => False) m a len (imgM m) where
  win := fun x low high => Or.inl ⟨List.mem_range'_1.2 ⟨low, by omega⟩, rfl⟩
  nz := h.nz
  nul := h.nul
  lo := h.lo
  hi := h.hi
  htif := h.htif

theorem CBytes.transport {m m' : Vsa.MemRepr.Mem} {a len : Nat} (h : CBytes m a len)
    (same : ∀ i, i ≤ len → imgM m' (a + i) = imgM m (a + i)) : CBytes m' a len where
  nz := fun i hi => by rw [same i (by omega)]; exact h.nz i hi
  nul := by rw [same len (Nat.le_refl _)]; exact h.nul
  lo := h.lo
  hi := h.hi
  htif := h.htif

structure StrdupMeasured (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 name : BitVec 64) (len : Nat)
    (before after : Config) where
  entered : Config
  opening : WriteRegistersPost [2, 9, 1] (strdupLog sp ra s0 s1) before jal_8000be08_call.target name
    ((1, jal_8000be08_call.link) :: strdupStrlenArgs sp s0 name) entered
  measured : StrlenCallPost startupLive jal_8000be08_call.link len entered after
  ready : RuntimeReady H capacity (nativeStack sp 48) jal_8000be08_call.link after

/-- caml_stat_strdup up to the return of strlen. -/
theorem strdup_measure (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra s0 s1 name : BitVec 64)
    (len : Nat) (ready : RuntimeReady H capacity sp ra c) (frame : NativeFrame sp 48)
    (saved : GHolds c.σ [(9, s1), (8, s0), (10, name)])
    (string : CBytes c.σ.mem name.toNat len)
    (outside : name.toNat + len + 1 ≤ nativeFrameBase sp 48 ∨ sp.toNat ≤ name.toNat) :
    FnSummary 0x8000bdf4#64 (fun d => d = c)
      (fun after => Nonempty (StrdupMeasured H capacity sp ra s0 s1 name len c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨entered, run1, opening⟩ := (strdup_prefix c sp ra s0 s1 name ready.toLeafInput frame
    ⟨ready.stack, ready.raReg, saved.1, saved.2.1, saved.2.2.1, trivial⟩).run c ⟨pc, rfl⟩
  have readyE := ready.stack_log opening (by decide) (by simp only [strdupStrlenArgs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ opening.regs (by rfl)) (gholds_lookup (n := 1) _ opening.regs (by rfl)) (by decide)
    frame (strdupLog_inside frame)
  have stringE : CBytes entered.σ.mem name.toNat len := string.transport (fun i hi => by
    change (entered.σ.mem[name.toNat + i]?).getD 0 = (c.σ.mem[name.toNat + i]?).getD 0
    have lower := frame.lower
    rw [opening.memory, frameOn_writeLog _ _ _ (strdupLog_inside frame) _ ⟨?_, trivial⟩]
    rcases outside with below | above
    · exact Or.inl (by dsimp only; omega)
    · exact Or.inr (by dsimp only; omega))
  have readOnly : ROHolds (vsaModel startupLive) entered roR
      (snpText ++ dataOf entered.σ.mem (List.range' name.toNat (len + 1))) := by
    refine ⟨readyE.readOnly.1, ?_⟩
    intro p hp
    rcases List.mem_append.1 hp with snp | data
    · change (entered.σ.mem[p.1]?).getD 0 = p.2
      rw [snp_text_loaded readyE.image p snp]; rfl
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 data
      rfl
  have nameBound : name.toNat < 2^64 := name.isLt
  obtain ⟨after, run2, measured⟩ := (strlen_call entered snp_text_live stringE.read readyE.platform readyE.image
    startup_image_live readOnly (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gholds_lookup (n := 10) _ opening.regs (by rfl))
    (gholds_lookup (n := 1) _ opening.regs (by rfl)) (by decide)).run entered ⟨opening.pc, rfl⟩
  have readyM := readyE.of_same_memory measured.toLeafInput measured.libraryGood measured.memory
    (measured.registers 3 (by decide) (by decide) (by decide))
    ((measured.registers 2 (by decide) (by decide) (by decide)).trans readyE.stack)
  exact ⟨after, run1.trans run2, ⟨entered, opening, measured, readyM⟩⟩
end OCaml.Vm.Boot.Startup
