import OCaml.Vm.Gc.Generated.Young
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Gc.Invariant

namespace OCaml.Vm.Gc.Young
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Runtime domain fields used by Is_young, expressed only with Layout offsets. -/
structure Windows (domain : BitVec 64) : Prop where
  upper : ReadWindow (domain + BitVec.ofNat 64 Layout.off_young_end) 8
  lower : ReadWindow (domain + BitVec.ofNat 64 Layout.off_young_start) 8

def upperWord (domain : BitVec 64) (c : Config) : BitVec 64 :=
  word c (domain + BitVec.ofNat 64 Layout.off_young_end).toNat
def lowerWord (domain : BitVec 64) (c : Config) : BitVec 64 :=
  word c (domain + BitVec.ofNat 64 Layout.off_young_start).toNat

def above (value domain : BitVec 64) (c : Config) : Bool := guardB .BGEU value (upperWord domain c)
def aboveLower (value domain : BitVec 64) (c : Config) : Bool := guardB .BLTU (lowerWord domain c) value

def loads (domain : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem Layout.sym_Caml_state,
   read8 c.σ.mem (domain + BitVec.ofNat 64 Layout.off_young_end).toNat,
   read8 c.σ.mem (domain + BitVec.ofNat 64 Layout.off_young_start).toNat]

theorem domain_window : ReadWindow (BitVec.ofNat 64 Layout.sym_Caml_state) 8 := by
  constructor <;> decide

theorem upper_access (branch : Bool) {value domain c}
    (root : word c Layout.sym_Caml_state = domain) (windows : Windows domain) :
    AccessPlan c.σ.mem (regs value) (loads domain c) (upperBlock branch).body := by
  have rootBytes : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = domain := by
    rw [read8_value]; exact root
  cases branch <;> simp only [upperBlock, Bool.false_eq_true, ite_false, ite_true,
    caml_oldify_mopupX9d5cTSeg, caml_oldify_mopupX9d5cFSeg, List.getD_cons_zero, AccessPlan]
  all_goals chain_facts True.intro
  all_goals first
    | apply domain_window.ld rfl ?_ (read8_pins _ _)
    | apply windows.upper.ld rfl ?_ (read8_pins _ _)
  all_goals simp [eaddrM, mkLine, decodeM, regs, loads, srcVal, lookupG, eraseG,
    stepGM, stepLdsM, wvalM, rootBytes, Layout.off_young_end,
    Functions.sign_extend, Sail.BitVec.signExtend]

theorem upper_control (value domain : BitVec 64) (c : Config) :
    TermFactsO (runGM (upperBlock (above value domain c)).body (regs value) (loads domain c))
      (upperBlock (above value domain c)).term := by
  generalize choice : above value domain c = branch
  cases branch <;> simpa [above, upperWord, upperBlock, caml_oldify_mopupX9d5cTSeg,
    caml_oldify_mopupX9d5cFSeg, TermFactsO, TermFactsT, runGM, stepGM, regs,
    loads, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    read8_value, word, Functions.sign_extend, Sail.BitVec.signExtend] using choice

theorem lower_access (branch : Bool) (value domain hi : BitVec 64) (c : Config)
    (windows : Windows domain) :
    AccessPlan c.σ.mem (afterUpper value domain hi) (loads domain c).tail.tail
      (lowerBlock branch).body := by
  cases branch <;> simp only [lowerBlock, Bool.false_eq_true, ite_false, ite_true,
    caml_oldify_mopupX9d68TSeg, caml_oldify_mopupX9d68FSeg, List.getD_cons_zero, AccessPlan]
  all_goals chain_facts True.intro
  all_goals apply windows.lower.ld rfl ?_ (read8_pins _ _)
  all_goals simp [eaddrM, mkLine, decodeM, afterUpper, srcVal, lookupG,
    Layout.off_young_start, Functions.sign_extend, Sail.BitVec.signExtend]

theorem lower_control (value domain hi : BitVec 64) (c : Config) :
    TermFactsO (runGM (lowerBlock (aboveLower value domain c)).body (afterUpper value domain hi)
      (loads domain c).tail.tail) (lowerBlock (aboveLower value domain c)).term := by
  generalize choice : aboveLower value domain c = branch
  cases branch <;> simpa [aboveLower, lowerWord, lowerBlock, caml_oldify_mopupX9d68TSeg,
    caml_oldify_mopupX9d68FSeg, TermFactsO, TermFactsT, runGM, stepGM, afterUpper,
    loads, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
    read8_value, word, Functions.sign_extend, Sail.BitVec.signExtend] using choice

theorem access {value domain c} (root : word c Layout.sym_Caml_state = domain)
    (windows : Windows domain) : ChainAccess c.σ.mem (regs value) (loads domain c)
      (blocks (above value domain c) (aboveLower value domain c)) := by
  have upper := upper_control value domain c
  generalize choice : above value domain c = branch at upper ⊢
  cases branch
  · apply ChainAccess.cons ⟨upper_access false root windows, upper⟩
    rw [upper_log, upper_regs, upper_loads]
    have rootBytes : bytesVal .ld ((loads domain c).headD []) = domain := by
      change bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = _
      rw [read8_value]; exact root
    rw [rootBytes]
    exact ChainAccess.cons ⟨lower_access _ _ _ _ _ windows, lower_control _ _ _ _⟩ ChainAccess.nil
  · exact ChainAccess.cons ⟨upper_access true root windows, upper⟩ ChainAccess.nil

/-- Concrete input for the untagged-word range classifier; parity is checked
by its caller. Runtime state and total field reads supply both bounds. -/
structure Input (value domain : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ (regs value)
  root : word c Layout.sym_Caml_state = domain
  windows : Windows domain

/-- Exact classifier effects, with the runtime's strict lower bound retained. -/
structure Result (value domain : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (blocks (above value domain before) (aboveLower value domain before)) pc
    (regs value) (loads domain before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (if (lowerWord domain before).toNat < value.toNat ∧
      value.toNat < (upperWord domain before).toNat then oldifyPc else copyPc) after
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem decision (value domain : BitVec 64) (c : Config) :
    (!above value domain c && aboveLower value domain c) =
      decide ((lowerWord domain c).toNat < value.toNat ∧ value.toNat < (upperWord domain c).toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [above, aboveLower, guardB, Functions.zopz0zKzJ_u, Functions.zopz0zI_u,
    Sail.BitVec.toNatInt]
  omega

/-- Reflected code and scalar-access certificates for an Is_young site.
The first-field and suffix classifiers differ in code addresses but share
runtime observations, decision semantics and the machine-summary fold. -/
structure Site where
  entry : BitVec 64
  copy : BitVec 64
  oldify : BitVec 64
  blocks : Bool → Bool → List BBlock
  code : ∀ upper lower {mem}, Code.Caml_oldify_mopupLoaded mem → ChainCode mem (blocks upper lower)
  shape : ∀ upper lower, ChainOK entry [22,10] (blocks upper lower)
  access : ∀ {value domain c}, word c Layout.sym_Caml_state = domain → Windows domain →
    ChainAccess c.σ.mem (regs value) (loads domain c) (blocks (above value domain c) (aboveLower value domain c))
  log : ∀ upper lower value lds,
    (evalBlocks (blocks upper lower) (SegEvalState.init (regs value) lds)).log = []
  endpoint : ∀ upper lower value lds,
    evalBlocksPC entry (SegEvalState.init (regs value) lds) (blocks upper lower) =
      if !upper && lower then oldify else copy

structure SiteResult (site : Site) (value domain : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (site.blocks (above value domain before) (aboveLower value domain before)) site.entry
    (regs value) (loads domain before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (if (lowerWord domain before).toNat < value.toNat ∧
      value.toNat < (upperWord domain before).toNat then site.oldify else site.copy) after
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem classify_site (site : Site) {value domain c} (input : Input value domain c) :
    FnSummary site.entry (fun d => d = c) (SiteResult site value domain c) := by
  have summary := block_summary (site.blocks (above value domain c) (aboveLower value domain c)) site.entry
    (regs value) (loads domain c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [22,10]; decide,
      chainPlan_facts (site.code _ _ input.code) (site.access input.root input.windows),
      site.shape _ _, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, site.log]; rfl
  refine ⟨post, memory, ?_, memory ▸ input.code⟩
  rw [PCAt, post.pc, site.endpoint, decision]
  simp only [decide_eq_true_eq]

/-- The suffix-field site's generated certificates. -/
def suffixSite : Site :=
  ⟨pc, copyPc, oldifyPc, blocks, code_facts, chain_ok, access, no_writes, end_pc⟩

theorem classify {value domain c} (input : Input value domain c) :
    FnSummary pc (fun d => d = c) (Result value domain c) := by
  apply (classify_site suffixSite input).weaken (fun _ h => h)
  intro after post
  exact ⟨post.machine, post.memory, post.pc, post.code⟩

/-- Both nursery endpoints are excluded by the real Is_young classifier. -/
theorem decision_at_start (domain : BitVec 64) (c : Config) :
    (!above (lowerWord domain c) domain c && aboveLower (lowerWord domain c) domain c) = false := by
  rw [decision]; simp

theorem decision_at_end (domain : BitVec 64) (c : Config) :
    (!above (upperWord domain c) domain c && aboveLower (upperWord domain c) domain c) = false := by
  rw [decision]; simp

/-- The existing NoForgery invariant uses a conservative half-open range.
It therefore excludes this stricter classifier for every even nonpointer. -/
theorem nonpointer_outside {P s pl lo hi v w}
    (safe : NoForgery P s pl lo hi) (scanned : Scanned P s v)
    (nonpointer : v.loc? = none) (represented : valWord pl v = some w)
    (even : w.toNat % 2 = 0) : ¬ (lo < w.toNat ∧ w.toNat < hi) := by
  intro bounds
  exact safe v w scanned nonpointer represented ⟨even, Nat.le_of_lt bounds.1, bounds.2⟩

/-- The represented nonpointer case follows the concrete copy continuation,
using NoForgery rather than assuming a convenient branch result. -/
theorem Result.copy_nonpointer {value domain before after P s pl v}
    (post : Result value domain before after)
    (safe : NoForgery P s pl (lowerWord domain before).toNat (upperWord domain before).toNat)
    (scanned : Scanned P s v) (nonpointer : v.loc? = none)
    (represented : valWord pl v = some value) (even : value.toNat % 2 = 0) :
    PCAt copyPc after := by
  simpa only [ite_eq_right (nonpointer_outside safe scanned nonpointer represented even)] using post.pc

end OCaml.Vm.Gc.Young
