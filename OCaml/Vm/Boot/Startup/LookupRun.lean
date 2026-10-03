import OCaml.Vm.Boot.Startup.LookupEndpoints

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives

/-- Successful builtin primitive lookup, before the outer table insertion. -/
structure LookupFound (function : BitVec 64) (before after : Config) : Prop where
  ready : LookupReady after
  pc : PCAt 0x80024e4c#64 after
  result : gprGet after.σ 11 = some function
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r, NotWrittenStrcmp r → r ≠ .x1 → r ≠ .x8 →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- The entire inner primitive lookup: first pointer load, arbitrary-length strcmp
scan, final match and function-pointer load. The table assumptions are memory
facts only; every machine run comes from generated blocks or the library spec. -/
theorem lookup_run (c : Config) (required namesBase functionsBase function : BitVec 64)
    (name : String) (pointers : Nat → BitVec 64) (names : Nat → String) (target : Nat)
    (ready : LookupReady c)
    (table : NameTable required namesBase name pointers names target c.σ.mem)
    (requiredReg : gprGet c.σ 9 = some required)
    (namesReg : gprGet c.σ 18 = some namesBase)
    (functionsReg : gprGet c.σ 20 = some functionsBase)
    (firstWindow : ReadWindow namesBase 8)
    (firstValue : bytesVal .ld (read8 c.σ.mem namesBase.toNat) = pointers 0)
    (functionWindow : ReadWindow (lookupFunctionAddress (BitVec.ofNat 64 target) functionsBase) 8)
    (functionValue : bytesVal .ld
      (read8 c.σ.mem (lookupFunctionAddress (BitVec.ofNat 64 target) functionsBase).toNat) = function)
    (nonnull : function ≠ 0#64) :
    FnSummary 0x80024e0c#64 (fun d => d = c) (LookupFound function c) := by
  constructor
  rintro d ⟨pc, eq⟩
  subst d
  obtain ⟨start, startRun, sp⟩ := (block_summary _ _ _ _ _
    (lookup_start_input ready namesReg firstWindow (read8_pins _ _)
      (by rw [firstValue]; exact table.nonnull 0 (Nat.zero_le _)))).run c ⟨pc, rfl⟩
  have sm : start.σ.mem = c.σ.mem := sp.memory
  have sr := sp.regs
  change gprGet start.σ 8 = some 0#64 ∧
    gprGet start.σ 11 = some (bytesVal .ld (read8 c.σ.mem namesBase.toNat)) ∧ _ at sr
  obtain ⟨si, sc, rest⟩ := sr
  have startAt : LookupAt required namesBase pointers target 0 c start := {
    ready := ⟨sp.good, by rw [sm]; exact ready.code, sp.tick⟩,
    bound := Nat.zero_le _, pc := sp.pc, index := si,
    requiredReg := (sp.frame .x9 (by decide) (by decide)).trans requiredReg,
    baseReg := (sp.frame .x18 (by decide) (by decide)).trans namesReg,
    candidate := by simpa only [firstValue] using sc,
    memory := sm, output := sp.output,
    frame := by
      intro r hr h1 h8
      apply sp.frame r (strcmp_frame_noise hr)
      have h11 : (.x11 == r) = false := by simp_all [NotWrittenStrcmp]
      change ∀ n ∈ [11, 8], (gprReg n == r) = false
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact h11
      · exact beq_eq_false_iff_ne.mpr (Ne.symm h8) }
  obtain ⟨matchState, scanRun, atMatch⟩ := lookup_loop table start startAt
  have strings : NameMemory required (pointers target) name (names target) matchState.σ.mem := by
    rw [atMatch.memory]; exact table.strings target (Nat.le_refl _)
  obtain ⟨found, matchRun, matchPost⟩ := (lookup_head matchState required (pointers target) name
    (names target) atMatch.ready strings atMatch.requiredReg atMatch.candidate).run matchState
      ⟨atMatch.pc, rfl⟩
  have fm : found.σ.mem = c.σ.mem := matchPost.memory.trans atMatch.memory
  have fi : gprGet found.σ 8 = some (BitVec.ofNat 64 target) :=
    (matchPost.frame .x8 (by decide) (by decide)).trans atMatch.index
  have fb : gprGet found.σ 20 = some functionsBase :=
    (matchPost.frame .x20 (by decide) (by decide)).trans
      ((atMatch.frame .x20 (by decide) (by decide) (by decide)).trans functionsReg)
  let bytes := read8 found.σ.mem (lookupFunctionAddress (BitVec.ofNat 64 target) functionsBase).toNat
  have fv : bytesVal .ld bytes = function := by dsimp [bytes]; rw [fm]; exact functionValue
  obtain ⟨after, finishRun, post⟩ := (block_summary _ _ _ _ _
    (lookup_finish_input matchPost.ready fi fb functionWindow (read8_pins _ _)
      (by rw [fv]; exact nonnull))).run found
        ⟨by simpa [table.matchAt] using matchPost.pc, rfl⟩
  have am : after.σ.mem = found.σ.mem := post.memory
  have regs := post.regs
  change gprGet after.σ 11 = some (bytesVal .ld bytes) ∧ _ at regs
  refine ⟨after, startRun.trans (scanRun.trans (matchRun.trans finishRun)),
    ⟨⟨post.good, by rw [am]; exact matchPost.ready.code, post.tick⟩, post.pc,
      by simpa only [fv] using regs.1, am.trans fm,
      post.output.trans (matchPost.output.trans atMatch.output), ?_⟩⟩
  intro r hr h1 h8
  have lastFrame : after.σ.regs.get? r = found.σ.regs.get? r := by
    apply post.frame r (strcmp_frame_noise hr)
    have h11 : (.x11 == r) = false := by simp_all [NotWrittenStrcmp]
    change ∀ n ∈ [8, 8, 11], (gprReg n == r) = false
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact beq_eq_false_iff_ne.mpr (Ne.symm h8)
    · exact beq_eq_false_iff_ne.mpr (Ne.symm h8)
    · exact h11
  exact lastFrame.trans ((matchPost.frame r hr h1).trans (atMatch.frame r hr h1 h8))

end OCaml.Vm.Boot.Startup
