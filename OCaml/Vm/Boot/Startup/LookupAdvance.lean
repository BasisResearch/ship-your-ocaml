import OCaml.Vm.Boot.Startup.LookupBlocks
import OCaml.Vm.Primitives.Read
import OCaml.Vm.Primitives.Control

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions OCaml.Vm.Primitives

def nextLookupIndex (i : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (i + 1#64) 31 0)

def nextLookupAddress (i base : BitVec 64) : BitVec 64 :=
  base + (nextLookupIndex i <<< 3)

theorem lookup_advance_input {c : Config} {i base : BitVec 64} {bytes : List (BitVec 8)}
    (h : LookupReady c) (hi : gprGet c.σ 8 = some i) (hb : gprGet c.σ 18 = some base)
    (window : ReadWindow (nextLookupAddress i base) 8)
    (pins : LPins8 c.σ.mem (nextLookupAddress i base).toNat bytes)
    (nonnull : bytesVal .ld bytes ≠ 0#64) :
    BlockInput caml_build_primitive_tableX4e1cFSeg 0x80024e1c#64
      (caml_build_primitive_tableX4e1cFL i base) [bytes] c where
  good := h.good
  minstret := h.good.minstret
  regs := ⟨hi, hb, True.intro⟩
  keys := by show KeysOK [8, 18]; decide
  shape := by show ChainOK 0x80024e1c#64 [8, 18] caml_build_primitive_tableX4e1cFSeg; decide
  tick := h.tick
  facts := by
    chain_facts h.code with "Vsa.Sim.Code.caml_build_primitive_table_at_"
    · apply window.ld rfl ?_ pins
      change nextLookupAddress i base + 0#64 = nextLookupAddress i base
      exact BitVec.add_zero _
    · change (bytesVal .ld bytes == 0#64) = false
      exact beq_eq_false_iff_ne.mpr nonnull

structure LookupAdvancePost (i value : BitVec 64) (before after : Config) : Prop where
  ready : LookupReady after
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  pc : PCAt 0x80024e30#64 after
  index : gprGet after.σ 8 = some (nextLookupIndex i)
  candidate : gprGet after.σ 11 = some value
  frame : ∀ r, (∀ q ∈ noiseRegs, (q == r) = false) →
    r ≠ .x8 → r ≠ .x11 → r ≠ .x15 → after.σ.regs.get? r = before.σ.regs.get? r

theorem lookup_advance (c : Config) (i base : BitVec 64) (bytes : List (BitVec 8))
    (h : LookupReady c) (hi : gprGet c.σ 8 = some i) (hb : gprGet c.σ 18 = some base)
    (window : ReadWindow (nextLookupAddress i base) 8)
    (pins : LPins8 c.σ.mem (nextLookupAddress i base).toNat bytes)
    (nonnull : bytesVal .ld bytes ≠ 0#64) :
    FnSummary 0x80024e1c#64 (fun d => d = c)
      (LookupAdvancePost i (bytesVal .ld bytes) c) := by
  apply (block_summary _ _ _ _ _ (lookup_advance_input h hi hb window pins nonnull)).weaken (fun _ hc => hc)
  intro d post
  have hm : d.σ.mem = c.σ.mem := post.memory
  have regs := post.regs
  change gprGet d.σ 11 = some (bytesVal .ld bytes) ∧
    gprGet d.σ 15 = some (nextLookupAddress i base) ∧
    gprGet d.σ 8 = some (nextLookupIndex i) ∧ _ at regs
  obtain ⟨candidate, address, index, rest⟩ := regs
  refine ⟨⟨post.good, by rw [hm]; exact h.code, post.tick⟩,
    hm, post.output, post.pc, index, candidate, ?_⟩
  intro r noise h8 h11 h15
  apply post.frame r noise
  change ∀ n ∈ [8, 15, 15, 11], (gprReg n == r) = false
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl
  all_goals simp [gprReg, beq_eq_false_iff_ne, Ne.symm h8, Ne.symm h11, Ne.symm h15]

end OCaml.Vm.Boot.Startup
