import OCaml.Vm.Boot.Startup.PageModifyHashNormalized
import OCaml.Vm.Boot.Startup.PageModifyHashImage
import OCaml.Vm.Boot.Startup.PageModifyHashTailNormalized
import OCaml.Vm.Boot.Startup.PageModifyHashTailImage
import OCaml.Vm.Boot.Startup.PageModifySlotNormalized
import OCaml.Vm.Boot.Startup.PageModifySlotImage
import OCaml.Vm.Boot.Startup.PageModifyUpdateNormalized
import OCaml.Vm.Boot.Startup.PageModifyUpdateImage
import OCaml.Vm.Boot.Startup.PageModifyInsertNormalized
import OCaml.Vm.Boot.Startup.PageModifyInsertImage
import OCaml.Vm.Boot.Startup.PageModifyNextNormalized
import OCaml.Vm.Boot.Startup.PageModifyNextImage
import OCaml.Vm.Boot.Startup.PageModifyStepNormalized
import OCaml.Vm.Boot.Startup.PageModifyStepImage
import OCaml.Vm.Boot.Startup.LinearChain
import OCaml.Vm.Boot.Startup.PageHash
import OCaml.Vm.Boot.Startup.ReadSectionsSteps
import OCaml.Vm.Boot.Startup.PageTable
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_page_table_modify's hash: `(page >> 12) * HASH_FACTOR >> shift`.
The native shift-add chain is evaluated over coefficients (`linRun_sound`);
the factor comes out as `0x9E3779B97F4A7C16`. -/

/-- The page number. -/
def pageNumber (page : BitVec 64) : BitVec 64 := page >>> 12

/-- OCaml's `HASH_FACTOR`. -/
abbrev hashFactor : BitVec 64 := 11400714819323198486#64

theorem srli_page (page : BitVec 64) (a : MInstr) (imm : a.imm = 12#12) :
    Sail.shift_bits_right page (Sail.BitVec.extractLsb (shamtOf a) 5 0) = pageNumber page := by
  rw [shamtOf, imm]
  simp only [Sail.shift_bits_right, pageNumber, BitVec.ushiftRight_eq']
  rfl

theorem hash_coefs_a :
    linRun (caml_page_table_modifyXadf0Seg.flatMap (·.body)).tail [(12, 1#64)] =
      some [(14, 2805824235320#64), (15, 70145605883#64), (12, 1#64)] := by decide

theorem hash_coefs_b :
    linRun (caml_page_table_modifyXae38Seg.flatMap (·.body)) [(14, 2805824235320#64), (15, 70145605883#64), (12, 1#64)] =
      some [(15, hashFactor), (14, 22985312135732255#64), (12, 1#64)] := by decide

/-- The shift-add chain: `a5 = HASH_FACTOR * (page >> 12)`. -/
theorem page_hash_chain (c : Config) (ra page : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, page)]) :
    FnSummary 0x8000adf0#64 (fun e => e = c) (BoundaryPost [12, 14, 15] c ra 0x8000ae70#64
      [(15, hashFactor * pageNumber page), (12, pageNumber page)]) := by
  apply boundary_of_blocks leaf
    (block_summary _ _ _ _ _ (show BlockInput (caml_page_table_modifyXadf0Seg ++ caml_page_table_modifyXae38Seg)
        0x8000adf0#64 [(8, page)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8]; decide
      shape := by change ChainOK _ [8] _; decide
      tick := leaf.tick
      facts := by
        have code := pageModifyHash_code leaf.image
        have code2 := pageModifyHashTail_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_" }))
  · rfl
  · rfl
  · intro σ pins
    have start : LinHolds (pageNumber page) [(12, 1#64)]
        (stepGM (mkLine 0x8000adf0#64 0x00c45613#32) [(8, page)] []) := by
      intro n k hn
      simp only [lookupG] at hn
      split at hn
      · rename_i e; subst e
        simp only [Option.some.injEq] at hn; subst hn
        rw [pagemodifyhash_line_8000adf0]
        simp only [stepGM, wvalM, lookupG, srcVal, ite_true, Option.getD_some]
        rw [srli_page _ _ rfl, BitVec.one_mul]
      · simp at hn
    have afterA := linRun_sound (y := pageNumber page) [] start hash_coefs_a
    have afterB := linRun_sound (y := pageNumber page) [] afterA hash_coefs_b
    have run : (evalBlocks (caml_page_table_modifyXadf0Seg ++ caml_page_table_modifyXae38Seg)
        (SegEvalState.init [(8, page)] [])).regs =
        runGM (caml_page_table_modifyXae38Seg.flatMap (·.body))
          (runGM ((caml_page_table_modifyXadf0Seg.flatMap (·.body)).tail)
            (stepGM (mkLine 0x8000adf0#64 0x00c45613#32) [(8, page)] []) []) [] := rfl
    rw [run] at pins
    exact ⟨gholds_lookup _ pins (afterB 15 _ rfl), gholds_lookup _ pins (by
      rw [afterB 12 _ rfl, BitVec.one_mul]), trivial⟩
  · decide
  · decide

/-- The page's home slot: the top 11 bits of the hash product. -/
def pageHash (page : BitVec 64) : BitVec 64 := (hashFactor * pageNumber page) >>> 53

theorem pageHash_lt (page : BitVec 64) : (pageHash page).toNat < 2048 := by
  unfold pageHash
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (hashFactor * pageNumber page).isLt
  omega

/-- The address of slot `h` of the slots at `ent`. -/
def slotAddr (ent h : BitVec 64) : BitVec 64 := ent + (h <<< 3)

theorem srl_shift (x : BitVec 64) : Sail.shift_bits_right x (Sail.BitVec.extractLsb (53#64) 5 0) = x >>> 53 := by
  simp only [Sail.shift_bits_right, BitVec.ushiftRight_eq']
  rfl

theorem slli_three (x : BitVec 64) (a : MInstr) (imm : a.imm = 3#12) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (shamtOf a) 5 0) = x <<< 3 := by
  rw [shamtOf, imm]
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq']
  rfl

def pageSlotBlocks (empty : Bool) : List BBlock :=
  if empty then caml_page_table_modifyXae70TSeg else caml_page_table_modifyXae70FSeg

local macro "psk" : tactic => `(tactic| simp only [pagemodifyslot_line_8000ae70, pagemodifyslot_line_8000ae74, pagemodifyslot_line_8000ae78, pagemodifyslot_line_8000ae7c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The home slot: load its word; empty goes to the insertion, occupied to the probe loop. -/
theorem page_slot (c : Config) (ra page ent : BitVec 64) (empty : Bool) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, hashFactor * pageNumber page), (18, 53#64), (13, ent)])
    (window : ReadWindow (slotAddr ent (pageHash page)) 8)
    (test : (bytesT c.σ.mem (slotAddr ent (pageHash page)).toNat 8 == 0#64) = empty) :
    FnSummary 0x8000ae70#64 (fun e => e = c) (BoundaryPost [15, 12, 14] c ra
      (if empty then 0x8000aee4#64 else 0x8000ae84#64)
      [(14, bytesT c.σ.mem (slotAddr ent (pageHash page)).toNat 8), (12, slotAddr ent (pageHash page)),
        (15, pageHash page), (18, 53#64), (13, ent)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (slotAddr ent (pageHash page)).toNat) =
      bytesT c.σ.mem (slotAddr ent (pageHash page)).toNat 8 := read8_value _ _
  have input : BlockInput (pageSlotBlocks empty) 0x8000ae70#64
      [(15, hashFactor * pageNumber page), (18, 53#64), (13, ent)]
      [read8 c.σ.mem (slotAddr ent (pageHash page)).toNat] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [15, 18, 13]; decide
    shape := by unfold pageSlotBlocks; split <;> (change ChainOK _ [15, 18, 13] _; decide)
    tick := leaf.tick
    facts := by
      have code := pageModifySlot_code leaf.image
      unfold pageSlotBlocks
      split
      · chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        · refine window.ld rfl ?_ (read8_pins _ _)
          psk
          rw [srl_shift, slli_three _ _ rfl, (show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide),
            BitVec.add_zero]
          rfl
        · rename_i h
          psk; rw [word]; simp only [guardB]; rw [h] at test; exact test
      · chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        · refine window.ld rfl ?_ (read8_pins _ _)
          psk
          rw [srl_shift, slli_three _ _ rfl, (show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide),
            BitVec.add_zero]
          rfl
        · rename_i h
          psk; rw [word]; simp only [guardB]; rw [Bool.not_eq_true] at h; rw [h] at test; exact test }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
    (keys := by unfold pageSlotBlocks; split <;> decide) (no3 := by unfold pageSlotBlocks; split <;> decide)
  · unfold pageSlotBlocks; split <;> rfl
  · unfold pageSlotBlocks; split <;> rfl
  · intro σ pins
    unfold pageSlotBlocks at pins
    split at pins <;>
    · simp only [caml_page_table_modifyXae70TSeg, caml_page_table_modifyXae70FSeg, evalBlocks, evalBlock,
        SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some,
        Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons, List.tail_cons, pagemodifyslot_line_8000ae70,
        pagemodifyslot_line_8000ae74, pagemodifyslot_line_8000ae78, pagemodifyslot_line_8000ae7c] at pins
      rw [srl_shift, slli_three _ _ rfl, word] at pins
      exact pins
  · unfold pageSlotBlocks; split <;> decide
  · decide

theorem next_index (h : Nat) (hh : h < 2048) :
    (BitVec.ofNat 64 h + Functions.sign_extend (m := 64) 1#12) &&& 2047#64 = BitVec.ofNat 64 ((h + 1) % 2048) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (2047#64).toNat = 2 ^ 11 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
    show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  simp only [BitVec.toNat_ofNat]
  omega

def probeStepBlocks (empty : Bool) : List BBlock :=
  caml_page_table_modifyXae9cTSeg ++ if empty then caml_page_table_modifyXae90TSeg else caml_page_table_modifyXae90FSeg

local macro "pqk" : tactic => `(tactic| simp only [pagemodifystep_line_8000ae9c, pagemodifystep_line_8000aea0, pagemodifystep_line_8000aea4, pagemodifystep_line_8000aea8, pagemodifynext_line_8000ae90, pagemodifynext_line_8000ae94, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- One probe past a slot holding another page: advance and load the next slot. -/
theorem page_probe_step (c : Config) (ra page ent e : BitVec 64) (h : Nat) (hh : h < 2048) (empty : Bool)
    (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, BitVec.ofNat 64 h), (14, e), (17, 2047#64), (16, 4096#64), (8, page), (13, ent)])
    (other : guardB bop.BGEU (page ^^^ e) 4096#64 = true)
    (window : ReadWindow (slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))) 8)
    (test : (bytesT c.σ.mem (slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))).toNat 8 == 0#64) = empty) :
    FnSummary 0x8000ae9c#64 (fun d => d = c) (BoundaryPost [15, 11, 10, 12, 14] c ra
      (if empty then 0x8000aee4#64 else 0x8000ae9c#64)
      [(14, bytesT c.σ.mem (slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))).toNat 8),
        (12, slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))), (15, BitVec.ofNat 64 ((h + 1) % 2048)),
        (17, 2047#64), (16, 4096#64), (8, page), (13, ent)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))).toNat) =
      bytesT c.σ.mem (slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))).toNat 8 := read8_value _ _
  have input : BlockInput (probeStepBlocks empty) 0x8000ae9c#64
      [(15, BitVec.ofNat 64 h), (14, e), (17, 2047#64), (16, 4096#64), (8, page), (13, ent)]
      [read8 c.σ.mem (slotAddr ent (BitVec.ofNat 64 ((h + 1) % 2048))).toNat] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [15, 14, 17, 16, 8, 13]; decide
    shape := by unfold probeStepBlocks; split <;> (change ChainOK _ [15, 14, 17, 16, 8, 13] _; decide)
    tick := leaf.tick
    facts := by
      have code := pageModifyStep_code leaf.image
      have code2 := pageModifyNext_code leaf.image
      unfold probeStepBlocks
      split
      all_goals
        rename_i hb
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        · pqk; exact other
        · refine memFacts_writeLog ?_ (fun _ => ?_)
          · refine window.ld rfl ?_ (read8_pins _ _)
            pqk
            rw [next_index h hh, slli_three _ _ rfl, (show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide),
              BitVec.add_zero]
            rfl
          · pqk; simp only [wlogM]; trivial
        · pqk; rw [word]; simp only [guardB]
          first | (rw [hb] at test; exact test) | (rw [Bool.not_eq_true] at hb; rw [hb] at test; exact test) }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
    (keys := by unfold probeStepBlocks; split <;> decide) (no3 := by unfold probeStepBlocks; split <;> decide)
  · unfold probeStepBlocks; split <;> rfl
  · unfold probeStepBlocks; split <;> rfl
  · intro σ pins
    unfold probeStepBlocks at pins
    split at pins <;>
    · simp only [caml_page_table_modifyXae9cTSeg, caml_page_table_modifyXae90TSeg, caml_page_table_modifyXae90FSeg,
        List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
        srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
        List.tail_cons, pagemodifystep_line_8000ae9c, pagemodifystep_line_8000aea0, pagemodifystep_line_8000aea4,
        pagemodifystep_line_8000aea8, pagemodifynext_line_8000ae90, pagemodifynext_line_8000ae94] at pins
      rw [next_index h hh, slli_three _ _ rfl, word] at pins
      exact ⟨gholds_lookup (n := 14) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, gholds_lookup (n := 15) _ pins rfl,
        gholds_lookup (n := 17) _ pins rfl, gholds_lookup (n := 16) _ pins rfl, gholds_lookup (n := 8) _ pins rfl,
        gholds_lookup (n := 13) _ pins rfl, trivial⟩
  · unfold probeStepBlocks; split <;> decide
  · decide

local macro "pik" : tactic => `(tactic| simp only [pagemodifyinsert_line_8000aee4, pagemodifyinsert_line_8000aee8, pagemodifyinsert_line_8000aeec, pagemodifyinsert_line_8000aef0, pagemodifyinsert_line_8000aef4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

theorem occupancy_addr : BitVec.ofNat 64 pageTable + Functions.sign_extend (m := 64) 24#12 =
    BitVec.ofNat 64 (pageTable + 0x18) := by decide

/-- An empty slot: store `page | kind` there and bump the occupancy. -/
theorem page_insert (c : Config) (ra page kind slot occ v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, BitVec.ofNat 64 pageTable), (19, kind), (8, page), (12, slot), (10, v)])
    (window : WriteWindow slot 8) (occWord : bytesT c.σ.mem (pageTable + 0x18) 8 = occ)
    (outside : ImageOutside [(slot.toNat, 8, kind ||| page), (pageTable + 0x18, 8, occ + 1#64)]) :
    FnSummary 0x8000aee4#64 (fun d => d = c) (WriteRegistersPost [15, 8]
      [(slot.toNat, 8, kind ||| page), (pageTable + 0x18, 8, occ + 1#64)] c 0x8000aec0#64 v
      [(15, occ + 1#64), (8, kind ||| page), (9, BitVec.ofNat 64 pageTable), (19, kind), (12, slot), (10, v)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (pageTable + 0x18)) = occ := by rw [read8_value]; exact occWord
  apply registers_of_blocks leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_modifyXaee4Seg 0x8000aee4#64
        [(9, BitVec.ofNat 64 pageTable), (19, kind), (8, page), (12, slot), (10, v)]
        [read8 c.σ.mem (pageTable + 0x18)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 19, 8, 12, 10]; decide
      shape := by change ChainOK _ [9, 19, 8, 12, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageModifyInsert_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 (pageTable + 0x18)) 8 by constructor <;> decide).ld rfl
            (by pik; exact occupancy_addr) (by
              rw [show (BitVec.ofNat 64 (pageTable + 0x18)).toNat = pageTable + 0x18 by decide]
              exact read8_pins _ _)
        · exact window.sd rfl (by pik; rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
            BitVec.add_zero])
        · exact (show WriteWindow (BitVec.ofNat 64 (pageTable + 0x18)) 8 by constructor <;> decide).sd rfl
            (by pik; exact occupancy_addr) }))
  · simp only [caml_page_table_modifyXaee4Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, List.headD_cons, List.tail_cons, pagemodifyinsert_line_8000aee4,
      pagemodifyinsert_line_8000aee8, pagemodifyinsert_line_8000aeec, pagemodifyinsert_line_8000aef0,
      pagemodifyinsert_line_8000aef4]
    rw [word, occupancy_addr, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero,
      show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
      show (BitVec.ofNat 64 (pageTable + 0x18)).toNat = pageTable + 0x18 by decide]
    rfl
  · rfl
  · simp only [caml_page_table_modifyXaee4Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, List.headD_cons, List.tail_cons, pagemodifyinsert_line_8000aee4,
      pagemodifyinsert_line_8000aee8, pagemodifyinsert_line_8000aeec, pagemodifyinsert_line_8000aef0,
      pagemodifyinsert_line_8000aef4]
    rw [word, show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
