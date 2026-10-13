import OCaml.Vm.Boot.Startup.PageModifyHashNormalized
import OCaml.Vm.Boot.Startup.PageModifyHashImage
import OCaml.Vm.Boot.Startup.PageModifyHashTailNormalized
import OCaml.Vm.Boot.Startup.PageModifyHashTailImage
import OCaml.Vm.Boot.Startup.PageModifySlotNormalized
import OCaml.Vm.Boot.Startup.PageModifySlotImage
import OCaml.Vm.Boot.Startup.PageModifyReturnNormalized
import OCaml.Vm.Boot.Startup.PageModifyReturnImage
import OCaml.Vm.Boot.Startup.PageModifyEntryNormalized
import OCaml.Vm.Boot.Startup.PageModifyEntryImage
import OCaml.Vm.Boot.Startup.PageModifyProbeNormalized
import OCaml.Vm.Boot.Startup.PageModifyProbeImage
import OCaml.Vm.Boot.Startup.PageModifyShiftNormalized
import OCaml.Vm.Boot.Startup.PageModifyShiftImage
import OCaml.Vm.Boot.Startup.PageModifyLoadNormalized
import OCaml.Vm.Boot.Startup.PageModifyLoadImage
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
import Vsa.Sim.DeriveLoop
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

theorem slli_one (x : BitVec 64) (a : MInstr) (imm : a.imm = 1#12) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (shamtOf a) 5 0) = x <<< 1 := by
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

/-- A boundary over fewer written registers is one over more. -/
theorem BoundaryPost.widen {w w' before ra pc regs after} (h : BoundaryPost w before ra pc regs after)
    (sub : ∀ n ∈ w, n ∈ w') : BoundaryPost w' before ra pc regs after :=
  { h with frame := fun r hr hn => h.frame r (fun n hn' => hr n (sub n hn')) hn }

/-- The registers the probe loop writes. -/
abbrev probeWrites : List Nat := [15, 11, 10, 12, 14]

/-- Slot `i`'s word, read through the native address. -/
def slotWord (m : Std.ExtHashMap Nat (BitVec 8)) (ent : BitVec 64) (i : Nat) : BitVec 64 :=
  bytesT m (slotAddr ent (BitVec.ofNat 64 i)).toNat 8

/-- The probe loop's head after `j` occupied probes from the home slot `h₀`. -/
structure ProbeAt (start : Config) (ra page ent : BitVec 64) (h₀ j : Nat) (d : Config) : Prop where
  post : BoundaryPost probeWrites start ra 0x8000ae9c#64
    [(15, BitVec.ofNat 64 (probe h₀ j)), (14, slotWord start.σ.mem ent (probe h₀ j)), (17, 2047#64),
      (16, 4096#64), (8, page), (13, ent)] d
  occupied : ∀ i, i ≤ j → slotWord start.σ.mem ent (probe h₀ i) ≠ 0#64

/-- The loop's exit: an empty slot `i` on the probe path. -/
structure ProbeFound (start : Config) (ra page ent : BitVec 64) (h₀ slot steps : Nat) (d : Config) : Prop where
  at_slot : slot = probe h₀ steps
  post : BoundaryPost probeWrites start ra 0x8000aee4#64
    [(12, slotAddr ent (BitVec.ofNat 64 slot)), (8, page), (13, ent)] d
  empty : slotWord start.σ.mem ent slot = 0#64
  occupied : ∀ i, i < steps → slotWord start.σ.mem ent (probe h₀ i) ≠ 0#64

theorem probe_lt (h j : Nat) : probe h j < 2048 := by unfold probe; omega

theorem page_probe_loop (start : Config) (ra page ent : BitVec 64) (h₀ e : Nat) (hh : h₀ < 2048) (he : e < 2048)
    (hole : slotWord start.σ.mem ent e = 0#64)
    (windows : ∀ i, i < 2048 → ReadWindow (slotAddr ent (BitVec.ofNat 64 i)) 8)
    (absent : ∀ i, i < 2048 → slotWord start.σ.mem ent i ≠ 0#64 →
      guardB bop.BGEU (page ^^^ slotWord start.σ.mem ent i) 4096#64 = true)
    (d : Config) (P : ProbeAt start ra page ent h₀ 0 d) :
    ∃ f slot steps, Steps d f ∧ ProbeFound start ra page ent h₀ slot steps f := by
  have dist := probe_distance (h := h₀) he
  have distLt := probeDistance_lt h₀ e
  -- the loop at its head never reaches the hole
  have below (j : Nat) (occ : ∀ i, i ≤ j → slotWord start.σ.mem ent (probe h₀ i) ≠ 0#64) :
      j < probeDistance h₀ e := by
    apply Classical.byContradiction
    intro ge
    exact occ (probeDistance h₀ e) (by omega) (by rw [dist]; exact hole)
  let head : BitVec 64 := 0x8000ae9c#64
  let I : Config → Prop := fun c => (∃ j, ProbeAt start ra page ent h₀ j c) ∨
    (∃ slot steps, ProbeFound start ra page ent h₀ slot steps c)
  let B : Config → Prop := fun c => c.σ.regs.get? Register.PC = some head
  let μ : Config → Nat := fun c => if c.σ.regs.get? Register.PC = some head then
    probeDistance h₀ e - (((gprGet c.σ 15).getD 0).toNat + 2048 - h₀) % 2048 else 0
  have index (j : Nat) (hj : j < 2048) : ((BitVec.ofNat 64 (probe h₀ j)).toNat + 2048 - h₀) % 2048 = j := by
    have small : probe h₀ j < 2 ^ 64 := Nat.lt_of_lt_of_le (probe_lt h₀ j) (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    unfold probe; omega
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ μ c = n) (fun c => I c ∧ μ c < n) := by
    intro n c ⟨inv, atHead, measure⟩
    rcases inv with ⟨j, P⟩ | ⟨slot, steps, F⟩
    · have jd := below j P.occupied
      have hm : c.σ.mem = start.σ.mem := P.post.memory
      have pc : PCAt 0x8000ae9c#64 c := P.post.pc
      have next : (probe h₀ j + 1) % 2048 = probe h₀ (j + 1) := probe_next h₀ j
      let empty := slotWord start.σ.mem ent (probe h₀ (j + 1)) == 0#64
      obtain ⟨d', run, step⟩ := (page_probe_step c ra page ent (slotWord start.σ.mem ent (probe h₀ j)) (probe h₀ j)
        (probe_lt h₀ j) empty P.post.toLeafInput P.post.regs
        (absent _ (probe_lt h₀ j) (P.occupied j (Nat.le_refl j)))
        (by rw [next]; exact windows _ (probe_lt h₀ (j + 1)))
        (by rw [hm, next]; rfl)).run c ⟨pc, rfl⟩
      have joined := P.post.then (BoundaryPost.widen step (by decide))
      rw [next, hm] at joined
      have μc : μ c = probeDistance h₀ e - j := by
        have pcc : c.σ.regs.get? Register.PC = some head := atHead
        simp only [μ, pcc, ite_true, gholds_lookup (n := 15) _ P.post.regs rfl, Option.getD_some,
          index j (by omega)]
      by_cases isEmpty : slotWord start.σ.mem ent (probe h₀ (j + 1)) = 0#64
      · have et : empty = true := by simp [empty, isEmpty]
        refine ⟨d', run, Or.inr ⟨probe h₀ (j + 1), j + 1, {
          at_slot := rfl
          post := (by rw [et] at joined; exact joined.select (fun n v mem => by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at mem
            rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl))
          empty := isEmpty
          occupied := fun i hi => P.occupied i (by omega) }⟩, ?_⟩
        have pcd : d'.σ.regs.get? Register.PC ≠ some head := by
          rw [show d'.σ.regs.get? Register.PC = some 0x8000aee4#64 by
            have := step.pc; rw [et] at this; exact this]
          decide
        simp only [μ, pcd, ite_false]
        omega
      · have ef : empty = false := by simp [empty, isEmpty]
        have jd' : j + 1 < probeDistance h₀ e := by
          rcases Nat.lt_or_ge (j + 1) (probeDistance h₀ e) with lt | ge
          · exact lt
          · exfalso
            have eq : j + 1 = probeDistance h₀ e := by omega
            exact isEmpty (by rw [eq, dist]; exact hole)
        have post' : BoundaryPost probeWrites start ra 0x8000ae9c#64
            [(15, BitVec.ofNat 64 (probe h₀ (j + 1))), (14, slotWord start.σ.mem ent (probe h₀ (j + 1))),
              (17, 2047#64), (16, 4096#64), (8, page), (13, ent)] d' := by
          rw [ef] at joined
          exact joined.select (fun n v mem => by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at mem
            rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
        refine ⟨d', run, Or.inl ⟨j + 1, {
          post := post'
          occupied := fun i hi => by
            rcases Nat.lt_or_ge i (j + 1) with lt | ge
            · exact P.occupied i (by omega)
            · rw [show i = j + 1 by omega]; exact isEmpty }⟩, ?_⟩
        have pcd : d'.σ.regs.get? Register.PC = some head := post'.pc
        simp only [μ, pcd, ite_true, gholds_lookup (n := 15) _ post'.regs rfl, Option.getD_some,
          index (j + 1) (by omega)]
        rw [← measure, μc]
        omega
    · exfalso
      have pcf : c.σ.regs.get? Register.PC = some 0x8000aee4#64 := F.post.pc
      have : c.σ.regs.get? Register.PC = some head := atHead
      rw [pcf] at this
      exact absurd this (by decide)
  obtain ⟨f, run, inv, notHead⟩ := loopFromBody μ body d (Or.inl ⟨0, P⟩)
  rcases inv with ⟨j, P'⟩ | ⟨slot, steps, F⟩
  · exact absurd P'.post.pc notHead
  · exact ⟨f, slot, steps, run, F⟩

local macro "plk2" : tactic => `(tactic| simp only [pagemodifyload_line_8000adc0, pagemodifyload_line_8000adc4, pagemodifyload_line_8000adc8, pagemodifyload_line_8000adcc, pagemodifyload_line_8000add0, pagemodifyload_line_8000add4, pagemodifyload_line_8000add8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

theorem page_record_base (i : MInstr) (w : i.word = 382103#32) :
    2147528128#64 + Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) + Functions.sign_extend (m := 64) 1784#12 =
      BitVec.ofNat 64 pageTable := by
  rw [imm20Of, w]; decide

theorem page_record_base' : 2147528128#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 382103#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1784#12 = BitVec.ofNat 64 pageTable := by decide

theorem page_record_field (off : Nat) (imm : BitVec 12) (h : Functions.sign_extend (m := 64) imm = BitVec.ofNat 64 off)
    (small : pageTable + off < 2 ^ 64) :
    BitVec.ofNat 64 pageTable + Functions.sign_extend (m := 64) imm = BitVec.ofNat 64 (pageTable + off) := by
  rw [h, ← BitVec.ofNat_add]

/-- Load the record: occupancy, size and entries; `a0 = 2 * occupancy`. -/
theorem page_record_load (c : Config) (ra page occ size ent : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, page)])
    (occWord : bytesT c.σ.mem (pageTable + 0x18) 8 = occ) (sizeWord : bytesT c.σ.mem (pageTable + 0) 8 = size)
    (entWord : bytesT c.σ.mem (pageTable + 0x20) 8 = ent) :
    FnSummary 0x8000adc0#64 (fun d => d = c) (BoundaryPost [9, 14, 15, 8, 10, 13] c ra 0x8000addc#64
      [(13, ent), (10, occ <<< 1), (8, page), (15, size), (14, occ), (9, BitVec.ofNat 64 pageTable)]) := by
  have base (i : MInstr) (w : i.word = 382103#32) := page_record_base i w
  have occW : bytesVal .ld (read8 c.σ.mem (pageTable + 0x18)) = occ := by rw [read8_value]; exact occWord
  have sizeW : bytesVal .ld (read8 c.σ.mem (pageTable + 0)) = size := by rw [read8_value]; exact sizeWord
  have entW : bytesVal .ld (read8 c.σ.mem (pageTable + 0x20)) = ent := by rw [read8_value]; exact entWord
  have field (off : Nat) (hoff : off ≤ 0x20) (aligned : off % 8 = 0) :
      ReadWindow (BitVec.ofNat 64 (pageTable + off)) 8 := by
    constructor <;> rw [BitVec.toNat_ofNat] <;> simp only [pageTable, Layout.sym_caml_page_table, Layout.sym_tohost] <;>
      omega
  have pin (off : Nat) (hoff : off ≤ 0x20) :
      LPins8 c.σ.mem (BitVec.ofNat 64 (pageTable + off)).toNat (read8 c.σ.mem (pageTable + off)) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [pageTable, Layout.sym_caml_page_table]; omega)]
    exact read8_pins _ _
  apply boundary_of_blocks leaf
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_modifyXadc0Seg 0x8000adc0#64 [(10, page)]
        [read8 c.σ.mem (pageTable + 0x18), read8 c.σ.mem (pageTable + 0), read8 c.σ.mem (pageTable + 0x20)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := pageModifyLoad_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        · refine (field 0x18 (by decide) (by decide)).ld rfl ?_ (pin 0x18 (by decide))
          plk2; rw [page_record_base']; exact page_record_field 0x18 _ (by decide) (by decide)
        · refine memFacts_stepMem_skip rfl ?_
          refine (field 0 (by decide) (by decide)).ld rfl ?_ (pin 0 (by decide))
          plk2; rw [page_record_base']; exact page_record_field 0 _ (by decide) (by decide)
        · repeat refine memFacts_stepMem_skip rfl ?_
          refine (field 0x20 (by decide) (by decide)).ld rfl ?_ (pin 0x20 (by decide))
          plk2; rw [page_record_base']; exact page_record_field 0x20 _ (by decide) (by decide) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_page_table_modifyXadc0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, pagemodifyload_line_8000adc0, pagemodifyload_line_8000adc4,
      pagemodifyload_line_8000adc8, pagemodifyload_line_8000adcc, pagemodifyload_line_8000add0,
      pagemodifyload_line_8000add4, pagemodifyload_line_8000add8] at pins
    rw [base _ rfl, occW, sizeW, entW, slli_one _ _ rfl, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      BitVec.add_zero] at pins
    exact pins
  · decide
  · decide

local macro "pmk" : tactic => `(tactic| simp only [pagemodifyshift_line_8000addc, pagemodifyshift_line_8000ade0, pagemodifyshift_line_8000ade4, pagemodifyshift_line_8000ade8, pagemodifyprobe_line_8000ae84, pagemodifyprobe_line_8000ae88, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

theorem page_shift_addr : 2147528156#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 382231#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1764#12 = BitVec.ofNat 64 (pageTable + 8) := by decide

theorem page_shift_reg (i : MInstr) (w : i.word = 382231#32) :
    2147528156#64 + Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) + Functions.sign_extend (m := 64) 1764#12 =
      BitVec.ofNat 64 (pageTable + 8) := by
  rw [imm20Of, w]; decide

/-- Load the shift; the table is at most half full, so no resize. -/
theorem page_shift_check (c : Config) (ra clr kind twice size : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, clr), (12, kind), (10, twice), (15, size)])
    (shiftWord : read4 c.σ.mem (pageTable + 8) = [53#8, 0#8, 0#8, 0#8])
    (room : guardB bop.BGEU twice size = false) :
    FnSummary 0x8000addc#64 (fun d => d = c) (BoundaryPost [18, 20, 19] c ra 0x8000adf0#64
      [(19, kind), (20, clr), (18, 53#64), (11, clr), (12, kind), (10, twice), (15, size)]) := by
  have shiftV : bytesVal .lw (read4 c.σ.mem (pageTable + 8)) = 53#64 := by rw [shiftWord]; decide
  apply boundary_of_blocks leaf
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_modifyXaddcFSeg 0x8000addc#64
        [(11, clr), (12, kind), (10, twice), (15, size)] [read4 c.σ.mem (pageTable + 8)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 12, 10, 15]; decide
      shape := by change ChainOK _ [11, 12, 10, 15] _; decide
      tick := leaf.tick
      facts := by
        have code := pageModifyShift_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        · refine (show ReadWindow (BitVec.ofNat 64 (pageTable + 8)) 4 by constructor <;> decide).lw rfl ?_ (by
            rw [show (BitVec.ofNat 64 (pageTable + 8)).toNat = pageTable + 8 by decide]; exact read4_pins _ _)
          pmk; exact page_shift_addr
        · pmk; exact room }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_page_table_modifyXaddcFSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, pagemodifyshift_line_8000addc, pagemodifyshift_line_8000ade0,
      pagemodifyshift_line_8000ade4, pagemodifyshift_line_8000ade8] at pins
    rw [shiftV, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero] at pins
    exact pins
  · decide
  · decide

/-- Into the probe loop: the mask and the page size. -/
theorem lui_page (i : MInstr) (w : i.word = 0x00001837#32) :
    Functions.sign_extend (m := 64) (imm20Of i +++ 0#12) = 4096#64 := by
  rw [imm20Of, w]; decide

theorem page_probe_init (c : Config) (ra mask : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, BitVec.ofNat 64 pageTable)])
    (maskWord : bytesT c.σ.mem (pageTable + 0x10) 8 = mask) :
    FnSummary 0x8000ae84#64 (fun d => d = c) (BoundaryPost [17, 16] c ra 0x8000ae9c#64
      [(16, 4096#64), (17, mask), (9, BitVec.ofNat 64 pageTable)]) := by
  have maskV : bytesVal .ld (read8 c.σ.mem (pageTable + 0x10)) = mask := by rw [read8_value]; exact maskWord
  apply boundary_of_blocks leaf
    (block_summary _ _ _ _ _ (show BlockInput caml_page_table_modifyXae84Seg 0x8000ae84#64
        [(9, BitVec.ofNat 64 pageTable)] [read8 c.σ.mem (pageTable + 0x10)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9]; decide
      shape := by change ChainOK _ [9] _; decide
      tick := leaf.tick
      facts := by
        have code := pageModifyProbe_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_page_table_modify_at_"
        refine (show ReadWindow (BitVec.ofNat 64 (pageTable + 0x10)) 8 by constructor <;> decide).ld rfl ?_ (by
          rw [show (BitVec.ofNat 64 (pageTable + 0x10)).toNat = pageTable + 0x10 by decide]; exact read8_pins _ _)
        pmk; exact page_record_field 0x10 _ (by decide) (by decide) }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_page_table_modifyXae84Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM,
      ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, pagemodifyprobe_line_8000ae84, pagemodifyprobe_line_8000ae88] at pins
    rw [maskV, lui_page _ rfl] at pins
    exact pins
  · decide
  · decide
end OCaml.Vm.Boot.Startup
