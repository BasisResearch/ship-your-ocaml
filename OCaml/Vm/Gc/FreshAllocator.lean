import OCaml.Vm.Gc.FreshCall
import OCaml.Vm.Gc.AllocEntryAccess

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Allocation-wrapper entry pins derived entirely from oldify's initial
caller values, observed header and actual allocating JAL link. -/
def allocatorRegs (R : Nat → BitVec 64) (c : Config) (n : Nat) : BitVec 64 :=
  if n = 1 then call.link else if n = 2 then OldifyEntry.frameSp R
  else if n = 8 then R 10 else if n = 9 then R 11
  else if n = 10 then sizeWord (word c (R 10 - 8#64).toNat)
  else if n = 11 then tagWord (word c (R 10 - 8#64).toNat) else R n

/-- Any 64-bit header yields a size within the allocating wrapper's maximum. -/
theorem allocator_size (R : Nat → BitVec 64) (c : Config) :
    (allocatorRegs R c 10).toNat ≤ AllocEntry.maximum.toNat := by
  change (sizeWord (word c (R 10 - 8#64).toNat)).toNat ≤ AllocEntry.maximum.toNat
  rw [sizeWord_nat]
  have bound := (word c (R 10 - 8#64).toNat).isLt
  change _ ≤ 18014398509481983
  omega

/-- Prologue stores preserve the allocator's code image under the shared
above-HTIF write policy. -/
theorem Prepared.allocator_code {R before after exitPC writes}
    (post : Prepared R before after exitPC writes)
    (windows : ∀ cell ∈ OldifyEntry.saves,
      WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8)
    (code : Code.Caml_alloc_shr_for_minor_gcLoaded before.σ.mem) :
    Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem := by
  rw [post.memory]
  apply image_writeLog Code.caml_alloc_shr_for_minor_gc_transport code
  intro e member
  exact Nat.le_trans (by decide : (0x8000b8a4 : Nat) ≤ tohostAddr)
    (OldifyEntry.saveLog_high windows e member)

theorem Prepared.word_frame {R before after exitPC writes a}
    (post : Prepared R before after exitPC writes)
    (outside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) a 8) :
    word after a = word before a := by
  change bytesT after.σ.mem a 8 = bytesT before.σ.mem a 8
  rw [post.memory, bytesT_writeLog_out _ outside]

/-- Derive the wrapper's real input, including loaded free-list target,
from the actual oldify prefix and initial separated observations. -/
theorem AllocationEntry.allocator_input {R target before after}
    (post : AllocationEntry R before after)
    (saved : ∀ cell ∈ OldifyEntry.saves,
      WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8)
    (code : Code.Caml_alloc_shr_for_minor_gcLoaded before.σ.mem)
    (windows : AllocEntry.Windows (allocatorRegs R before))
    (pointer : word before Layout.sym_caml_fl_p_allocate = target)
    (outer : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) Layout.sym_caml_fl_p_allocate 8)
    (inner : OutLRange (AllocEntry.prefixLog (allocatorRegs R before)) Layout.sym_caml_fl_p_allocate 8) :
    AllocEntry.Input (allocatorRegs R before) target after := by
  refine ⟨post.good, post.minstret, post.tick, post.toPrepared.allocator_code saved code,
    ?_, windows, allocator_size R before, (post.toPrepared.word_frame outer).trans pointer, inner⟩
  exact ⟨gholds_lookup _ post.carried rfl, post.link, gholds_lookup _ post.arguments rfl,
    gholds_lookup _ post.carried rfl, gholds_lookup _ post.arguments rfl,
    gholds_lookup _ post.arguments rfl, True.intro⟩

/-- Oldify and the allocating wrapper have installed both native frames and
loaded the free-list target. Its indirect JAL and allocation body are next. -/
structure FreeListBoundary (R : Nat → BitVec 64) (target : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  oldifyCode : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem
    (OldifyEntry.saveLog OldifyEntry.saves R ++ AllocEntry.effect (allocatorRegs R before))
  pc : PCAt AllocEntry.callPc after
  registers : GHolds after.σ (AllocEntry.atCall (allocatorRegs R before) target)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ (1 :: prepareWrites) ++ wrChain AllocEntry.blocks, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Real fresh oldify entry and allocating-wrapper prefix through the
loaded free-list indirect-call boundary, with no callee-run premise. -/
theorem prepare_free_list {R domain size tag target c}
    (input : EntryInput R domain size tag c)
    (code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem)
    (windows : AllocEntry.Windows (allocatorRegs R c))
    (pointer : word c Layout.sym_caml_fl_p_allocate = target)
    (outer : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) Layout.sym_caml_fl_p_allocate 8)
    (inner : OutLRange (AllocEntry.prefixLog (allocatorRegs R c)) Layout.sym_caml_fl_p_allocate 8) :
    FnSummary OldifyEntry.pc (fun d => d = c) (FreeListBoundary R target c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_allocation input).run
  intro middle entered
  have allocInput := entered.allocator_input input.entry.windows code windows pointer outer inner
  obtain ⟨after, run, prepared⟩ := (AllocEntry.prepare allocInput).run middle ⟨entered.pc,rfl⟩
  refine ⟨after, run, ⟨prepared.machine.good, prepared.machine.minstret, prepared.machine.tick,
    prepared.code, ?_, ?_, prepared.pc, prepared.registers,
    prepared.machine.output.trans entered.output, ?_⟩⟩
  · exact image_after Code.caml_oldify_one_transport (by decide) entered.toPrepared.code
      (chainPlan_facts (AllocEntry.code_facts allocInput.code) (AllocEntry.access allocInput)) prepared.machine
  · rw [prepared.memory, entered.memory, writeLog_append]
  · intro r noise outside
    exact (prepared.machine.frame r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (entered.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

end OCaml.Vm.Gc.Fresh
