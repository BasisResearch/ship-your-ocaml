import OCaml.Vm.Primitives.StringCopyFast
import OCaml.Vm.Primitives.LibraryStrlenCall

namespace OCaml.Vm.Primitives.StringCopy
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

def entryRegisters (ra sp : BitVec 64) (a : Nat) : Nat → BitVec 64
  | 1 => ra | 2 => sp | 10 => BitVec.ofNat 64 a | _ => 0

/-- Ordinary memory and ABI facts at the copy-string entry. The read-only
library image comes from the fixed ELF and the supplied C-string bytes. -/
structure SizedInput (live : Nat → Prop) (Dt : Vsa.MemRepr.Mem) (DA : List Nat)
    (ra sp : BitVec 64) (a len : Nat) (g : Nat → BitVec 8) (c : Config) : Prop
    extends LeafInput ra c where
  libraryGood : VsaOk live c
  stack : gpr c 2 = some sp
  returnSlot : WriteWindow (sp - 8#64) 8
  sourceSlot : WriteWindow (sp - 24#64) 8
  saveImage : ImageOutside (saveLog (entryRegisters ra sp a))
  saveLibrary : ∀ p ∈ snpText ++ dataOf Dt DA, OutL (saveLog (entryRegisters ra sp a)) p.1
  libraryImage : ImageLive live
  codeLive : ∀ p ∈ snpText, live p.1
  readOnly : ROHolds (vsaModel live) c roR (snpText ++ dataOf Dt DA)
  string : StrRead Dt DA (fun _ => False) c.σ.mem a len g

/-- The first native call has computed the length while retaining its stack
frame, source bytes, output and all non-scratch ABI registers. -/
structure SizedPost (live : Nat → Prop) (ra sp : BitVec 64) (a len : Nat)
    (before after : Config) : Prop extends LeafInput save_call.link after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some 0x8000c264#64
  result : gpr after 10 = some (BitVec.ofNat 64 len)
  stack : gpr after 2 = some (sp - 32#64)
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (saveLog (entryRegisters ra sp a)))
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 10, 11, 12, 13, 14, 15] →
    gpr after n = gpr before n

/-- Compose the generated save/JAL boundaries with the proved strlen call. -/
theorem copy_string_sized {live Dt DA ra sp a len g} (c : Config)
    (h : SizedInput live Dt DA ra sp a len g c)
    (source : gpr c 10 = some (BitVec.ofNat 64 a)) :
    FnSummary 0x8000c254#64 (fun d => d = c) (SizedPost live ra sp a len c) := by
  let R := entryRegisters ra sp a
  have regs : GHolds c.σ (save_input R) := ⟨h.raReg, h.stack, source, True.intro⟩
  have S := save_fast c R h.toLeafInput regs h.returnSlot h.sourceSlot h.saveImage
  apply summary_bind S (fun _ p => p.pc)
  intro saved p
  have good := p.vsaOk h.libraryGood (by decide) (by simp [save_regs, keysG])
  have readonly := p.toEffectPost.readOnly_log (live := live) (by decide) (by decide) h.readOnly h.saveLibrary
  have args : GHolds saved.σ [(2, sp - 32#64), (10, BitVec.ofNat 64 a)] :=
    holds_project p.regs (by simp [save_regs, R, entryRegisters, lookupG])
  have J := call_registers_summary save_call_shape save_call_decode saved (save_call_pins p.image)
    p.good p.image p.tick p.minstret _ args (by change KeysOK [2, 10]; decide)
    (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good' := q.vsaOk (log := []) good (by decide) (by simp [keysG])
  have readonly' := q.toEffectPost.readOnly_log (live := live) (log := [])
    (by decide) (by decide) readonly (fun _ _ => True.intro)
  have L := strlen_call entered h.codeLive (strlen_readOnly_memory h.string entered.σ.mem)
    good' q.image h.libraryImage readonly'
    (gholds_lookup _ q.regs rfl) (gholds_lookup _ q.regs rfl) (by decide)
  apply L.weaken (fun _ eq => eq)
  intro after post
  refine ⟨post.toLeafInput, post.libraryGood, post.pc, post.result, ?_, ?_, ?_, ?_⟩
  · exact (post.registers 2 (by decide) (by decide) (by decide)).trans (gholds_lookup _ q.regs rfl)
  · intro x
    have memory := post.memory x
    rw [q.memory, p.memory] at memory
    exact memory
  · exact post.output.trans (by simp only [output, q.output, p.output])
  · intro n low high untouched
    have neq1 : n ≠ 1 := by simp only [List.mem_cons, List.mem_singleton] at untouched; omega
    have neq2 : n ≠ 2 := by simp only [List.mem_cons, List.mem_singleton] at untouched; omega
    have scratch : n ∉ [10, 11, 12, 13, 14, 15] := fun hn => untouched (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn))
    exact (post.registers n low high scratch).trans
      ((q.toEffectPost.gpr_frame (by decide) n low high (by simpa using neq1)).trans
       (p.toEffectPost.gpr_frame (by decide) n low high (by simpa using neq2)))

end OCaml.Vm.Primitives.StringCopy
