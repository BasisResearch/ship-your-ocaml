import OCaml.Vm.Primitives.Format.AllocSprintf
import OCaml.Vm.Primitives.Format.VsnprintfLong
import OCaml.Vm.Primitives.Format.ParseFormatCall
import OCaml.Vm.Primitives.StringCopyMachine

/-! The real short-result continuation of `caml_alloc_sprintf`.

The requested splice to `copy_string_machine` is obstructed by the pinned
JAL target: this ELF calls `caml_alloc_initialized_string`, with a length in
a0 and a source in a1. This module checks that obstruction and executes the
actual fits/argument/JAL continuation. It does not claim an allocation or an
entry-to-return `caml_alloc_sprintf` summary.
-/
namespace OCaml.Vm.Primitives.Format.AllocSprintfLong
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

def decimalBytes (v : BitVec 64) : List (BitVec 8) :=
  strBytes (Vsa.While.intToString v.toInt)

/-- Signed 64-bit decimal selects the real 127-byte fit test's fallthrough. -/
theorem decimal_fits (v : BitVec 64) :
    guardB .BLTU 127#64 (BitVec.ofNat 64 (decimalBytes v).length) = false := by
  have bound := intToString_length_le v
  apply ParseFormat.bltu_false_of_le
  simp only [BitVec.toNat_ofNat]
  change (decimalBytes v).length % 18446744073709551616 ≤ 127
  unfold decimalBytes
  omega

/-- At capacity 128 the wrapper returns every decimal byte and the final NUL. -/
structure DecimalBuffer (v : BitVec 64) (dst : Nat) (mv : Nat → BitVec 8) : Prop where
  length : (decimalBytes v).length ≤ 20
  fits : (decimalBytes v).length + 1 ≤ 128
  bytes : ∀ i, i < (decimalBytes v).length → mv (dst + i) = (decimalBytes v).getD i 0
  nul : mv (dst + (decimalBytes v).length) = 0#8

theorem decimal_buffer {s dst R Mt rv mv v}
    (post : VsnResult s dst 128 R Mt (decimalBytes v) rv mv) :
    DecimalBuffer v dst mv := by
  have bound : (decimalBytes v).length ≤ 20 := intToString_length_le v
  have full : min (decimalBytes v).length (128 - 1) = (decimalBytes v).length := by omega
  exact ⟨bound, by omega, fun i hi => post.bytes i (by rw [full]; exact hi),
    by simpa only [full] using post.nul⟩

/-- The decoded short-path JAL cannot enter the existing copy-string summary,
whose entry in `StringCopy.copy_string_machine` is `0x8000c254`. This is a
control-flow obstruction, independent of caller/runtime preconditions. -/
theorem copy_string_target_obstruction :
    AllocSprintf.copy_call.target ≠ 0x8000c254#64 := by
  rw [AllocSprintf.copy_call_target]
  decide

/-- Actual parked state after the short-result continuation. The length and
buffer argument use the initialized-string ABI; allocation is still pending. -/
structure CopyEntered (R : Nat → BitVec 64) (before after : Config) : Prop
    extends LeafInput AllocSprintf.copy_call.link after where
  pc : OCaml.Vm.pcOf after = some 0x8000c284#64
  arguments : GHolds after.σ [(2, R 2), (10, R 10), (11, R 2 + 16#64)]
  memory : after.σ.mem = before.σ.mem
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- Execute the real fit branch, source setup and decoded JAL. No callee
summary or callee-return assumption occurs in these premises. -/
theorem short_continuation {v : BitVec 64} (c : Config) (R : Nat → BitVec 64)
    (h : LeafInput (R 1) c) (regs : GHolds c.σ (AllocSprintf.fits_input R))
    (length : R 10 = BitVec.ofNat 64 (decimalBytes v).length) :
    FnSummary 0x80013f10#64 (fun d => d = c) (CopyEntered R c) := by
  have fit : guardB .BLTU 127#64 (R 10) = false := by rw [length]; exact decimal_fits v
  apply summary_bind (AllocSprintf.fits_fast c R h regs fit) (fun _ p => p.pc)
  intro fitted p
  have leaf : LeafInput (R 1) fitted :=
    ⟨p.good, p.image, p.minstret, gholds_lookup _ p.regs rfl, h.aligned, p.tick⟩
  have copyRegs : GHolds fitted.σ (AllocSprintf.copy_input R) :=
    holds_project p.regs (by simp [AllocSprintf.copy_input, AllocSprintf.fits_regs, lookupG])
  apply summary_bind (AllocSprintf.copy_fast fitted R leaf copyRegs) (fun _ q => q.pc)
  intro prepared q
  have args : GHolds prepared.σ [(2, R 2), (10, R 10), (11, R 2 + 16#64)] :=
    holds_project q.regs (by simp [AllocSprintf.copy_regs, lookupG])
  have call := call_registers_summary AllocSprintf.copy_call_shape AllocSprintf.copy_call_decode
    prepared (AllocSprintf.copy_call_pins q.image) q.good q.image q.tick q.minstret
    _ args (by change KeysOK [2, 10, 11]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply call.weaken (fun _ eq => eq)
  intro after entered
  refine ⟨⟨entered.good, entered.image, entered.minstret,
    gholds_lookup _ entered.regs rfl, by decide, entered.tick⟩,
    ?_, ?_, ?_, ?_⟩
  · exact entered.pc
  · exact holds_project entered.regs (by simp [lookupG])
  · exact entered.memory.trans (q.memory.trans p.memory)
  · simp only [Vsa.Machine.output, entered.output, q.output, p.output]

/-- The actual a0 length cannot also be copy_string's source pointer at the
real local-buffer address. The ordinary stack lower bound suffices. -/
theorem copy_string_argument_obstruction {R : Nat → BitVec 64} {v : BitVec 64} {sp : Nat}
    (stack : R 2 = BitVec.ofNat 64 sp) (lower : 1024 ≤ sp) (upper : sp + 16 < 2 ^ 64)
    (length : R 10 = BitVec.ofNat 64 (decimalBytes v).length) :
    R 10 ≠ R 2 + 16#64 := by
  have bound : (decimalBytes v).length ≤ 20 := intToString_length_le v
  rw [length, stack]
  intro eq
  have natEq := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at natEq
  omega

end OCaml.Vm.Primitives.Format.AllocSprintfLong
