import OCaml.Vm.Boot.Startup.SearchInPathScan
import OCaml.Vm.Boot.Startup.SearchExePath
import OCaml.Vm.Boot.Startup.EmbedFrame
import OCaml.Vm.Boot.WhileMinArgv
import OCaml.Vm.Boot.Startup.SearchTableReset
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic VsaIris VsaIris.Sym VsaIris.MallocFast OCaml.Vm.Primitives

theorem cstr_getD_le {m : Vsa.MemRepr.Mem} {p : Nat} {cs : List Char} (h : Vsa.MemRepr.CStr m p cs)
    (k : Nat) (hk : k ≤ cs.length) : (m[p + k]?).getD 0 = BitVec.ofNat 8 (byteVal cs k) := by
  obtain ⟨b, pin, -, val⟩ := cstr_byte_val m p cs h k hk
  rw [pin, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  rw [BitVec.toNat_ofNat, ← val, Nat.mod_eq_of_lt this]

def argv0Ptr : BitVec 64 := BitVec.ofNat 64 WhileMinImage.argv0

theorem argv0_byte {c : Config} (h : EmbedImage c) (k : Nat) (hk : k ≤ 8) :
    imgM c.σ.mem (argv0Ptr.toNat + k) = BitVec.ofNat 8 (byteVal WhileMinImage.argv0Chars k) := by
  unfold imgM
  have inside : EmbedByte (WhileMinImage.argv0 + k) := by
    constructor
    · unfold WhileMinImage.argv0 Vsa.Sim.DlHeap.heapEnd; omega
    · unfold WhileMinImage.argv0 embedLimit Layout.sym_stack_top Layout.sym_stack_size; omega
  rw [show argv0Ptr.toNat = WhileMinImage.argv0 from by decide, h.byte _ inside]
  exact cstr_getD_le WhileMinImage.argv0_string k hk

/-- `argv[0]` ("ocamlrun") is a nonempty slash-free C string in every state that
keeps the embedded image. -/
theorem argv0_plain {c : Config} (h : EmbedImage c) : PlainName c.σ.mem argv0Ptr 8 where
  bytes := {
    nz := fun i hi => by
      rw [argv0_byte h i (by omega)]
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    nul := by rw [argv0_byte h 8 (by decide)]; decide
    lo := by decide
    hi := by decide
    htif := by decide }
  region := by constructor <;> decide
  noSlash := fun k hk => by
    rw [argv0_byte h k (by omega)]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  positive := by decide
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

/-- caml_main's `exe_name` slot holds `argv[0]` once caml_attempt_open has saved its frame. -/
theorem ResetSearchTableReturned.exe_name {initial after} (w : ResetSearchTableReturned initial after) :
    bytesT w.atSaved.σ.mem exeNameSlot.toNat 8 = argv0Ptr := by
  have attemptFrame : NativeFrame parameterStack 64 := by constructor <;> decide
  have argv := w.shared.kept.embed.argv_word 0 (by decide)
  rw [Nat.mul_zero] at argv
  rw [word_observed (m := w.atOpen.σ.mem) _ (fun i _ => by
      rw [w.save.memory, frameOn_writeLog _ _ _ (attemptOpenLog_inside attemptFrame) _
        ⟨Or.inr (by unfold exeNameSlot; decide +revert), trivial⟩]),
    w.call.memory]
  unfold camlAttemptLog exeNameSlot
  rw [word_writeLog, show (BitVec.ofNat 64 WhileMinImage.argvArray).toNat = WhileMinImage.argvArray + 0 from by decide,
    argv, WhileMinImage.argv_entry0]
  rfl
end OCaml.Vm.Boot.WhileMinElfParse
