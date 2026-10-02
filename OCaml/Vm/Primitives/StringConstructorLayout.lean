import OCaml.Vm.Primitives.StringNursery
import OCaml.Vm.Primitives.StringAllocationLayout

namespace OCaml.Vm.Primitives.StringAllocation
open Vsa.Machine Vsa.Sim

/-- Normalize the machine initializer's wrapped addresses to the canonical
string layout using the RAM header window and the bounded byte length. -/
theorem initialization_shell_log (ra sp header : BitVec 64) (n : Nat)
    (bound : n < 2^32) (window : WriteWindow header 8) :
    initializationLog (reservedRegisters ra sp (BitVec.ofNat 64 n) header) header =
      shellLog (header.toNat + 8) n := by
  have h := window.upper
  have span := stringSpan_toNat n bound
  have last : (header + 8#64 + stringSpan (BitVec.ofNat 64 n) - 8#64).toNat =
      header.toNat + 8 + 8 * ((n + 8) / 8) - 8 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, span]
    omega
  have padding : (header + 8#64 + (stringSpan (BitVec.ofNat 64 n) - 1#64)).toNat =
      header.toNat + 8 + 8 * ((n + 8) / 8) - 1 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, span]
    omega
  simp only [initializationLog, reservedRegisters, shellLog, last, padding, Nat.add_sub_cancel]
  rfl

/-- The successful machine constructor establishes the string shell. -/
theorem NurseryPost.shell {ra sp domain young c after n}
    (post : NurseryPost ra sp (BitVec.ofNat 64 n) domain young c after)
    (bound : n < 2^32)
    (window : WriteWindow (nurseryHeader young (BitVec.ofNat 64 n)) 8) :
    StringShell after ((nurseryHeader young (BitVec.ofNat 64 n)).toNat + 8) n := by
  let saved := writeLog c.σ.mem (savedRaLog sp ra ++ reservationLog domain young
    (stringSpan (BitVec.ofNat 64 n)))
  let initial : Config := ⟨{ c.σ with mem := saved }, c.tick, c.steps⟩
  apply shell_layout (c := initial) (by omega) bound
  rw [post.memory]
  unfold constructorLog
  rw [writeLog_append, initialization_shell_log ra sp _ n bound window]

/-- A payload-confined copy cannot alter the header or canonical padding. -/
theorem StringShell.frame_payload {before after : Config} {a n : Nat}
    (shell : StringShell before a n) (address : 8 ≤ a)
    (frame : ∀ x, x < a ∨ a + n ≤ x → byte after x = byte before x) :
    StringShell after a n := by
  have header : word after (a - 8) = word before (a - 8) :=
    Reloc.bytesT_congr (fun i hi => frame _ (Or.inl (by omega)))
  constructor
  · rw [header]; exact shell.header
  · rw [frame _ (Or.inr (by omega))]; exact shell.padding
  · intro i low high
    rw [frame _ (Or.inr (by omega))]
    exact shell.zeroPad i low high

end OCaml.Vm.Primitives.StringAllocation
