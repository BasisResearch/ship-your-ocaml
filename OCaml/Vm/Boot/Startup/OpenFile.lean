import OCaml.Vm.Boot.Startup.ResolveRun
import OCaml.Vm.Boot.Startup.FsUp
import OCaml.Vm.Boot.Startup.OpenProg
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-! htif.c's state for "/prog" open as descriptor 3, apart from its position. -/

/-- Descriptor 3 is open on slot 1, whose name block is `node`. -/
structure OpenFile (m : Std.ExtHashMap Nat (BitVec 8)) (node : BitVec 64) : Prop where
  words : FsWords m
  slot : FsSlotOne m node
  kind : read4 m (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8]
  nodeWord : read4 m (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8]
  flags : read4 m (Layout.sym_fds + 88) = [0#8, 0#8, 0#8, 0#8]

/-- The bytes `OpenFile` reads: htif.c globals other than descriptor 3's
position, and the name block. -/
def OpenFileByte (node : BitVec 64) (x : Nat) : Prop :=
  (HtifByte x ∧ (x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x)) ∨ (node.toNat ≤ x ∧ x ≤ node.toNat + 4)

theorem OpenFile.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {node : BitVec 64} (h : OpenFile m node)
    (same : ∀ x, OpenFileByte node x → (m'[x]?).getD 0 = (m[x]?).getD 0) : OpenFile m' node := by
  have fds (x : Nat) (lo : Layout.sym_fds ≤ x) (hi : x < Layout.sym_fds + 24 * 32)
      (pos : x < Layout.sym_fds + 80 ∨ Layout.sym_fds + 88 ≤ x) : (m'[x]?).getD 0 = (m[x]?).getD 0 :=
    same x (Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨lo, hi⟩))), pos⟩)
  refine ⟨h.words.transport fun x hx => same x (Or.inl ⟨?_, ?_⟩), h.slot.transport
    (fun x lo hi => same x (Or.inl ⟨slotOne_htif lo hi, ?_⟩)) (fun j hj => same _ (Or.inr ⟨by omega, by omega⟩)),
    ?_, ?_, ?_⟩
  · rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩)))
  · rcases hx with h | h <;> simp only [Layout.sym_fs_ready, Layout.sym_fds] at * <;> omega
  · simp only [slotOne, Layout.sym_files, Layout.sym_fds] at *; omega
  · rw [read4_observed (m := m) _ fun k hk => fds _ (by omega) (by omega) (by omega)]; exact h.kind
  · rw [read4_observed (m := m) _ fun k hk => fds _ (by omega) (by omega) (by omega)]; exact h.nodeWord
  · rw [read4_observed (m := m) _ fun k hk => fds _ (by omega) (by omega) (by omega)]; exact h.flags

end OCaml.Vm.Boot.Startup
