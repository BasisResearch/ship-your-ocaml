import OCaml.Vm.Boot.Startup.OpenRun
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris OCaml.Vm.Primitives

/-- htif.c's file system after the first `open`: `fs_ready`, the three
standard descriptors, slot 1 holding `prog` (its name at `node`), and
descriptor 3 free. -/
structure FsUp (m : Std.ExtHashMap Nat (BitVec 8)) (node : BitVec 64) : Prop where
  words : FsWords m
  slot : FsSlotOne m node
  fd3 : read4 m (Layout.sym_fds + 72) = [0#8, 0#8, 0#8, 0#8]

theorem FsWordByte.htif {x : Nat} (h : FsWordByte x) : HtifByte x := by
  unfold FsWordByte at h
  unfold HtifByte
  rcases h with ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact Or.inl ⟨lo, hi⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨lo, ?_⟩)))
    simp only [Layout.sym_fds] at hi ⊢; omega

theorem slotOne_htif {x : Nat} (lo : slotOne ≤ x) (hi : x < slotOne + 56) : HtifByte x := by
  unfold HtifByte
  refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)) <;> simp only [slotOne, Layout.sym_files] at lo hi ⊢ <;> omega

theorem fd3_htif {i : Nat} (hi : i < 4) : HtifByte (Layout.sym_fds + 72 + i) := by
  unfold HtifByte
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))) <;> simp only [Layout.sym_fds] <;> omega

/-- File-system state lives in kept bytes and the node's name block. -/
theorem FsUp.transport {m m' : Std.ExtHashMap Nat (BitVec 8)} {node : BitVec 64} (h : FsUp m node)
    (kept : ∀ x, HtifByte x → (m'[x]?).getD 0 = (m[x]?).getD 0)
    (name : ∀ j, j ≤ 4 → (m'[node.toNat + j]?).getD 0 = (m[node.toNat + j]?).getD 0) : FsUp m' node where
  words := h.words.transport fun x hx => kept x hx.htif
  slot := h.slot.transport (fun x lo hi => kept x (slotOne_htif lo hi)) name
  fd3 := by
    have k (i : Nat) (hi : i < 4) : (m'[Layout.sym_fds + 72 + i]?).getD 0 = (m[Layout.sym_fds + 72 + i]?).getD 0 :=
      kept _ (fd3_htif hi)
    rw [← h.fd3]
    simp only [read4]
    rw [show (m'[Layout.sym_fds + 72]?).getD 0 = (m[Layout.sym_fds + 72]?).getD 0 from by simpa using k 0 (by decide),
      k 1 (by decide), k 2 (by decide), k 3 (by decide)]

theorem FsUp.frame {before after : Config} {node : BitVec 64} (h : FsUp before.σ.mem node)
    (kept : EmbedFrame before after)
    (name : ∀ j, j ≤ 4 → (after.σ.mem[node.toNat + j]?).getD 0 = (before.σ.mem[node.toNat + j]?).getD 0) :
    FsUp after.σ.mem node :=
  h.transport (fun x hx => kept.byte x (Or.inr (Or.inr (Or.inr hx)))) name

/-- Descriptor 3 is clear while htif.c's globals hold their loader values. -/
theorem HtifImage.fd3 {c : Config} (h : HtifImage c) (i : Nat) (hi : i < 4) :
    (c.σ.mem[Layout.sym_fds + 72 + i]?).getD 0 = 0#8 :=
  h.zero (fd3_htif hi) (Or.inr (by unfold allocatorImpureAddr Layout.sym_fds; omega))

/-- The first `open` leaves the file system up. -/
theorem OpenOcamlrun.fs_up {H capacity sp ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 before after}
    (w : OpenOcamlrun H capacity sp ra path s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 before after)
    (htif : HtifImage before) : FsUp after.σ.mem w.node where
  words := w.words
  slot := w.slot
  fd3 := by
    have k (i : Nat) (hi : i < 4) : (after.σ.mem[Layout.sym_fds + 72 + i]?).getD 0 = 0#8 :=
      (w.fdsKept _ (by omega) (by omega)).trans (htif.fd3 i hi)
    simp only [read4]
    rw [show (after.σ.mem[Layout.sym_fds + 72]?).getD 0 = 0#8 from by simpa using k 0 (by decide),
      k 1 (by decide), k 2 (by decide), k 3 (by decide)]
end OCaml.Vm.Boot.Startup
