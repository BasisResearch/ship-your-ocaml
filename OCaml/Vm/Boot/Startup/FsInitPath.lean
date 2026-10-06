import OCaml.Vm.Boot.Startup.EmbedFrame
import OCaml.Vm.Boot.Startup.LeafReady
import OCaml.Vm.Boot.WhileMinEmbedFiles
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris OCaml.Vm.Primitives
open OCaml.Vm.Boot.WhileMinImage (initialMem)

/-! What htif.c's `fs_init` reads of the embedded-file table, from any state
that keeps the embedded image: the header, the single entry "/prog" and its
extent, the terminator, and the name "prog" that `strchr` and `strlen` scan. -/

/-- The table's only path, "/prog". -/
abbrev progPath : BitVec 64 := 0x8680253d#64
/-- The name after the leading '/'. -/
abbrev progName : BitVec 64 := 0x8680253e#64

theorem EmbedImage.fs_word {c} (h : EmbedImage c) (a : Nat) (lo : heapEnd ≤ a) (hi : a + 8 ≤ embedLimit) :
    bytesT c.σ.mem a 8 = bytesT initialMem a 8 :=
  h.word a fun i hi' => ⟨by omega, by omega⟩

theorem EmbedImage.fs_header {c} (h : EmbedImage c) :
    bytesT c.σ.mem Layout.sym_embed_start 8 = 0x86800018#64 :=
  (h.fs_word _ (by decide) (by decide)).trans WhileMinImage.embed_header

theorem EmbedImage.fs_path {c} (h : EmbedImage c) : bytesT c.σ.mem (0x86800018#64).toNat 8 = progPath :=
  (h.fs_word _ (by decide) (by decide)).trans WhileMinImage.embed_path0

theorem EmbedImage.fs_start {c} (h : EmbedImage c) :
    bytesT c.σ.mem (0x86800018#64 + 8#64).toNat 8 = 0x86800090#64 :=
  (h.fs_word _ (by decide) (by decide)).trans WhileMinImage.embed_start0

theorem EmbedImage.fs_stop {c} (h : EmbedImage c) :
    bytesT c.σ.mem (0x86800018#64 + 16#64).toNat 8 = 0x8680253c#64 :=
  (h.fs_word _ (by decide) (by decide)).trans WhileMinImage.embed_end0

theorem EmbedImage.fs_end {c} (h : EmbedImage c) : bytesT c.σ.mem (0x86800018#64 + 24#64).toNat 8 = 0#64 :=
  (h.fs_word _ (by decide) (by decide)).trans WhileMinImage.embed_end

/-- The bytes of "/prog" and its NUL. -/
def progByte : Nat → BitVec 8
  | 0 => 47#8 | 1 => 112#8 | 2 => 114#8 | 3 => 111#8 | 4 => 103#8 | _ => 0#8

theorem EmbedImage.fs_byte {c} (h : EmbedImage c) (j : Nat) (hj : j < 6) :
    strByte c.σ.mem (WhileMinImage.embedPath0 + j) = progByte j := by
  unfold strByte
  rw [h.byte _ ⟨by unfold WhileMinImage.embedPath0 heapEnd; omega,
    by unfold WhileMinImage.embedPath0 embedLimit Layout.sym_stack_top Layout.sym_stack_size; omega⟩]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [WhileMinImage.embedPath0_byte_0]; rfl
  · rw [WhileMinImage.embedPath0_byte_1]; rfl
  · rw [WhileMinImage.embedPath0_byte_2]; rfl
  · rw [WhileMinImage.embedPath0_byte_3]; rfl
  · rw [WhileMinImage.embedPath0_byte_4]; rfl
  · rw [WhileMinImage.embedPath0_byte_5]; rfl

theorem EmbedImage.prog_slash {c} (h : EmbedImage c) : SlashString c.σ.mem progName 4 where
  region := ⟨by decide, by decide, Or.inr (by decide)⟩
  free := fun j hj => by
    have e := h.fs_byte (j + 1) (by omega)
    rw [show WhileMinImage.embedPath0 + (j + 1) = progName.toNat + j by
      unfold WhileMinImage.embedPath0; simp only [progName]; rw [BitVec.toNat_ofNat]; omega] at e
    rw [e]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide
  nul := by
    have e := h.fs_byte 5 (by omega)
    rw [show WhileMinImage.embedPath0 + 5 = progName.toNat + 4 by decide] at e
    rw [e]; rfl

theorem EmbedImage.prog_plan {c} (h : EmbedImage c) : StrchrPlan c.σ.mem progName 4 := by
  have word : wordAt c.σ.mem (nameCursor progName 2) = 0x676f#64 := by
    unfold wordAt
    rw [show (nameCursor progName 2).toNat = 0x86802540 by decide]
    exact (h.fs_word _ (by decide) (by decide)).trans WhileMinImage.embedPath0_word_86802540
  refine .first 2 (by decide) (fun j hj => ?_) (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ ?_
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
  · rw [word]; decide

theorem EmbedImage.prog_cbytes {c} (h : EmbedImage c) : CBytes c.σ.mem progName.toNat 4 where
  nz := fun i hi => by
    have := (h.prog_slash.free i hi).1
    exact this
  nul := h.prog_slash.nul
  lo := by decide
  hi := by decide
  htif := Or.inr (by decide)
end OCaml.Vm.Boot.Startup
