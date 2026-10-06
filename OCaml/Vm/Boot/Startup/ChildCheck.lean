import OCaml.Vm.Boot.Startup.ChildUsedNormalized
import OCaml.Vm.Boot.Startup.ChildUsedImage
import OCaml.Vm.Boot.Startup.ChildLinkedNormalized
import OCaml.Vm.Boot.Startup.ChildLinkedImage
import OCaml.Vm.Boot.Startup.ChildParentNormalized
import OCaml.Vm.Boot.Startup.ChildParentImage
import OCaml.Vm.Boot.Startup.ChildLengthNormalized
import OCaml.Vm.Boot.Startup.ChildLengthImage
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import OCaml.Vm.Primitives.Word32Access
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! One slot of htif.c's `child(d, n, k)` scan: a `struct mfile` at `p` with
`used` at +0, `linked` at +2, `parent` (int) at +4 and `nlen` at +16. -/

def slotUsed (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) : BitVec 8 := (m[p]?).getD 0
def slotLinked (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) : BitVec 8 := (m[p + 2]?).getD 0
def slotParent (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) : BitVec 64 := bytesVal .lw (read4 m (p + 4))
def slotLength (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) : BitVec 64 := bytesT m (p + 16) 8

/-- How the slot at `p` fails to be directory `d`'s entry of length `k`. -/
inductive SlotMiss (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) (d k : BitVec 64) : Prop
  | unused : slotUsed m p = 0#8 → SlotMiss m p d k
  | unlinked : slotUsed m p ≠ 0#8 → slotLinked m p = 0#8 → SlotMiss m p d k
  | parent : slotUsed m p ≠ 0#8 → slotLinked m p ≠ 0#8 → slotParent m p ≠ d → SlotMiss m p d k
  | length : slotUsed m p ≠ 0#8 → slotLinked m p ≠ 0#8 → slotParent m p = d → slotLength m p ≠ k →
      SlotMiss m p d k

/-- The value the failed test leaves in a5. -/
def slotMissValue (m : Std.ExtHashMap Nat (BitVec 8)) (p : Nat) (d : BitVec 64) : BitVec 64 :=
  if slotUsed m p = 0#8 then 0#64 else if slotLinked m p = 0#8 then 0#64
  else if slotParent m p ≠ d then slotParent m p else slotLength m p

/-- A slot inside RAM below the HTIF registers. -/
structure SlotWindow (p : BitVec 64) : Prop where
  lower : 0x80000000 ≤ p.toNat
  upper : p.toNat + 24 ≤ Layout.sym_tohost

theorem SlotWindow.read {p : BitVec 64} (h : SlotWindow p) (off w : Nat) (fits : off + w ≤ 24) :
    ReadWindow (p + BitVec.ofNat 64 off) w := by
  have lo := h.lower
  have hi := h.upper
  have tohost : Layout.sym_tohost < 0x100000000 := by decide
  have nat : (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : off < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, by omega, Or.inl (by omega)⟩

theorem SlotWindow.nat {p : BitVec 64} (h : SlotWindow p) {off : Nat} (fits : off ≤ 24) :
    (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
  have hi := h.upper
  have tohost : Layout.sym_tohost < 0x100000000 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : off < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]

def childCheckInput (p d k a0 : BitVec 64) : GRegs := [(8, p), (19, d), (20, k), (10, a0)]

theorem child_check (c : Config) (ra p d k a0 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (childCheckInput p d k a0)) (window : SlotWindow p) (miss : SlotMiss c.σ.mem p.toNat d k) :
    FnSummary 0x8000008c#64 (fun e => e = c)
      (WriteRegistersPost [15] [] c 0x80000080#64 a0
        [(15, slotMissValue c.σ.mem p.toNat d), (8, p), (19, d), (20, k), (10, a0)]) := by
  rcases miss with used | ⟨used, linked⟩ | ⟨used, linked, parent⟩ | ⟨used, linked, parent, length⟩
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput childX008cTSeg 0x8000008c#64 (childCheckInput p d k a0)
          [[slotUsed c.σ.mem p.toNat]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [8, 19, 20, 10]; decide
        shape := by change ChainOK _ [8, 19, 20, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := childUsed_code leaf.image
          chain_facts code with "Vsa.Sim.Code.child_at_"
          · exact (window.read 0 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotUsed c.σ.mem p.toNat]) 0#64 = true
            rw [used]; rfl }))
    · rfl
    · rfl
    · change [(15, bytesVal .lbu [slotUsed c.σ.mem p.toNat]), (8, p), (19, d), (20, k), (10, a0)] = _
      unfold slotMissValue
      rw [if_pos used, used]
      rfl
    · rfl
    · decide
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (childX008cFSeg ++ childX0094TSeg) 0x8000008c#64 (childCheckInput p d k a0)
          [[slotUsed c.σ.mem p.toNat], [slotLinked c.σ.mem p.toNat]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [8, 19, 20, 10]; decide
        shape := by change ChainOK _ [8, 19, 20, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := childUsed_code leaf.image
          chain_facts code with "Vsa.Sim.Code.child_at_"
          · exact (window.read 0 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotUsed c.σ.mem p.toNat]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of used (by decide))
          · exact (window.read 2 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotLinked c.σ.mem p.toNat]) 0#64 = true
            rw [linked]; rfl
        }))
    · rfl
    · rfl
    · change [(15, bytesVal .lbu [slotLinked c.σ.mem p.toNat]), (8, p), (19, d), (20, k), (10, a0)] = _
      unfold slotMissValue
      rw [if_neg used, if_pos linked, linked]; rfl
    · rfl
    · decide
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (childX008cFSeg ++ childX0094FSeg ++ childX009cTSeg) 0x8000008c#64 (childCheckInput p d k a0)
          [[slotUsed c.σ.mem p.toNat], [slotLinked c.σ.mem p.toNat], read4 c.σ.mem (p.toNat + 4)] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [8, 19, 20, 10]; decide
        shape := by change ChainOK _ [8, 19, 20, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := childUsed_code leaf.image
          chain_facts code with "Vsa.Sim.Code.child_at_"
          · exact (window.read 0 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotUsed c.σ.mem p.toNat]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of used (by decide))
          · exact (window.read 2 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotLinked c.σ.mem p.toNat]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of linked (by decide))
          · exact (window.read 4 4 (by decide)).lw rfl rfl (by rw [window.nat (by decide)]; exact read4_pins _ _)
          · change guardB bop.BNE (slotParent c.σ.mem p.toNat) d = true
            exact bne_iff_ne.mpr parent
        }))
    · rfl
    · rfl
    · change [(15, slotParent c.σ.mem p.toNat), (8, p), (19, d), (20, k), (10, a0)] = _
      unfold slotMissValue
      rw [if_neg used, if_neg linked, if_pos parent]
    · rfl
    · decide
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (childX008cFSeg ++ childX0094FSeg ++ childX009cFSeg ++ childX00a4TSeg) 0x8000008c#64 (childCheckInput p d k a0)
          [[slotUsed c.σ.mem p.toNat], [slotLinked c.σ.mem p.toNat], read4 c.σ.mem (p.toNat + 4),
            read8 c.σ.mem (p.toNat + 16)] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [8, 19, 20, 10]; decide
        shape := by change ChainOK _ [8, 19, 20, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := childUsed_code leaf.image
          chain_facts code with "Vsa.Sim.Code.child_at_"
          · exact (window.read 0 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotUsed c.σ.mem p.toNat]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of used (by decide))
          · exact (window.read 2 1 (by decide)).lbu rfl rfl (by rw [window.nat (by decide)]; rfl)
          · change guardB bop.BEQ (bytesVal .lbu [slotLinked c.σ.mem p.toNat]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of linked (by decide))
          · exact (window.read 4 4 (by decide)).lw rfl rfl (by rw [window.nat (by decide)]; exact read4_pins _ _)
          · change guardB bop.BNE (slotParent c.σ.mem p.toNat) d = false
            rw [parent]; exact bne_self_eq_false d
          · exact (window.read 16 8 (by decide)).ld rfl rfl (by rw [window.nat (by decide)]; exact read8_pins _ _)
          · change guardB bop.BNE (bytesVal .ld (read8 c.σ.mem (p.toNat + 16))) k = true
            rw [read8_value]
            exact bne_iff_ne.mpr length
        }))
    · rfl
    · rfl
    · change [(15, bytesVal .ld (read8 c.σ.mem (p.toNat + 16))), (8, p), (19, d), (20, k), (10, a0)] = _
      unfold slotMissValue
      rw [if_neg used, if_neg linked, if_neg (fun h => h parent), read8_value]; rfl
    · rfl
    · decide
end OCaml.Vm.Boot.Startup
