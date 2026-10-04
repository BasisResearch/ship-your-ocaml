import OCaml.Vm.Boot.Startup.FindCount
import OCaml.Vm.Boot.Startup.StrncmpEqual
import OCaml.Vm.Boot.Startup.EqualPrefixFrame
import OCaml.Vm.Primitives.RegisterPins
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def findComparedRegs (sp name entry : BitVec 64) (count : Nat) (byte : Nat → BitVec 8) : GRegs :=
  strncmpEqualRegs entry name jal_800374c8_call.link (count - 1) byte ++
    [(8, BitVec.ofNat 64 count), (2, nativeStack sp 80), (18, name)]

/-- Save s0, call the actual bounded comparator, and return its equal-prefix
result with the search's parked frame/name/length registers retained. -/
theorem find_compared (c : Config) (sp s0 name entry ra : BitVec 64) (count : Nat) (byte : Nat → BitVec 8)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findCompareInput sp s0 name (nameCursor name count) entry))
    (positive : 0 < count) (small : count < 2^31)
    (data : EqualPrefix entry name (count - 1) byte c)
    (entryBelow : entry.toNat + count ≤ nativeFrameBase sp 80)
    (nameBelow : name.toNat + count ≤ nativeFrameBase sp 80)
    (unaligned : strncmpAlignment entry name ≠ 0#64) :
    FnSummary 0x800374b8#64 (fun d => d = c)
      (WriteRegistersPost [8, 12, 11, 1, 10, 14, 15] (findCompareLog sp s0) c jal_800374c8_call.link 0#64
        (findComparedRegs sp name entry count byte)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have length : count - 1 + 1 = count := by omega
  obtain ⟨a, run1, prepared⟩ := (find_compare c sp s0 name _ entry ra leaf frame regs).run c ⟨pc, rfl⟩
  have countEq := findCompareCount_cursor name count small
  have holds : GHolds a.σ ([(10, entry), (11, name), (12, BitVec.ofNat 64 count)] ++
      [(8, BitVec.ofNat 64 count), (2, nativeStack sp 80), (18, name)]) := by
    have hs := prepared.regs
    change GHolds a.σ (findCompareRegs sp name (nameCursor name count) entry) at hs
    unfold findCompareRegs at hs
    rw [countEq] at hs
    exact ⟨gholds_lookup (n := 10) _ hs (by rfl), gholds_lookup (n := 11) _ hs (by rfl), gholds_lookup (n := 12) _ hs (by rfl), gholds_lookup (n := 8) _ hs (by rfl), gholds_lookup (n := 2) _ hs (by rfl), gholds_lookup (n := 18) _ hs (by rfl), trivial⟩
  have call := call_registers_summary jal_800374c8_call_shape jal_800374c8_call_decode a
    (jal_800374c8_call_pins prepared.image) prepared.good prepared.image prepared.tick prepared.minstret
    _ holds (by simp only [List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [KeysAvoidRa, List.cons_append, List.nil_append, keysG]; decide) (by rfl)
  obtain ⟨b, run2, called⟩ := call.run a ⟨prepared.pc, rfl⟩
  have dataA := data.stack_log (by omega) (by omega) (findCompareLog_inside frame) prepared.memory
  have dataB := dataA.same_mem called.memory
  have args : GHolds b.σ (strncmpFirstInput entry name (BitVec.ofNat 64 (count - 1 + 1))) := by
    rw [length]
    exact ⟨gholds_lookup (n := 10) _ called.regs (by rfl), gholds_lookup (n := 11) _ called.regs (by rfl), gholds_lookup (n := 12) _ called.regs (by rfl), trivial⟩
  obtain ⟨after, run3, post⟩ := (strncmp_equal b entry name _ (count - 1) byte (called.leaf (by rfl) (by decide)) dataB args unaligned).run b ⟨called.pc, rfl⟩
  have parked : GHolds b.σ [(8, BitVec.ofNat 64 count), (2, nativeStack sp 80), (18, name)] :=
    ⟨gholds_lookup (n := 8) _ called.regs (by rfl), gholds_lookup (n := 2) _ called.regs (by rfl), gholds_lookup (n := 18) _ called.regs (by rfl), trivial⟩
  have kept := holds_frame_ne post.frame parked (by simp only [keysG]; decide)
    (by simp only [keysG]; decide) (by simp only [keysG]; decide)
  have effects := (prefix_readonly_post prepared (prefix_readonly_post (log := []) called post)).toEffectPost.widen
    (writes' := [8, 12, 11, 1, 10, 14, 15]) (by decide)
  exact ⟨after, run1.trans (run2.trans run3), ⟨effects, (gholds_append _ _).mpr ⟨post.regs, kept⟩⟩⟩
end OCaml.Vm.Boot.Startup
