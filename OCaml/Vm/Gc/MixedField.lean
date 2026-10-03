import OCaml.Vm.Gc.CopyContext
import OCaml.Vm.Gc.CopyProgress

namespace OCaml.Vm.Gc.MixedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The runtime's exact strict nursery test, including the immediate bit. -/
def needsOldify (domain value : BitVec 64) (c : Config) : Prop :=
  value.toNat % 2 = 0 ∧ (Young.lowerWord domain c).toNat < value.toNat ∧
    value.toNat < (Young.upperWord domain c).toNat

instance (domain value : BitVec 64) (c : Config) : Decidable (needsOldify domain value c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Shared machine inputs for either real field route. The forwarding
conditions are required only when the loaded value needs oldification. -/
structure Input (R : Nat → BitVec 64) (domain : BitVec 64) (c : Config) : Prop where
  read : FieldCopy.ReadInput (R 8) (R 18) (R 19) (R 9) c
  oldifyCode : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (ForwardedField.carried R)
  header : ReadWindow (R 19 - 8#64) 8
  destination : WriteWindow (R 18 + R 8) 8
  domainReg : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  root : word c Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  stackWindows : ∀ cell ∈ OldifyEntry.saves,
    WriteWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2) 8
  forwarded : needsOldify domain (word c (R 8).toNat) c →
    ForwardedCall.Conditions (ForwardedField.args R c) domain c

/-- Native register map after the actually selected field route. -/
def next (R : Nat → BitVec 64) (oldify : Bool) :=
  if oldify then ForwardedField.next R else FieldCopy.copyNext R

/-- The common progress interface additionally retains the context needed
to process another field, whichever route the current field takes. -/
structure Post (R : Nat → BitVec 64) (domain : BitVec 64) (a b count start i : Nat)
    (expected : Nat → BitVec 64) (before after : Config) : Prop where
  progress : FieldCopy.ScanProgress [1,8,9,10,11,12,14,15] a b count start i
    (MopupCall.scanFootprint R b start count) expected before after
  oldifyCode : Code.Caml_oldify_oneLoaded after.σ.mem
  registers : GHolds after.σ (ForwardedField.carried
    (next R (decide (needsOldify domain (word before (R 8).toNat) before))))

/-- One mixed scan iteration executes the actual immediate/non-young copy
or complete already-forwarded oldify route. This is not a branch oracle:
the case split uses the loaded word and runtime bounds at the entry state. -/
theorem step {R domain a b count start i c expected}
    (input : Input R domain c)
    (geometry : FieldCopy.Geometry a b count)
    (slot : R 8 = scanPtr a i)
    (delta : R 18 = BitVec.ofNat 64 b - BitVec.ofNat 64 a)
    (target : R 19 = BitVec.ofNat 64 b)
    (index : R 9 = BitVec.ofNat 64 i)
    (stack : (MopupCall.nativeWindow R).hi ≤ b - 8 ∨
      b + 8 * count ≤ (MopupCall.nativeWindow R).lo)
    (header : (word c (b - 8)).toNat / 1024 = count)
    (value : expected i = if needsOldify domain (word c (R 8).toNat) c
      then word c (word c (R 8).toNat).toNat else word c (R 8).toNat)
    (lower : start ≤ i) (bound : i < count) :
    FnSummary FieldCopy.pc (fun d => d = c) (Post R domain a b count start i expected c) := by
  by_cases young : needsOldify domain (word c (R 8).toNat) c
  · have forwarded : ForwardedField.Input R domain c :=
      ⟨input.read.good, input.read.minstret, input.read.tick, input.read.code,
        input.oldifyCode, input.registers, input.read.window, input.header,
        input.domainReg, input.stackWindows, young.1, input.forwarded young⟩
    apply (ForwardedField.forwarded_field forwarded).weaken (fun _ h => h)
    intro after post
    refine ⟨forwarded.scan_progress post geometry slot delta target index stack header ?_ lower bound,
      forwarded.oldifyCode_after post, ?_⟩
    · simpa only [ite_eq_left young] using value.symm
    · simpa only [decide_eq_true young, next, ite_true] using forwarded.next_registers post
  · have safe : (word c (R 8).toNat).toNat % 2 = 0 →
        ¬ ((Young.lowerWord domain c).toNat < (word c (R 8).toNat).toNat ∧
          (word c (R 8).toNat).toNat < (Young.upperWord domain c).toNat) :=
      fun even bounds => young ⟨even,bounds⟩
    apply (FieldCopy.copy_nonYoung input.read input.domainReg input.root input.windows safe
      input.destination input.header).weaken (fun _ h => h)
    intro after post
    have normalized : FieldCopy.CopyEffect [1,8,9,10,11,12,14,15]
        (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
        (BitVec.ofNat 64 b) (BitVec.ofNat 64 i) c after := by
      simpa only [slot,delta,target,index] using post.mono
        (show ∀ n ∈ FieldCopy.copyWrites, n ∈ [1,8,9,10,11,12,14,15] from by decide)
    refine ⟨normalized.progress geometry lower bound header (fun _ h => h.2) ?_,
      post.oldifyCode_after input.oldifyCode input.destination, ?_⟩
    · have same : (R 8).toNat = a + 8 * i := by
        rw [slot, geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)]
      rw [ite_eq_right young] at value
      simpa only [same] using value.symm
    · simpa only [decide_eq_false young, next, Bool.false_eq_true, ite_false] using
        post.next_registers input.registers

end OCaml.Vm.Gc.MixedField
