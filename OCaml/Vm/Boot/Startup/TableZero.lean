import OCaml.Vm.Boot.Startup.MinorTableZero0Normalized
import OCaml.Vm.Boot.Startup.MinorTableZero1Normalized
import OCaml.Vm.Boot.Startup.MinorTableZero0CallInterface
import OCaml.Vm.Boot.Startup.MinorTableZero1CallInterface
import OCaml.Vm.Boot.Startup.TablePublished
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def tableZeroEntry (second : Bool) : BitVec 64 := if second then 0x80009864#64 else 0x8000983c#64
def tableZeroBlocks (second : Bool) : List BBlock :=
  if second then caml_alloc_minor_tablesX9864Seg else caml_alloc_minor_tablesX983cSeg
def tableZeroCall (second : Bool) : CallInstr := if second then jal_8000986c_call else jal_80009844_call
def tableZeroRegs (p : BitVec 64) : GRegs := [(11, 0#64), (12, 56#64), (10, p)]

theorem tableZero_shape (second : Bool) : CallShape (tableZeroCall second) := by
  cases second
  · exact jal_80009844_call_shape
  · exact jal_8000986c_call_shape

theorem tableZero_decode (second : Bool) : CallDecode (tableZeroCall second) := by
  cases second
  · exact jal_80009844_call_decode
  · exact jal_8000986c_call_decode

theorem tableZero_pins (second : Bool) {c : Config} (h : ExecutableImage c) : CallPins (tableZeroCall second) c := by
  cases second
  · exact jal_80009844_call_pins h
  · exact jal_8000986c_call_pins h

/-- Both ordinary table-zeroing calls share the generated argument setup. -/
theorem table_zero_prefix (c : Config) (second : Bool) (p ra : BitVec 64) (h : LeafInput ra c)
    (pointer : gprGet c.σ 10 = some p) :
    FnSummary (tableZeroEntry second) (fun d => d = c)
      (BoundaryPost [12, 11] c ra (tableZeroCall second).pc (tableZeroRegs p)) := by
  have input : BlockInput (tableZeroBlocks second) (tableZeroEntry second) [(10, p)] [] c := {
    good := h.good
    minstret := h.minstret
    regs := ⟨pointer, trivial⟩
    keys := by change KeysOK [10]; decide
    shape := by cases second <;> change ChainOK _ [10] _ <;> decide
    tick := h.tick
    facts := by
      have code := minorTables_code h.image
      cases second <;> chain_facts code with "Vsa.Sim.Code.caml_alloc_minor_tables_at_" }
  apply boundary_of_blocks h (block_summary _ _ _ _ _ input)
  · cases second <;> rfl
  · cases second <;> rfl
  · intro σ pins
    cases second <;> exact pins
  · cases second <;> decide
  · decide

def tableZeroFinalRegs (second : Bool) (base : Nat) : GRegs :=
  (1, (tableZeroCall second).link) :: (11, 0#64) :: memset56Regs base

/-- The native call setup, JAL and complete memset summary clear a table and
return with an exact allocation-local memory effect. -/
theorem table_zero_registers (c : Config) (second : Bool) (base : Nat) (ra : BitVec 64)
    (region : Memset56Region base) (h : LeafInput ra c)
    (pointer : gprGet c.σ 10 = some (BitVec.ofNat 64 base)) :
    FnSummary (tableZeroEntry second) (fun d => d = c)
      (RegistersPost [12, 11, 1, 6, 14, 15, 13, 5] (memset56Memory c.σ.mem base) c
        (tableZeroCall second).link (BitVec.ofNat 64 base) (tableZeroFinalRegs second base)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, front, setup⟩ := (table_zero_prefix c second _ ra h pointer).run c ⟨pc, rfl⟩
  obtain ⟨b, callRun, call⟩ := (call_registers_summary (tableZero_shape second) (tableZero_decode second)
    a (tableZero_pins second setup.image) setup.good setup.image setup.tick setup.minstret
    (tableZeroRegs _) setup.regs (by change KeysOK [11, 12, 10]; decide)
    (by change KeysAvoidRa [(11, 0#64), (12, 56#64), (10, BitVec.ofNat 64 base)]; simp [KeysAvoidRa, keysG])
    (by rfl)).run a ⟨setup.pc, rfl⟩
  have input : Memset56Input (BitVec.ofNat 64 base) (tableZeroCall second).link b := {
    good := call.good
    image := call.image
    minstret := call.minstret
    raReg := gholds_lookup _ call.regs (by rfl)
    aligned := by cases second <;> decide
    tick := call.tick
    pointer := call.result
    zero := gholds_lookup _ call.regs (by rfl)
    size := gholds_lookup _ call.regs (by rfl)
    alignedPointer := by
      have nat := region.pairs.cursor_nat (k := 0) (by decide)
      simp only [pairCursor, Nat.mul_zero, Nat.add_zero] at nat
      rw [nat]; exact region.aligned }
  have atMemset : PCAt 0x8004276c#64 b := by cases second <;> exact call.pc
  obtain ⟨d, zeroRun, zeroed⟩ := (memset56_registers b base _ region input).run b ⟨atMemset, rfl⟩
  refine ⟨d, front.trans (callRun.trans zeroRun), ?_, ?_⟩
  · refine { zeroed.toEffectPost with memory := ?_, output := ?_, frame := ?_ }
    · rw [zeroed.memory, call.memory, setup.memory]
    · exact zeroed.output.trans (call.output.trans setup.output)
    · have memIncl : ∀ n ∈ [6, 14, 15, 13, 12, 5], n ∈ [12, 11, 1, 6, 14, 15, 13, 5] := by decide
      have callIncl : ∀ n ∈ [1], n ∈ [12, 11, 1, 6, 14, 15, 13, 5] := by decide
      have setupIncl : ∀ n ∈ [12, 11], n ∈ [12, 11, 1, 6, 14, 15, 13, 5] := by decide
      intro r outside noise
      exact (zeroed.frame r (fun n hn => outside n (memIncl n hn)) noise).trans
        ((call.frame r (fun n hn => outside n (callIncl n hn)) noise).trans
          (setup.frame r (fun n hn => outside n (setupIncl n hn)) noise))
  · exact ⟨(zeroed.frame .x1 (by decide) (by decide)).trans
        (gholds_lookup (n := 1) _ call.regs (by rfl)),
      (zeroed.frame .x11 (by decide) (by decide)).trans
        (gholds_lookup (n := 11) _ call.regs (by rfl)), zeroed.regs⟩

/-- Effect-only interface for a complete table-zeroing call. -/
theorem table_zero (c : Config) (second : Bool) (base : Nat) (ra : BitVec 64)
    (region : Memset56Region base) (h : LeafInput ra c)
    (pointer : gprGet c.σ 10 = some (BitVec.ofNat 64 base)) :
    FnSummary (tableZeroEntry second) (fun d => d = c)
      (EffectPost [12, 11, 1, 6, 14, 15, 13, 5] (memset56Memory c.σ.mem base) c
        (tableZeroCall second).link (BitVec.ofNat 64 base)) :=
  (table_zero_registers c second base ra region h pointer).weaken (fun _ eq => eq) (fun _ p => p.toEffectPost)
end OCaml.Vm.Boot.Startup
