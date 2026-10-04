import OCaml.Vm.Boot.Startup.MinorTableNext0Normalized
import OCaml.Vm.Boot.Startup.MinorTableNext1Normalized
import OCaml.Vm.Boot.Startup.MinorTableNext0CallInterface
import OCaml.Vm.Boot.Startup.MinorTableNext1CallInterface
import OCaml.Vm.Boot.Startup.TableReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def tableNextEntry (last : Bool) : BitVec 64 := if last then 0x80009870#64 else 0x80009848#64
def tableNextBlocks (last : Bool) : List BBlock :=
  if last then caml_alloc_minor_tablesX9870Seg else caml_alloc_minor_tablesX9848Seg
def tableNextCall (last : Bool) : CallInstr := if last then jal_80009878_call else jal_80009850_call
def tableNextRegs : GRegs := [(9, firstDomainPtr), (10, 56#64), (8, BitVec.ofNat 64 Layout.sym_Caml_state)]

theorem tableNext_shape (last : Bool) : CallShape (tableNextCall last) := by
  cases last
  · exact jal_80009850_call_shape
  · exact jal_80009878_call_shape

theorem tableNext_decode (last : Bool) : CallDecode (tableNextCall last) := by
  cases last
  · exact jal_80009850_call_decode
  · exact jal_80009878_call_decode

theorem tableNext_pins (last : Bool) {c : Config} (h : ExecutableImage c) : CallPins (tableNextCall last) c := by
  cases last
  · exact jal_80009850_call_pins h
  · exact jal_80009878_call_pins h

/-- Both remaining allocations reload the domain and request 56 bytes. -/
theorem table_next_prefix (c : Config) (last : Bool) (ra : BitVec 64) (h : LeafInput ra c)
    (globalReg : gprGet c.σ 8 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary (tableNextEntry last) (fun d => d = c)
      (BoundaryPost [10, 9] c ra (tableNextCall last).pc tableNextRegs) := by
  have loaded : bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state) = firstDomainPtr :=
    (read8_value _ _).trans domain
  have input : BlockInput (tableNextBlocks last) (tableNextEntry last)
      [(8, BitVec.ofNat 64 Layout.sym_Caml_state)] [read8 c.σ.mem Layout.sym_Caml_state] c := {
    good := h.good
    minstret := h.minstret
    regs := ⟨globalReg, trivial⟩
    keys := by decide
    shape := by cases last <;> decide
    tick := h.tick
    facts := by
      have code := minorTables_code h.image
      cases last <;> chain_facts code with "Vsa.Sim.Code.caml_alloc_minor_tables_at_"
      all_goals apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_Caml_state) (by constructor <;> decide) rfl rfl
      all_goals exact read8_pins _ _ }
  apply boundary_of_blocks h (block_summary _ _ _ _ _ input)
  · cases last <;> rfl
  · cases last <;> rfl
  · intro σ pins
    cases last <;> change GHolds σ [(9, bytesVal .ld (read8 c.σ.mem Layout.sym_Caml_state)),
      (10, 56#64), (8, BitVec.ofNat 64 Layout.sym_Caml_state)] at pins
    all_goals rw [loaded] at pins; exact pins
  · cases last <;> decide
  · decide

/-- The argument prefix and source JAL reach the stat-allocation wrapper. -/
theorem table_next (c : Config) (last : Bool) (ra : BitVec 64) (h : LeafInput ra c)
    (globalReg : gprGet c.σ 8 = some (BitVec.ofNat 64 Layout.sym_Caml_state))
    (domain : bytesT c.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr) :
    FnSummary (tableNextEntry last) (fun d => d = c)
      (WriteRegistersPost [10, 9, 1] [] c (tableNextCall last).target 56#64
        ((1, (tableNextCall last).link) :: tableNextRegs)) := by
  apply boundary_bind (table_next_prefix c last ra h globalReg domain)
  intro a setup
  have front : WriteRegistersPost [10, 9] [] c (tableNextCall last).pc 56#64 tableNextRegs a :=
    ⟨⟨setup.good, setup.image, setup.minstret, setup.tick, setup.pc,
      gholds_lookup _ setup.regs (by rfl), setup.memory, setup.output, setup.frame⟩, setup.regs⟩
  have call := call_registers_summary (tableNext_shape last) (tableNext_decode last) a
    (tableNext_pins last setup.image) setup.good setup.image setup.tick setup.minstret
    tableNextRegs setup.regs (by decide) (by simp [KeysAvoidRa, keysG, tableNextRegs]) (by rfl)
  exact call.weaken (fun _ eq => eq) (fun _ post => prefix_call_post front post)
end OCaml.Vm.Boot.Startup
