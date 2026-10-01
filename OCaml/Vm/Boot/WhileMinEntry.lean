import OCaml.Vm.Boot.WhileMinEntryReads
import Vsa.Sim.Frame

/-! Assembly of the proved entry-memory facts. The remaining control/image/binding
premise must be supplied for the actual Sail cut, along with its memory
projection. This theorem does not assert startup reachability. -/
namespace OCaml.Vm.Boot.WhileMinEntry
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim.Boot WhileMinLog WhileMinHeap

/-- Entry obligations not yet discharged by the memory certificates. The
actual cut must supply control, executable-image and primitive-table facts. -/
structure EntryControl (c : Config) : Prop where
  atEntry : pcOf c = some (BitVec.ofNat 64 Layout.sym_caml_interprete)
  argCode : gpr c 10 = some (BitVec.ofNat 64 place.codeBase)
  argSize : gpr c 11 = some (BitVec.ofNat 64 (4 * whileMin.code.size))
  console : output c.σ = ""
  control : Vsa.Sim.GoodState c.σ
  image : ExecutableImage c
  /-- Startup resolves the PRIM names to their native function pointers. -/
  primitives : PrimitiveBindings whileMin c

/-- All heap, code, globals, stack and runtime obligations follow from the
certified store-log memory. Control, image and primitive bindings remain explicit. -/
theorem loaded {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem (observedMem initial log))
    (entry : EntryControl c) : Loaded (runtimeLayout BestFitSingleton) whileMin c := by
  have dom : (word c Layout.sym_Caml_state).toNat = WhileMinRuntime.domain :=
    congrArg BitVec.toNat (WhileMinRuntime.read_domain memory)
  refine ⟨place, (fun _ => none), high, {
    atEntry := entry.atEntry
    argCode := entry.argCode
    argSize := entry.argSize
    codeBase := congrArg BitVec.toNat (read_caml_start_code memory)
    code := code memory
    globals := (congrArg some (read_caml_global_data memory)).symm
    stackHigh := ?_
    externSp := ?_
    trapsp := ?_
    heap := WhileMinHeap.repr memory
    world := ?_
    platform := ⟨entry.control, entry.image, WhileMinRuntime.runtimeOk memory⟩
    primitives := entry.primitives
  }⟩
  · rw [dom]; exact congrArg BitVec.toNat (read_stack_high memory)
  · rw [dom]; exact congrArg BitVec.toNat (read_extern_sp memory)
  · rw [dom]; exact congrArg BitVec.toNat (read_trapsp memory)
  · refine ⟨entry.console, ?_⟩
    intro id ch hc
    change ([] : List Chan)[id]? = some ch at hc
    simp at hc

/-- Densification preserves control, image bytes and total primitive-table reads. -/
theorem EntryControl.fillZero {c : Config} (h : EntryControl c) :
    EntryControl (Vsa.Densify.fillZero c) where
  atEntry := h.atEntry
  argCode := h.argCode
  argSize := h.argSize
  console := h.console
  control := h.control.set_mem _
  image := {
    text := fun i hi => Vsa.Densify.fillZeroMem_some (h.image.text i hi)
    rodata := fun i hi => Vsa.Densify.fillZeroMem_some (h.image.rodata i hi)
  }

  primitives := h.primitives.of_words fun a =>
    bytesT_memEqv (Vsa.Densify.memEqv_fillZeroMem c.σ.mem).symm a 8

/-- The requested densified entry statement, conditional only on the actual
cut's memory projection and remaining control/image/binding certificate. -/
theorem loaded_fillZero {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : c.σ.mem = observedMem initial log) (entry : EntryControl c) :
    Loaded (runtimeLayout BestFitSingleton) whileMin (Vsa.Densify.fillZero c) :=
  loaded ((Vsa.Densify.memEqv_fillZeroMem c.σ.mem).symm.trans
    (by rw [memory]; exact Vsa.Densify.MemEqv.refl _)) entry.fillZero

end OCaml.Vm.Boot.WhileMinEntry
