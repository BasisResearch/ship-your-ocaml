import OCaml.Vm.Boot.Startup.SetupElf
import OCaml.Vm.Boot.Startup.ToCamlMain
import OCaml.Vm.Boot.Startup.Crt0Image
import OCaml.Vm.Boot.Startup.MainImage
open Vsa.Machine Vsa.Sim
namespace OCaml.Vm.Boot.Startup

/-- Reset retains the immutable bytes of the while_min loader image. -/
theorem reset_image {elf : ELF64File} {c : Config} (image : WhileMinElf elf)
    (reset : ElfResetReady elf c) : ExecutableImage c where
  text := by rw [reset.memory, image.memory]; exact WhileMinImage.initial_text
  rodata := by rw [reset.memory, image.memory]; exact WhileMinImage.initial_rodata

/-- The same exact image pins hold after totalizing absent memory bytes. -/
theorem reset_image_fillZero {elf : ELF64File} {c : Config} (image : WhileMinElf elf)
    (reset : ElfResetReady elf c) : ExecutableImage (Vsa.Densify.fillZero c) where
  text := fun i hi => Vsa.Densify.fillZeroMem_some ((reset_image image reset).text i hi)
  rodata := fun i hi => Vsa.Densify.fillZeroMem_some ((reset_image image reset).rodata i hi)

structure ResetCamlMainPost (initial after : Config) : Prop extends CrtCamlMainPost (Vsa.Densify.fillZero initial) after where
  run : Steps (Vsa.Densify.fillZero initial) after

/-- Execution from the ELF's own reset configuration through crt0 and main.
The remaining `WhileMinElf` premise describes loader bytes and metadata only. -/
theorem reset_to_caml_main {elf : ELF64File} {c : Config} (image : WhileMinElf elf)
    (reset : ElfReset elf c) : ∃ d, ResetCamlMainPost c d := by
  have ready := reset.ready image.tohost
  have code := reset_image_fillZero image ready
  have crt : CrtReady (Vsa.Densify.fillZero c) := {
    good := ready.good.set_mem _, code := crt0_code code
    tick := by change c.tick < 2; rw [reset.tick]; decide }
  have pc : PCAt (BitVec.ofNat 64 Layout.sym_start) (Vsa.Densify.fillZero c) := by
    change c.σ.regs.get? .PC = _
    rw [reset.pc, image.entry]
  obtain ⟨d, run, post⟩ := (crt0_to_caml_main _ crt (main_code code)).run _ ⟨pc, rfl⟩
  exact ⟨d, {toCrtCamlMainPost := post, run := run}⟩
end OCaml.Vm.Boot.Startup
