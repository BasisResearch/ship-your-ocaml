import VsaIris.Vsa.SnpFmt
import OCaml.Vm.Primitives.Format.SvfLong

-- Focused audit for the caller-layout generalization. Run after building both
-- imports with scripts/lean-capped.sh lake env lean <this file>.
#print axioms VsaIris.Sym.ssputs_buf
#print axioms VsaIris.Sym.ssprint_nw
#print axioms VsaIris.Sym.ArgsOut.head
#print axioms VsaIris.Sym.ArgsOut.frames
#print axioms VsaIris.Sym.ArgsOut.tail
#print axioms VsaIris.Sym.ArgsOut.of_spill
#print axioms VsaIris.Sym.svf_entry
#print axioms VsaIris.Sym.svf_stack_owned
#print axioms VsaIris.Sym.svf_convS
#print axioms VsaIris.Sym.svf_intQ
#print axioms VsaIris.Sym.svf_intD
#print axioms VsaIris.Sym.ld_ap
#print axioms VsaIris.Sym.lw_ap
#print axioms VsaIris.Sym.svf_iterS
#print axioms VsaIris.Sym.svf_iterLLD
#print axioms VsaIris.Sym.svf_iterD
#print axioms VsaIris.Sym.svf_fmt
#print axioms VsaIris.Sym.loop_fmt
#print axioms VsaIris.Sym.svfprintf_nw
#print axioms VsaIris.Sym.svf_convL
#print axioms VsaIris.Sym.svf_intL
#print axioms VsaIris.Sym.svf_iterLD
#print axioms VsaIris.Sym.vsnprintf_layout

-- A legal stack placement witnesses that the concrete layout is inhabited.
example : VsaIris.Sym.VsnprintfLayout 0x87fff000 :=
  VsaIris.Sym.vsnprintf_layout (by decide) (by decide) (by decide)
