import OCaml.Vm.Gc.Generated.FirstYoung
import OCaml.Vm.Gc.YoungAccess

namespace OCaml.Vm.Gc.FirstYoung
open Vsa.Machine Vsa.Sim Primitives

/-- Reuse the suffix site's scalar proofs through generated equivalence;
first-field fetch/decode certificates still pin its own instruction bytes. -/
theorem access {value domain c} (root : word c Layout.sym_Caml_state = domain)
    (windows : Young.Windows domain) : ChainAccess c.σ.mem (regs value) (Young.loads domain c)
      (blocks (Young.above value domain c) (Young.aboveLower value domain c)) :=
  (Young.access root windows).retarget (access_equiv _ _)

def site : Young.Site :=
  ⟨pc, copyPc, oldifyPc, blocks, code_facts, chain_ok, access, no_writes, end_pc⟩

/-- Actual first-field Is_young classifier, sharing strict bound semantics
and the generic machine fold with the suffix site. -/
theorem classify {value domain c} (input : Young.Input value domain c) :
    FnSummary pc (fun d => d = c) (Young.SiteResult site value domain c) :=
  Young.classify_site site input

end OCaml.Vm.Gc.FirstYoung
