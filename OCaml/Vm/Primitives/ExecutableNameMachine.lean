import OCaml.Vm.Primitives.ExecutableNameTail
import OCaml.Vm.Primitives.StringCopyMachine

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris.Inst StringCopy

/-- The executable-name primitive loads its global C-string pointer and
executes the complete native copy function. -/
theorem executable_name_machine {live Dt DA ra nativeSp a len g domain young limit}
    (c : Config) (h : CopyInput live Dt DA ra nativeSp a len g domain young limit c)
    (source : word c Layout.sym_caml_exe_name = BitVec.ofNat 64 a) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_sys_executable_name) (fun d => d = c)
      (CopyPost live ra nativeSp a len g domain young c) := by
  apply summary_bind (ExecutableNameTail.tail_fast c ra h.toLeafInput) (fun _ p => p.pc)
  intro entered p
  have leaf : LeafInput ra entered :=
    ⟨p.good, p.image, p.minstret, gholds_lookup _ p.regs rfl, h.aligned, p.tick⟩
  have good := p.vsaOk (log := []) h.libraryGood (by decide) (by simp [keysG])
  have gp := p.toEffectPost.gpr_frame (by decide) 3 (by decide) (by decide) (by decide)
  have stack := (p.toEffectPost.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans h.stack
  have input := h.memory_transport p.memory gp leaf good stack
  apply (copy_string_machine entered input (p.result.trans (congrArg some source))).weaken (fun _ eq => eq)
  intro after finish
  refine { finish with memory := ?_, output := ?_, registers := ?_ }
  · intro x outside
    simpa only [p.memory] using finish.memory x outside
  · exact finish.output.trans (by simp only [output, p.output])
  · intro n low high untouched
    apply (finish.registers n low high untouched).trans
    apply p.toEffectPost.gpr_frame (by decide) n low high
    simp only [copyWrites, List.mem_cons, List.mem_nil_iff, or_false] at untouched ⊢
    omega

end OCaml.Vm.Primitives
