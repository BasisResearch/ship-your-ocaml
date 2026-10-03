import OCaml.Vm.Boot.Startup.LookupCompare

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.MemRepr LeanRV64DExecutable OCaml.Vm.Primitives

/-- Memory-only requirements supplied by the primitive-name table and required name. -/
structure NameMemory (pa pb : BitVec 64) (sa sb : String) (m : Mem) : Prop where
  code : Code.StrcmpLoaded m
  left : CString m pa.toNat sa
  right : CString m pb.toNat sb
  mask : MaskPinned m
  leftWindow : ∀ cs, CStr m pa.toNat cs → StrcmpWSlack pa cs.length
  rightWindow : ∀ cs, CStr m pb.toNat cs → StrcmpWSlack pb cs.length

structure LookupHeadPost (sa sb : String) (before after : Config) : Prop where
  ready : LookupReady after
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  pc : PCAt (if sa = sb then 0x80024e3c#64 else 0x80024e1c#64) after
  frame : ∀ r, NotWrittenStrcmp r → r ≠ .x1 →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- One complete comparison at the loop head, including argument setup and JAL. -/
theorem lookup_head (c : Config) (pa pb : BitVec 64) (sa sb : String)
    (ready : LookupReady c) (memory : NameMemory pa pb sa sb c.σ.mem)
    (left : gprGet c.σ 9 = some pa) (right : gprGet c.σ 11 = some pb) :
    FnSummary 0x80024e30#64 (fun d => d = c) (LookupHeadPost sa sb c) := by
  constructor
  rintro d ⟨pc, eq⟩
  subst d
  obtain ⟨arg, argRun, argPost⟩ := (block_summary _ _ _ _ _
    (lookup_argument_input ready left)).run c ⟨pc, rfl⟩
  have am : arg.σ.mem = c.σ.mem := argPost.memory
  have ac : Code.Caml_build_primitive_tableLoaded arg.σ.mem := by rw [am]; exact ready.code
  obtain ⟨call, callRun, callPost⟩ := (call_80024e34 arg argPost.good argPost.tick ac).run arg
    ⟨argPost.pc, rfl⟩
  have cm : call.σ.mem = c.σ.mem := callPost.memory.trans am
  have a0 : gprGet arg.σ 10 = some pa := by
    have regs := argPost.regs
    change gprGet arg.σ 10 = some (pa + 0#64) ∧ _ at regs
    simpa only [BitVec.add_zero] using regs.1
  have a1 : gprGet arg.σ 11 = some pb :=
    (argPost.frame .x11 (by decide) (by decide)).trans right
  have pre : StrcmpEntryCond (fun r => call.σ.regs.get? r) pa pb 0x80024e38#64
      sa sb c.σ.mem c.σ.sailOutput call := {
    good := callPost.good, loaded := by rw [cm]; exact memory.code,
    mem := cm, out := callPost.output.trans argPost.output, pc := callPost.pc,
    a0 := (callPost.frame .x10 (by decide) (by decide)).trans a0,
    a1 := (callPost.frame .x11 (by decide) (by decide)).trans a1,
    ra := callPost.linkReg, minstret := callPost.good.minstret,
    tick := callPost.tick, ralign := by decide,
    cstra := memory.left, cstrb := memory.right, maskpin := memory.mask,
    wrega := memory.leftWindow, wregb := memory.rightWindow, frame := by intros; rfl }
  obtain ⟨after, compareRun, post⟩ := lookup_compare _ pa pb sa sb _ _ ready.code call pre
  refine ⟨after, argRun.trans (callRun.trans compareRun),
    ⟨post.ready, post.memory_eq, post.output_eq, post.pc, ?_⟩⟩
  intro r hr hlink
  have noise := strcmp_frame_noise hr
  apply (post.frame r hr).trans
  apply (callPost.frame r noise hlink).trans
  apply argPost.frame r noise
  have dest : (.x10 == r) = false := by simp_all [NotWrittenStrcmp]
  change ∀ n ∈ [10], (gprReg n == r) = false
  intro n hn
  have : n = 10 := List.mem_singleton.mp hn
  subst n
  exact dest

end OCaml.Vm.Boot.Startup
