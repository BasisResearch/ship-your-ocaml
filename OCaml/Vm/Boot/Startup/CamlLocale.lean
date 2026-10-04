import OCaml.Vm.Boot.Startup.CamlLocalePrefix
import OCaml.Vm.Boot.Startup.ReturnStub
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def camlLocaleRegs (sp s0 s2 s3 s4 : BitVec 64) : GRegs :=
  (1, jal_80004dcc_call.link) :: (10, 1#64) :: camlLocaleParked sp s0 s2 s3 s4

/-- Compose first-start caller saves, the actual locale JAL and the linked
return-only locale hook; preserve every caller register except the link. -/
theorem caml_locale (c : Config) (sp ra s0 s2 s3 s4 : BitVec 64)
    (h : CamlLocaleInput sp ra s0 s2 s3 s4 c) :
    FnSummary 0x80004da8#64 (fun d => d = c)
      (WriteRegistersPost [1] (camlLocaleLog sp s0 s2 s3 s4) c jal_80004dcc_call.link 1#64
        (camlLocaleRegs sp s0 s2 s3 s4)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, saved⟩ := (caml_locale_prefix c sp ra s0 s2 s3 s4 h).run c ⟨pc, rfl⟩
  have args : GHolds a.σ ((10, 1#64) :: camlLocaleParked sp s0 s2 s3 s4) :=
    holds_project saved.regs (by simp [camlLocaleInput, camlLocaleParked, lookupG])
  obtain ⟨b, run2, called⟩ := (call_registers_summary jal_80004dcc_call_shape jal_80004dcc_call_decode a
    (jal_80004dcc_call_pins saved.image) saved.good saved.image saved.tick saved.minstret _ args
    (by change KeysOK [10, 2, 8, 20, 18, 19]; decide)
    (by simp only [KeysAvoidRa, keysG, camlLocaleParked]; decide) (by rfl)).run a ⟨saved.pc, rfl⟩
  have leaf := called.leaf (by rfl) (by decide)
  obtain ⟨after, run3, returned⟩ := (return_stub .locale b _ 1#64 leaf called.result).run b ⟨called.pc, rfl⟩
  have regs := holds_frame_ne returned.frame called.regs
    (by simp only [keysG, camlLocaleParked]; decide)
    (by simp only [keysG, camlLocaleParked]; decide)
    (by simp only [keysG, camlLocaleParked]; decide)
  have effects := ((saved.toEffectPost.trans called.toEffectPost).trans returned.toEffectPost).widen
    (writes' := [1]) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, ?_, effects.output, effects.frame⟩, regs⟩⟩
  have same : after.σ.mem = b.σ.mem := returned.memory
  rw [same, called.memory, saved.memory]
end OCaml.Vm.Boot.Startup
