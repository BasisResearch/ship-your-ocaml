import OCaml.Vm.Primitives.ExitPath.Machine
import OCaml.Vm.Primitives.ExitPath.LibcExitHandlerBlocks

/-!
# libc `exit` with the stdio exit handler installed

Once stdio has been used (`__sinit`), `__stdio_exit_handler` holds
`stdio_exit_handler`, and `exit` calls it after `__call_exitprocs`: it walks
the standard streams and closes them (`_fwalk_sglue` with `_fclose_r`). That
callee is a named obligation (`StdioExitHandler`); the rest of `exit` is
`exit_procs_run` and `exit_tail_run`, shared with the null-handler path.
-/

namespace OCaml.Vm.Primitives.ExitPath
open Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

/-- `stdio_exit_handler`, the handler `__sinit` installs. -/
def stdioExitHandlerFn : BitVec 64 := 0x8003e900#64

/-- Back in `exit` at `0x800373f0` after the handler. -/
structure HandlerReturned (code : BitVec 64) (c e : Config) : Prop where
  ok : ExitOk e
  image : ExecutableImage e
  minstret : ∃ v, e.σ.regs.get? Register.minstret = some v
  pc : pcOf e = some 0x800373f0#64
  raReg : ∃ ra, gpr e 1 = some ra ∧ ra.toNat % 4 = 0
  codeReg : gpr e 8 = some code
  output : Vsa.Machine.output e.σ = Vsa.Machine.output c.σ

/-- **Named obligation: newlib's `stdio_exit_handler` returns** to `exit`,
keeping `s0` (the status) and printing nothing: the standard streams hold
no pending stdio output at exit (the runtime writes through its own
channels, and `stderr` is unbuffered). Supplied by a summary of
`_fwalk_sglue`/`_fclose_r` on the three standard streams (stdio step tables,
A0). -/
structure StdioExitHandler (sp code : BitVec 64) : Prop where
  returns : ∀ c, pcOf c = some stdioExitHandlerFn → ExitOk c → ExecutableImage c →
    (∃ v, c.σ.regs.get? Register.minstret = some v) →
    gpr c 1 = some 0x800373f0#64 → gpr c 2 = some (sp - 16#64) → gpr c 8 = some code →
    ∃ e, Steps c e ∧ HandlerReturned code c e

/-- **libc `exit(code)` with the stdio exit handler installed** halts the
machine with the low 32 bits of `code` and the console output so far. -/
theorem libc_exit_handler_halts {ra sp code d} (h : ExitEntry ra sp code d)
    (installed : bytesVal .ld (read8 d.σ.mem stdioExitHandler.toNat) = stdioExitHandlerFn)
    (handler : StdioExitHandler sp code) (entry : pcOf d = some 0x800373c8#64) :
    Halts d (Vsa.Machine.output d.σ) (exitStatus code).toNat := by
  have L := h.layout
  obtain ⟨d1, run1, done⟩ := (exit_procs_run h).run d ⟨entry, rfl⟩
  have link : LibcExit.enter_call.link.toNat % 4 = 0 := by decide
  have slot : (0x80064d38#64 : BitVec 64).toNat = stdioExitHandler.toNat := rfl
  have set1 : bytesVal .ld (read8 d1.σ.mem stdioExitHandler.toNat) = stdioExitHandlerFn := by
    rw [done.ctx.read (L.globals _ (by simp))]; exact installed
  -- the handler is set: `bnez`
  have a1 := done.ctx.present 10 (by decide)
  let R1 : Nat → BitVec 64 := fun n => if n = 1 then LibcExit.enter_call.link else
    if n = 8 then code else (gpr d1 10).getD 0
  obtain ⟨d2, run2, p2⟩ := (LibcExitHandlerBlocks.handlerSome_fast d1 R1 (done.ctx.leaf done.raReg link)
    ⟨done.raReg, done.codeReg, a1, True.intro⟩
    (by simp only [LibcExitHandlerBlocks.handlerSome_loads, List.getD_cons_zero, slot, set1]; decide)).run d1
    ⟨done.pc, rfl⟩
  have ctx2 := done.ctx.step p2 LogWithin.nil (by decide) (by simp [LibcExitHandlerBlocks.handlerSome_regs, keysG])
  have k2 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [15]) : gpr d2 n = gpr d1 n :=
    p2.toEffectPost.gpr_frame (by decide) n lo hi out
  have f15 : gpr d2 15 = some stdioExitHandlerFn := by
    have := gholds_lookup (n := 15) _ p2.regs rfl
    simp only [LibcExitHandlerBlocks.handlerSome_regs, LibcExitHandlerBlocks.handlerSome_loads, List.getD_cons_zero, slot, set1] at this
    exact this
  -- `jalr a5`
  let R2 : Nat → BitVec 64 := fun n => if n = 1 then LibcExit.enter_call.link else
    if n = 8 then code else if n = 15 then stdioExitHandlerFn else (gpr d1 10).getD 0
  obtain ⟨d3, run3, p3⟩ := (LibcExitHandlerBlocks.callHandler_fast d2 R2
    (ctx2.leaf ((k2 1 (by decide) (by decide) (by decide)).trans done.raReg) link)
    ⟨(k2 1 (by decide) (by decide) (by decide)).trans done.raReg,
      (k2 8 (by decide) (by decide) (by decide)).trans done.codeReg,
      (k2 10 (by decide) (by decide) (by decide)).trans a1, f15, True.intro⟩).run d2 ⟨p2.pc, rfl⟩
  have ctx3 := ctx2.step p3 LogWithin.nil (by decide) (by simp [LibcExitHandlerBlocks.callHandler_regs, keysG])
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gpr d3 n = gpr d2 n :=
    p3.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
  have sp3 : gpr d3 2 = some (sp - 16#64) :=
    (k3 2 (by decide) (by decide)).trans ((k2 2 (by decide) (by decide) (by decide)).trans done.stack)
  let a3 : GRegs := [(15, stdioExitHandlerFn), (2, sp - 16#64), (8, code), (10, (gpr d1 10).getD 0)]
  obtain ⟨d4, run4, p4⟩ := (indirect_registers_summary LibcExitHandlerBlocks.callHandler_call_shape
    LibcExitHandlerBlocks.callHandler_call_decode d3 (LibcExitHandlerBlocks.callHandler_call_pins p3.image) p3.good p3.image p3.tick
    p3.minstret a3
    ⟨gholds_lookup (n := 15) _ p3.regs rfl, sp3, gholds_lookup (n := 8) _ p3.regs rfl,
      gholds_lookup (n := 10) _ p3.regs rfl, True.intro⟩
    (by change KeysOK [15, 2, 8, 10]; decide) (by simp [KeysAvoidRa, a3, keysG]) stdioExitHandlerFn rfl
    (by decide) rfl).run d3 ⟨p3.pc, rfl⟩
  have ctx4 := ctx3.call p4 (by simp [keysG])
  -- the handler, then `mv a0, s0; call _exit`
  obtain ⟨d5, run5, back⟩ := handler.returns d4
    (by have := p4.pc; rw [show LibcExitHandlerBlocks.callHandler_call.target stdioExitHandlerFn = stdioExitHandlerFn by decide]
          at this; exact this)
    ctx4.ok ctx4.image ctx4.minstret
    (by have := gholds_lookup (n := 1) _ p4.regs rfl; rw [LibcExitHandlerBlocks.callHandler_call_link] at this; exact this)
    (gholds_lookup (n := 2) _ p4.regs rfl) (gholds_lookup (n := 8) _ p4.regs rfl)
  obtain ⟨ra5, raReg5, aligned5⟩ := back.raReg
  have ctx5 : ExitCtx (sp.toNat - libcExitDepth) sp.toNat d5 d5 :=
    ⟨back.ok, back.image, back.minstret, rfl, fun _ _ => rfl⟩
  obtain ⟨d6, run6, parked⟩ := (exit_tail_run ctx5 raReg5 aligned5 back.codeReg).run d5 ⟨back.pc, rfl⟩
  have halt := HtifExit.store_halts (exitStatus_small code) parked.ctx.ok.good parked.ctx.image
    parked.pc parked.base (by rw [parked.data, exitStatus_word]) parked.ctx.ok.htifIdle
  rw [parked.ctx.output, back.output, ctx4.output] at halt
  obtain ⟨e', σf, run7, halted, out⟩ := halt
  exact ⟨e', σf, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), halted, out⟩

end OCaml.Vm.Primitives.ExitPath
