import OCaml.Vm.Boot.Startup.BacktraceSteps

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Backtrace initialization returned through the first real global-root insertion.
The domain frame refers to the initializer's own entry, before either tail call. -/
structure BacktraceDone (H : List (Nat × Nat)) (capacity : Nat)
    (sp ra : BitVec 64) (before after : Config) where
  atInsert : Config
  memory : atInsert.σ.mem = before.σ.mem
  s0 : BitVec 64
  s1 : BitVec 64
  inserted : Gc.SkiplistFirst.FirstInserted H Gc.SkiplistFirst.startupBlocks capacity sp ra s0 s1
    Gc.SkiplistFirst.startupKey atInsert after
  pc : PCAt ra after
  ready : RuntimeReady ((inserted.native.p.toNat, 24) :: H) capacity sp ra after
  saved : ∀ k ∈ abiSaved, gprGet after.σ k = gprGet before.σ k
  live : LiveFrame Gc.SkiplistFirst.startupBlocks before after
  keyKept : bytesT after.σ.mem Gc.SkiplistFirst.startupKey.toNat 8 =
    bytesT before.σ.mem Gc.SkiplistFirst.startupKey.toNat 8
  htif : after.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes =
    before.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ

/-- Execute both ELF tail calls and the checked first insertion. -/
theorem caml_init_backtrace (c : Config) (H : List (Nat × Nat)) (capacity charge : Nat)
    (sp ra : BitVec 64) (ready : RuntimeReady H (capacity + charge) sp ra c)
    (frame : NativeFrame sp Gc.Skiplist.opStack) (empty : Gc.SkiplistFirst.Empty c.σ.mem)
    (owned : Gc.SkiplistFirst.startupBlock ∈ H) (charged : vsaChg 24 charge) :
    FnSummary 0x8000ef3c#64 (fun d => d = c)
      (fun after => Nonempty (BacktraceDone H capacity sp ra c after)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have small := frame.resize (small := 16) (by decide) (by decide)
  obtain ⟨d, run1, P⟩ := (init_backtrace c ra ready.toLeafInput ready.domainWord).run c ⟨pc, rfl⟩
  have gP := GprsSame.of_post P (by decide)
  have readyD := ready.stack_log P (by decide) (by simp only [keysG]; decide) (by decide)
    (gP.get (by decide) (by decide) (by decide) ready.stack)
    (gP.get (by decide) (by decide) (by decide) ready.raReg) ready.aligned small (by simp only [LogInW])
  obtain ⟨e, run2, Q⟩ := (register_global_root d ra Gc.SkiplistFirst.startupKey readyD.toLeafInput
    (gholds_lookup (n := 10) _ P.regs rfl)).run d ⟨P.pc, rfl⟩
  have gQ := GprsSame.of_post Q (by decide)
  have readyE := readyD.stack_log Q (by decide) (by simp only [keysG]; decide) (by decide)
    (gQ.get (by decide) (by decide) (by decide) readyD.stack)
    (gQ.get (by decide) (by decide) (by decide) readyD.raReg) readyD.aligned small (by simp only [LogInW])
  have memory : e.σ.mem = c.σ.mem := Q.memory.trans P.memory
  obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.mp (readyE.gpr_some 8 (by decide) (by decide))
  obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (readyE.gpr_some 9 (by decide) (by decide))
  obtain ⟨after, run3, ⟨F⟩⟩ := (Gc.SkiplistFirst.first_insert_startup e H capacity charge sp ra s0 s1 readyE frame
    (by rw [memory]; exact empty)
    ⟨readyE.stack, readyE.raReg, gholds_lookup (n := 10) _ Q.regs rfl,
      gholds_lookup (n := 11) _ Q.regs rfl, gholds_lookup (n := 12) _ Q.regs rfl, hs0, hs1, trivial⟩
    owned charged).run e ⟨Q.pc, rfl⟩
  have same := ((gP.trans gQ).trans (GprsSame.of_saved F.saved)).mono (vs := abiClobbered) (by decide)
  exact ⟨after, run1.trans (run2.trans run3), ⟨{
    atInsert := e
    memory := memory
    s0 := s0
    s1 := s1
    inserted := F
    pc := F.native.terminal.pc
    ready := F.ready
    saved := fun k hk => same.same k
      (by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk; omega)
      (by simp only [abiSaved, List.mem_cons, List.not_mem_nil, or_false] at hk; omega)
      (by simp only [abiSaved, abiClobbered, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)
    live := (LiveFrame.of_memory memory).trans F.live
    keyKept := by rw [F.keyKept, memory]
    htif := F.ready.platform.htifIdle.trans ready.platform.htifIdle.symm
    output := by
      rw [F.output]
      unfold Vsa.Machine.output
      rw [Q.output, P.output] }⟩⟩

/-- The same insertion also frames any explicitly selected caller blocks. -/
theorem BacktraceDone.selected_live {H capacity sp ra before after kept}
    (B : BacktraceDone H capacity sp ra before after)
    (selection : Gc.SkiplistFirst.Selected H kept) (frame : NativeFrame sp Gc.Skiplist.opStack) :
    LiveFrame kept before after :=
  (LiveFrame.of_memory B.memory).trans (B.inserted.native.live selection frame)

end OCaml.Vm.Boot.Startup
