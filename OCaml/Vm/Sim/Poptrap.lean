import OCaml.Vm.Sim.TrapArithmetic
import OCaml.Vm.Sim.CheckSignals
import OCaml.Vm.Sim.PoptrapSegment
import OCaml.Vm.Sim.PoptrapPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- POPTRAP's no-pending path restores the prior trap pointer and removes
four represented stack words. The runtime supplies the no-pending invariant. -/
theorem poptrap_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {link : BitVec 63}
    (stable : WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (h : ArmInput L P s .POPTRAP c pl cp sp high) (quiet : SignalCheckReady c)
    (selected : s.stack[1]? = some (.int link)) (count : 4 ≤ s.stack.length)
    (bound : link.toNat ≤ s.stack.length)
    (readWindow : ReadWindow (BitVec.ofNat 64 (sp + 8)) 8)
    (space : TrapWriteOk P s c pl cp sp high (s.stack.length - link.toNat)) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := s.pc + 1, stack := s.stack.drop 4, trap := s.stack.length - link.toNat} after := by
  have slotWord : word c (sp + 8) = tag64 link := (Option.some.inj (h.stack.2 1 (.int link) selected)).symm
  have slotNat : (BitVec.ofNat 64 (sp + 8)).toNat = sp + 8 := stack_slot_nat h.toVmReprAt selected
  have slotAddress : BitVec.ofNat 64 sp + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (sp + 8) := by rw [BitVec.ofNat_add]; rfl
  have domainAddress : ((0x800030b8#64) + sign_extend (m := 64) ((0x00062#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0xc50#12) = BitVec.ofNat 64 Layout.sym_Caml_state := by decide
  have pendingAddress : ((0x800030a8#64) + sign_extend (m := 64) ((0x00062#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0xa88#12) = BitVec.ofNat 64 Layout.sym_caml_something_to_do := by decide
  have storeAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x0a8#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]
    rfl
  have storeNat : (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp := Nat.mod_eq_of_lt space.address
  have window : WriteWindow (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)) 8 := by
    rw [← storeAddress]
    exact space.window
  have store := writeWindow_nat window storeNat
  have restored := poptrap_link h.stack space.highNat bound
  have code : (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8 ≤ 0x800030a8 ∨
      0x800030dc ≤ (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp :=
    image_entry_code (w := BitVec.ofNat 64 (high - 8 * (s.stack.length - link.toNat)))
      space.image (by simp [trapLog]) (by decide) (by decide)
  obtain ⟨accu, accuReg, accuWord⟩ := h.accu
  apply dispatch_compose h.dispatch
  intro d dp
  have pending : sign_extend (m := 64) (bytesT4 d.σ.mem Layout.sym_caml_something_to_do) = 0#64 := quiet.read dp.memory
  have slotRead : sign_extend (m := 64) (bytesT8 d.σ.mem (sp + 8)) = tag64 link := by
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend,
      BitVec.signExtend_eq] using slotWord
  have domainRead : sign_extend (m := 64) (bytesT8 d.σ.mem Layout.sym_Caml_state) = word c Layout.sym_Caml_state := by
    simp only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  obtain ⟨memoryAfter, memoryEq⟩ : ∃ mem : Std.ExtHashMap Nat (BitVec 8),
      mem = writeLog d.σ.mem (trapLog (word c Layout.sym_Caml_state).toNat high (s.stack.length - link.toNat)) := ⟨_, rfl⟩
  have bp : SegSt (0x800030a8#64)
      [⟨Register.x9, BitVec.ofNat 64 sp⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩]
      (fun σ => Vsa.Sim.Code.CamlPoptrapLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x9 (by decide)).trans h.spReg, dp.nextCode, trivial⟩,
      dp.good.minstret, dp.tick, poptrap_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_poptrap (BitVec.ofNat 64 sp)
    (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) d.σ.mem d.σ
  simp only [pendingAddress, domainAddress, slotAddress,
    show (BitVec.ofNat 64 Layout.sym_caml_something_to_do).toNat = Layout.sym_caml_something_to_do from by decide,
    show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = Layout.sym_Caml_state from by decide] at run
  obtain ⟨nb, after, _, steps, post⟩ := run (by decide) (by decide) (by decide) 0#64 pending.symm (by decide)
    readWindow.lower readWindow.upper readWindow.htif (tag64 link) (by simpa only [slotNat] using slotRead.symm)
    (by decide) (by decide) (by decide) (word c Layout.sym_Caml_state) domainRead.symm
    (by simpa only [storeAddress, storeNat] using store.lower)
    (by simpa only [storeAddress, storeNat] using store.upper)
    (by simpa only [storeAddress, storeNat] using store.htif)
    (by simpa only [storeAddress, storeNat] using store.aligned)
    (by simpa only [storeAddress, storeNat] using code) memoryAfter
    (by rw [storeAddress, storeNat, restored]; exact memoryEq) d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have observed : StackPost d pl (s.pc + 1) (sp + 8 * 4) accu
      (writeLog d.σ.mem (trapLog (word c Layout.sym_Caml_state).toNat high (s.stack.length - link.toNat))) after := by
    refine ⟨post.good, post.pcAt, ?_, ?_,
      (frame.frame Register.x21 (by decide)).trans ((dp.frame.frame Register.x21 (by decide)).trans accuReg),
      memory.trans memoryEq, frame.out, fun r hr => frame.frame r (by revert r; decide)⟩
    · have pc : gpr after Layout.reg_pc = some ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) +
          sign_extend (m := 64) (0x000#12)) := PinsHold.get post.pins ⟨2, by simp⟩
      simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide, BitVec.add_zero, codePc_succ] using pc
    · have stack : gpr after Layout.reg_sp = some (BitVec.ofNat 64 sp + sign_extend (m := 64) (0x020#12)) :=
        PinsHold.get post.pins ⟨0, by simp⟩
      simpa only [show sign_extend (m := 64) (0x020#12) = BitVec.ofNat 64 (8 * 4) from by decide,
        BitVec.ofNat_add] using stack
  refine ⟨nb, after, steps, ?_⟩
  apply trap_restore stable h.toVmReprAt h.running.platform h.dispatch.loop space count accuWord
  simpa only [dp.memory] using observed.after_dispatch dp

/-- A successful POPTRAP transition supplies the link bound used by the native
pointer reconstruction; the four-word shape supplies stack consumption. -/
theorem poptrap_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {link : BitVec 63}
    {handler env extra : Val} {rest : List Val}
    (stable : WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (h : ArmInput L P s .POPTRAP c pl cp sp high) (quiet : SignalCheckReady c)
    (stack : s.stack = handler :: .int link :: env :: extra :: rest)
    (readWindow : ReadWindow (BitVec.ofNat 64 (sp + 8)) 8)
    (space : TrapWriteOk P s c pl cp sp high (s.stack.length - link.toNat))
    (step : stepI P s ⟨.POPTRAP, []⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  by_cases bound : link.toNat ≤ s.stack.length
  · have notGreater : ¬ s.stack.length < link.toNat := by omega
    have state : {s with pc := s.pc + 1, stack := s.stack.drop 4, trap := s.stack.length - link.toNat} = s' := by
      have reduced := step
      simp only [stepI, stack] at reduced
      rw [← stack] at reduced
      simp only [notGreater, ite_false, St.adv, Res.next.injEq] at reduced
      simpa only [stack, List.drop_succ_cons, List.drop_zero] using reduced
    rw [← state]
    exact poptrap_arm stable h quiet (by simp [stack]) (by simp [stack]) bound readWindow space
  · have greater : s.stack.length < link.toNat := by omega
    simp only [stepI, stack] at step
    rw [← stack] at step
    simp only [greater, ite_true] at step
    cases step

end OCaml.Vm.Sim
