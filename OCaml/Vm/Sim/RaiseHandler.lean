import OCaml.Vm.Sim.RaiseState
import OCaml.Vm.Sim.RaiseHandlerSegment
import OCaml.Vm.Sim.RaiseHandlerPins
import OCaml.Vm.Sim.LoopSetup

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Native handler reads are ordinary RAM windows at the four represented words. -/
structure RaiseFrameReads (base : Nat) : Prop where
  code : RamReadAt base 8
  link : RamReadAt (base + 8) 8
  environment : RamReadAt (base + 16) 8
  extraArgs : RamReadAt (base + 24) 8

/-- Execute the full caught handler and initialize dispatch, restoring Running. -/
theorem raise_handler {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high dest : Nat} {link extra : BitVec 63} {env : Val} {rest : List Val}
    (h : RaiseHandlerInput L P s pl cp sp high dest link env extra rest c)
    (nonnegative : 0 ≤ extra.toInt)
    (stable : WindowStable L.runtimeOk [⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (reads : RaiseFrameReads (high - 8 * s.trap))
    (space : TrapWriteOk P s c pl cp sp high (s.trap - link.toNat)) :
    ∃ count after, StepsN count c after ∧ Running L P
      {s with pc := dest, env := env, extra := extra.toNat, stack := rest, trap := s.trap - link.toNat} after := by
  let base := high - 8 * s.trap
  let log := trapLog (word c Layout.sym_Caml_state).toNat high (s.trap - link.toNat)
  obtain ⟨mem, memEq⟩ : ∃ mem : Std.ExtHashMap Nat (BitVec 8), mem = writeLog c.σ.mem log := ⟨_, rfl⟩
  have values := h.frame.values h.data
  have saved := h.frame.stack_repr h.data
  have length : (.code dest :: .int link :: env :: .int extra :: rest).length = s.trap := by
    have length := congrArg List.length h.frame.stack
    simp only [List.length_drop] at length
    have bound := h.frame.bound
    omega
  have linkBound : link.toNat ≤ (.code dest :: .int link :: env :: .int extra :: rest).length := by
    rw [length]; exact h.frame.linkBound
  have restored := poptrap_link saved space.highNat linkBound
  rw [length] at restored
  have address (i : Nat) : sp + 8 * (s.stack.length - s.trap + i) = base + 8 * i := by
    have shape := h.data.stack.1
    have bound := h.frame.bound
    dsimp only [base]
    omega
  have untouched (i : Nat) (v : Val)
      (slot : (.code dest :: .int link :: env :: .int extra :: rest)[i]? = some v) :
      OutLRange log (base + 8 * i) 8 := by
    have selected : s.stack[s.stack.length - s.trap + i]? = some v := by
      rw [← List.getElem?_drop, h.frame.stack]; exact slot
    have outside := space.payload.stack _ _ selected
    simpa only [address] using outside
  have readFrame (i : Nat) (v : Val)
      (slot : (.code dest :: .int link :: env :: .int extra :: rest)[i]? = some v) :
      bytesT8 mem (base + 8 * i) = bytesT8 c.σ.mem (base + 8 * i) := by
    rw [memEq]
    simpa only [bytesT_eight_eq] using bytesT_writeLog_out c.σ.mem (untouched i v slot)
  have readLink : sign_extend (m := 64) (bytesT8 c.σ.mem (base + 8)) = tag64 link := by
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using values.link
  have readCode : sign_extend (m := 64) (bytesT8 c.σ.mem base) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using values.code
  have readEnv : sign_extend (m := 64) (bytesT8 mem (base + 16)) = word c (base + 16) := by
    rw [readFrame 2 env rfl]
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have readExtra : sign_extend (m := 64) (bytesT8 mem (base + 24)) = tag64 extra := by
    rw [readFrame 3 (.int extra) rfl]
    simpa only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] using values.extraArgs
  have storeAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x0a8#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl
  have storeNat : (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp := Nat.mod_eq_of_lt space.address
  have window : WriteWindow (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)) 8 := by
    rw [← storeAddress]
    exact space.window
  have store := writeWindow_nat window storeNat
  have code : (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8 ≤ 0x80001ef0 ∨
      0x80001f1c ≤ (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp :=
    image_entry_code (w := BitVec.ofNat 64 (high - 8 * (s.trap - link.toNat)))
      space.image (by simp [trapLog]) (by decide) (by decide)
  have bp : SegSt (0x80001ef0#64) [⟨Register.x14, BitVec.ofNat 64 base⟩, ⟨Register.x15, word c Layout.sym_Caml_state⟩]
      (fun σ => Vsa.Sim.Code.CamlRaiseHandlerLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.platform.control, h.pc, ⟨h.trapReg, h.domainReg, trivial⟩, h.platform.control.minstret,
      h.tick, raise_handler_loaded h.platform.image, rfl, rfl⟩
  have native := tr_raise_handler (BitVec.ofNat 64 base) (word c Layout.sym_Caml_state) c.σ.mem c.σ
  simp only [base, show sign_extend (m := 64) (0x000#12) = 0#64 from rfl,
    show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 8 from rfl,
    show sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 16 from rfl,
    show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 24 from rfl,
    show sign_extend (m := 64) (0x020#12) = BitVec.ofNat 64 32 from rfl,
    BitVec.add_zero, ← BitVec.ofNat_add, storeAddress, storeNat,
    reads.code.toNat, reads.link.toNat, reads.environment.toNat, reads.extraArgs.toNat] at native
  obtain ⟨count, middle, _, run, post⟩ := native reads.link.lower reads.link.upper reads.link.htif (tag64 link) readLink.symm
    reads.code.lower reads.code.upper reads.code.htif (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) readCode.symm
    store.lower store.upper store.htif store.aligned code mem
    (by rw [restored]; exact memEq)
    reads.extraArgs.lower reads.extraArgs.upper reads.extraArgs.htif (tag64 extra) readExtra.symm
    reads.environment.lower reads.environment.upper reads.environment.htif (word c (base + 16)) readEnv.symm c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have image := image_of_writeLog h.platform.image space.image (memory.trans memEq)
  obtain ⟨loopCount, after, loopRun, loopPost⟩ := loop_setup ⟨post.good, image, post.tick, post.pcAt⟩
  have codeReg : gpr middle Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) := PinsHold.get post.pins ⟨4, by simp⟩
  have stackReg : gpr middle Layout.reg_sp = some (BitVec.ofNat 64 (base + 32)) := PinsHold.get post.pins ⟨3, by simp⟩
  have envReg : gpr middle Layout.reg_env = some (word c (base + 16)) := PinsHold.get post.pins ⟨1, by simp⟩
  have extraReg : gpr middle Layout.reg_extra = some (shift_bits_right_arith (tag64 extra) (Sail.BitVec.extractLsb (0x01#6) 5 0)) := PinsHold.get post.pins ⟨0, by simp⟩
  have extraValue : shift_bits_right_arith (tag64 extra) (Sail.BitVec.extractLsb (0x01#6) 5 0) = BitVec.ofNat 64 extra.toNat := by
    rw [longVal_native, longVal_nonnegative extra nonnegative]
  obtain ⟨accu, accuReg, accuWord⟩ := h.accu
  refine ⟨count + loopCount, after, run.append loopRun, ?_⟩
  apply raise_restore stable h.data h.bindings h.platform h.frame space
  case geometry => exact h.geometry
  case native => exact h.native
  refine ⟨loopPost.good, ?_, loopPost.loop,
    (loopPost.frame.frame (gprReg 2) (by decide)).trans (frame.frame (gprReg 2) (by decide)),
    loopPost.memory.trans (memory.trans memEq), loopPost.frame.out.trans frame.out⟩
  refine ⟨loopPost.head, (loopPost.frame.frame _ (by decide)).trans codeReg, ?_,
    ⟨accu, (loopPost.frame.frame _ (by decide)).trans ((frame.frame _ (by decide)).trans accuReg), accuWord⟩,
    ⟨word c (base + 16), (loopPost.frame.frame _ (by decide)).trans envReg, values.environment⟩, ?_⟩
  · have stackAddress : base + 32 = sp + 8 * (s.stack.length - s.trap + 4) := by
      simpa only [Nat.reduceMul] using (address 4).symm
    rw [← stackAddress]
    exact (loopPost.frame.frame _ (by decide)).trans stackReg
  · rw [extraValue] at extraReg
    exact (loopPost.frame.frame _ (by decide)).trans extraReg

end OCaml.Vm.Sim
