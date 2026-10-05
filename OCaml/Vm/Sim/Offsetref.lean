import OCaml.Vm.Sim.FieldRestore
import OCaml.Vm.Sim.OffsetArithmetic
import OCaml.Vm.Sim.OffsetrefSegment
import OCaml.Vm.Sim.OffsetrefPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- OFFSETREF replaces its selected integer field by the exact native modular
sum, restoring the represented heap and returning unit. -/
theorem offsetref_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k tag : Nat}
    {fields : List Val} {n : BitVec 63} {ofs : BitVec 32}
    (stable : WindowStable L.runtimeOk [⟨a + 8 * k, a + 8 * k + 8⟩])
    (h : ArmInput L P s .OFFSETREF c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) ofs)
    (pointer : s.accu = .ptr l k) (placed : pl.φ l = some a)
    (object : s.heap.get? l = some (.block tag fields))
    (selected : fields[k]? = some (.int n)) (room : 8 ≤ a)
    (space : FieldWriteOk P s c pl cp sp a k (tag64 n + offsetintOperand ofs)) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := s.pc + 2, accu := .unit, heap := s.heap.set l (.block tag (fields.set k (.int (untag (tag64 n + offsetintOperand ofs)))))} after := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have live : Live s.heap (roots P s) l := Live.root (show s.accu ∈ roots P s from by simp [roots]) (by rw [pointer]; rfl)
  have field : FieldSelection s.heap pl s.accu 0 (.int n) l a k :=
    ⟨pointer, placed, by simpa only [pointer, field?, object, Nat.add_zero] using selected⟩
  have source := represented_register h.accu field.sourceWord
  have fieldWord : word c (a + 8 * k) = tag64 n := by
    have value := (field.read h.toVmReprAt (by simp [roots])).word
    exact (Option.some.inj value).symm
  have addressNat : (BitVec.ofNat 64 (a + 8 * k)).toNat = a + 8 * k := Nat.mod_eq_of_lt space.address
  have store := writeWindow_nat space.window addressNat
  have code : a + 8 * k + 8 ≤ 0x80003224 ∨ 0x80003244 ≤ a + 8 * k :=
    image_entry_code (w := tag64 n + offsetintOperand ofs) space.image (by simp [fieldLog]) (by decide) (by decide)
  apply dispatch_compose h.dispatch
  intro d dp
  have read := operand.read32 h.code dp.memory
  have readField : sign_extend (m := 64) (bytesT8 d.σ.mem (a + 8 * k)) = tag64 n := by
    simpa only [dp.memory, word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend,
      BitVec.signExtend_eq] using fieldWord
  obtain ⟨memoryAfter, memoryEq⟩ : ∃ mem : Std.ExtHashMap Nat (BitVec 8),
      mem = writeLog d.σ.mem (fieldLog a k (tag64 n + offsetintOperand ofs)) := ⟨_, rfl⟩
  have bp : SegSt (0x80003224#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x21, BitVec.ofNat 64 (a + 8 * k)⟩]
      (fun σ => Vsa.Sim.Code.CamlOffsetrefLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
       (dp.frame.frame Register.x21 (by decide)).trans source, trivial⟩,
      dp.good.minstret, dp.tick, offsetref_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_offsetref (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
    (BitVec.ofNat 64 (a + 8 * k)) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, codePc_succ, operand.geometry.toNat, read, addressNat] at run
  have readHtif : a + 8 * k + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a + 8 * k :=
    Or.inr (by have htif := store.htif; omega)
  obtain ⟨nb, after, _, steps, post⟩ := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (sign_extend (m := 64) ofs) rfl store.lower store.upper readHtif (tag64 n) readField.symm
    store.lower store.upper store.htif store.aligned code memoryAfter memoryEq d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have observed : StackPost d pl (s.pc + 2) sp (tag64 0)
      (writeLog d.σ.mem (fieldLog a k (tag64 n + offsetintOperand ofs))) after := by
    refine ⟨post.good, post.pcAt, ?_,
      (frame.frame Register.x9 (by decide)).trans ((dp.frame.frame Register.x9 (by decide)).trans h.spReg),
      PinsHold.get post.pins ⟨0, by simp⟩, memory.trans memoryEq, frame.out,
      fun r hr => frame.frame r (by revert r; decide)⟩
    have pc : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + sign_extend (m := 64) (0x008#12)) :=
      PinsHold.get post.pins ⟨3, by simp⟩
    simpa only [show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 (4 * 2) from by decide,
      codePc_add] using pc
  refine ⟨nb, after, steps, ?_⟩
  apply field_restore stable h.toVmReprAt h.running.platform h.dispatch.loop space live placed object room bound
    (show valWord pl (.int (untag (tag64 n + offsetintOperand ofs))) = some (tag64 n + offsetintOperand ofs) from by
      simp only [valWord, tag_offsetint]) (fun _ loc => by cases loc)
  case geometry => exact h.geometry
  case native => exact h.native
  simpa only [dp.memory] using observed.after_dispatch dp

/-- The successful OFFSETREF bytecode rule matches the checked field update. -/
theorem offsetref_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k tag : Nat}
    {fields : List Val} {n : BitVec 63} {ofs : BitVec 32}
    (stable : WindowStable L.runtimeOk [⟨a + 8 * k, a + 8 * k + 8⟩])
    (h : ArmInput L P s .OFFSETREF c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) ofs)
    (pointer : s.accu = .ptr l k) (placed : pl.φ l = some a)
    (object : s.heap.get? l = some (.block tag fields))
    (selected : fields[k]? = some (.int n)) (room : 8 ≤ a)
    (space : FieldWriteOk P s c pl cp sp a k (tag64 n + offsetintOperand ofs))
    (step : stepI P s ⟨.OFFSETREF, [ofs.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have state : {s with pc := s.pc + 2, accu := .unit, heap := s.heap.set l (.block tag
      (fields.set k (.int (untag (tag64 n + offsetintOperand ofs)))))} = s' := by
    simpa only [stepI, pointer, field?, object, Nat.add_zero, selected, opt, setField?, bound,
      ite_true, St.adv, offsetintOperand_eq, BitVec.ofInt_toInt, Res.next.injEq] using step
  rw [← state]
  exact offsetref_arm stable h operand pointer placed object selected room space

end OCaml.Vm.Sim
