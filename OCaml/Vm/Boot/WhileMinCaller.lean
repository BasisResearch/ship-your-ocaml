import OCaml.Vm.Boot.WhileMin
import OCaml.Vm.Caller

/-! `caml_interprete`'s caller at the captured while_min cut: caml_main's
return site, native stack and saved frame, and the separation of entry's
writes from the initial VM representation. Register values come from the
captured register table; memory words from the kernel-checked store log. -/
namespace OCaml.Vm.Boot.WhileMin
open OCaml.Bytecode OCaml.Programs Vsa.Machine Vsa.Sim Vsa.Sim.Boot WhileMinLog OCaml.Vm.Primitives

/-- caml_main's native stack pointer at the cut. -/
def callerSp : Nat := 0x87ffff80

/-- The caller registers caml_interprete's prologue saves. -/
def callerRegs (r : Nat) : BitVec 64 := (gpr cut r).getD 0

/-- caml_main's saved words. -/
def mainSaved (r : Nat) : BitVec 64 := word cut (callerSp + Layout.camlMainSaveOffset r)

theorem caller_regs : ∀ r ∈ Layout.interpSavedRegs, gpr cut r = some (callerRegs r) := by
  intro r hr
  simp only [Layout.interpSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  unfold callerRegs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show gpr cut 1 = _ from WhileMinRegisters.get_x1]; rfl
  · rw [show gpr cut 8 = _ from WhileMinRegisters.get_x8]; rfl
  · rw [show gpr cut 9 = _ from WhileMinRegisters.get_x9]; rfl
  · rw [show gpr cut 18 = _ from WhileMinRegisters.get_x18]; rfl
  · rw [show gpr cut 19 = _ from WhileMinRegisters.get_x19]; rfl
  · rw [show gpr cut 20 = _ from WhileMinRegisters.get_x20]; rfl
  · rw [show gpr cut 21 = _ from WhileMinRegisters.get_x21]; rfl
  · rw [show gpr cut 22 = _ from WhileMinRegisters.get_x22]; rfl
  · rw [show gpr cut 23 = _ from WhileMinRegisters.get_x23]; rfl
  · rw [show gpr cut 24 = _ from WhileMinRegisters.get_x24]; rfl
  · rw [show gpr cut 25 = _ from WhileMinRegisters.get_x25]; rfl
  · rw [show gpr cut 26 = _ from WhileMinRegisters.get_x26]; rfl
  · rw [show gpr cut 27 = _ from WhileMinRegisters.get_x27]; rfl

theorem caller_ra : callerRegs 1 = 0x80004ff8#64 := by
  unfold callerRegs
  rw [show gpr cut 1 = _ from WhileMinRegisters.get_x1]
  rfl

theorem caller_stack : gpr cut 2 = some (BitVec.ofNat 64 callerSp) := WhileMinRegisters.get_x2

theorem main_return : mainSaved 1 = 0x80001df0#64 := by
  unfold mainSaved word
  rw [bytesT_memEqv memory_equiv, observedMem_bytes_stored logOk
    (a := callerSp + Layout.camlMainSaveOffset 1) (w := 8) (by decide +kernel)]
  decide +kernel

theorem domain_word : word cut Layout.sym_Caml_state = 0x8007d150#64 :=
  WhileMinRuntime.read_domain memory_equiv

/-- Every placed object of the initial heap lies in one band of the arena,
between the end of the `Caml_state` record and the native stack. -/
theorem objects_band : ∀ i, i < 29 →
    0x80281000 ≤ WhileMinHeap.addresses.getD i 0 ∧
      WhileMinHeap.addresses.getD i 0 + 8 * (whileMinHeap.getD i (.bytes [])).wosize ≤ 0x86000000 := by
  decide +kernel

theorem object_band {l a o} (ha : WhileMinHeap.place.φ l = some a) (ho : whileMin.init.heap.get? l = some o) :
    0x80281000 ≤ a ∧ a + 8 * o.wosize ≤ 0x86000000 := by
  change WhileMinHeap.addresses[l]? = some a at ha
  change whileMinHeap[l]? = some o at ho
  have hl : l < 29 := by
    have := (List.getElem?_eq_some_iff.mp ha).1
    have length : WhileMinHeap.addresses.length = 29 := by decide
    omega
  have band := objects_band l hl
  rw [List.getD_eq_getElem?_getD, ha, List.getD_eq_getElem?_getD, ho] at band
  exact band

theorem caller_outside :
    PayloadOutside (entryFootprint callerSp (word cut Layout.sym_Caml_state).toNat) whileMin whileMin.init cut
      WhileMinHeap.place (fun _ => none) WhileMinEntry.high := by
  rw [domain_word]
  have codeSize := code_size
  constructor
  · simp only [entryFootprint, OutLRange]; decide
  · rw [domain_word]; simp only [entryFootprint, OutLRange]; decide
  · rw [domain_word]; simp only [entryFootprint, OutLRange]; decide
  · simp only [entryFootprint, OutLRange]; decide
  · simp only [entryFootprint, OutLRange]; decide
  · simp only [entryFootprint, OutLRange]; decide
  · intro i w hw
    have bound : i < whileMin.code.size := by
      rcases Nat.lt_or_ge i whileMin.code.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hw; cases hw
    rw [codeSize] at bound
    simp only [entryFootprint, OutLRange, WhileMinHeap.place, callerSp, interpFrame, Layout.interpFrameBytes,
      Layout.sym_caml_callback_depth, Layout.off_external_raise, BitVec.toNat_ofNat]
    refine ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩
  · intro i v hv
    simp [Prog.init] at hv
  · intro l a o _ ha ho
    have band := object_band ha ho
    constructor
    · simp only [entryFootprint, OutLRange, callerSp, interpFrame, Layout.interpFrameBytes,
        Layout.sym_caml_callback_depth, Layout.off_external_raise, BitVec.toNat_ofNat]
      refine ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩
    · simp only [entryFootprint, OutLRange, callerSp, interpFrame, Layout.interpFrameBytes,
        Layout.sym_caml_callback_depth, Layout.off_external_raise, BitVec.toNat_ofNat]
      refine ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩
  · intro id ch a _ ha
    cases ha

/-- **caml_interprete's caller at the captured cut.** -/
theorem interpCaller :
    InterpCaller whileMin cut WhileMinHeap.place (fun _ => none) WhileMinEntry.high callerSp callerRegs
      mainSaved where
  regs := caller_regs
  ra := caller_ra
  stack := caller_stack
  frameLow := by decide
  frameHigh := by decide
  aligned := by decide
  mainFrame := fun _ _ => rfl
  mainReturn := main_return
  domainLow := by rw [domain_word]; decide
  domainHigh := by rw [domain_word]; decide
  domainAligned := by rw [domain_word]; decide
  primTable := by
    rw [domain_word]
    simp only [entryFootprint, OutLRange, callerSp, interpFrame, Layout.interpFrameBytes,
      Layout.sym_caml_callback_depth, Layout.off_external_raise, Layout.sym_caml_prim_table,
      Layout.off_prim_contents, BitVec.toNat_ofNat]
    decide
  primEntries := by
    intro i name hi
    have bound := (Array.getElem?_eq_some_iff.mp hi).1
    rw [WhileMinPrimitives.prims_size] at bound
    rw [domain_word, WhileMinPrimitives.read_table memory_equiv]
    simp only [entryFootprint, OutLRange, callerSp, interpFrame, Layout.interpFrameBytes,
      Layout.sym_caml_callback_depth, Layout.off_external_raise, BitVec.toNat_ofNat]
    refine ⟨Or.inl (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩
  tick := by decide
  htifIdle := WhileMinRegisters.get_htif_payload_writes
  outside := caller_outside

theorem interpCaller_densify {P : Prog} {c : Config} {pl : Place} {cp : ChanPlace} {high sp : Nat}
    {regs saved : Nat → BitVec 64} (h : InterpCaller P c pl cp high sp regs saved) :
    InterpCaller P (Vsa.Densify.fillZero c) pl cp high sp regs saved :=
  h.of_mem rfl (Vsa.Densify.memEqv_fillZeroMem c.σ.mem).symm rfl

/-- The same caller at the densified cut. -/
theorem interpCaller_fillZero :
    InterpCaller whileMin (Vsa.Densify.fillZero cut) WhileMinHeap.place (fun _ => none) WhileMinEntry.high
      callerSp callerRegs mainSaved :=
  interpCaller_densify interpCaller

/-- The initial heap objects lie, headers included, between the `Caml_state`
record and the VM stack window, word-aligned. -/
theorem objects_vm : ∀ i, i < 29 →
    0x80281008 ≤ WhileMinHeap.addresses.getD i 0 ∧
      WhileMinHeap.addresses.getD i 0 + 8 * (whileMinHeap.getD i (.bytes [])).wosize ≤ 0x803837b0 ∧
      WhileMinHeap.addresses.getD i 0 % 8 = 0 := by
  decide +kernel

theorem object_vm {l a o} (ha : WhileMinHeap.place.φ l = some a) (ho : whileMin.init.heap.get? l = some o) :
    0x80281008 ≤ a ∧ a + 8 * o.wosize ≤ 0x803837b0 ∧ a % 8 = 0 := by
  change WhileMinHeap.addresses[l]? = some a at ha
  change whileMinHeap[l]? = some o at ho
  have hl : l < 29 := by
    have := (List.getElem?_eq_some_iff.mp ha).1
    have length : WhileMinHeap.addresses.length = 29 := by decide
    omega
  have band := objects_vm l hl
  rw [List.getD_eq_getElem?_getD, ha, List.getD_eq_getElem?_getD, ho] at band
  exact band

theorem prim_table_word : word cut (Layout.sym_caml_prim_table + Layout.off_prim_contents) = 0x8038fb10#64 :=
  WhileMinPrimitives.read_table memory_equiv

/-- **Stack geometry at the captured cut** (the loop invariant's placement facts). -/
theorem stackGeometry_of {c : Config} (memory : Vsa.Densify.MemEqv c.σ.mem
      (observedMem WhileMinImage.initialMem WhileMinLog.log)) :
    OCaml.Vm.Sim.StackGeometry whileMin whileMin.init c WhileMinHeap.place (fun _ => none)
      WhileMinEntry.high := by
  have domain_word := WhileMinRuntime.read_domain memory
  have prim_table_word := WhileMinPrimitives.read_table memory
  have codeBound (i : Nat) (w : BitVec 32) (hw : whileMin.code[i]? = some w) : i < 191 := by
    rcases Nat.lt_or_ge i whileMin.code.size with h | h
    · have := code_size; omega
    · rw [Array.getElem?_eq_none h] at hw; cases hw
  have obj := @object_vm
  have words : OCaml.Vm.Sim.WordPlace WhileMinHeap.place := ⟨by decide, fun l a ha => by
      change WhileMinHeap.addresses[l]? = some a at ha
      have hl : l < 29 := by
        have := (List.getElem?_eq_some_iff.mp ha).1
        have length : WhileMinHeap.addresses.length = 29 := by decide
        omega
      have aligned := (objects_vm l hl).2.2
      rw [List.getD_eq_getElem?_getD, ha] at aligned
      simp only [Option.getD_some] at aligned
      exact aligned, by decide⟩
  refine
    { statics := by decide
      top := by decide
      aligned := by decide
      domain := by rw [domain_word]; simp only [OCaml.Vm.Sim.stackWindow, OutWRange]; decide
      code := fun i w hw => by
        have := codeBound i w hw
        simp only [OCaml.Vm.Sim.stackWindow, OutWRange, WhileMinHeap.place, WhileMinEntry.high, Layout.stackBytes]
        exact ⟨Or.inr (by omega), trivial⟩
      heap := fun l a o ha ho => by
        have band := obj ha ho
        simp only [OCaml.Vm.Sim.stackWindow, OutWRange, WhileMinEntry.high, Layout.stackBytes]
        exact ⟨Or.inl (by omega), trivial⟩
      channels := fun id ch a _ ha => by cases ha
      primitives := fun i name _ => by
        rw [prim_table_word]
        simp only [OCaml.Vm.Sim.stackWindow, OutWRange, WhileMinEntry.high, Layout.stackBytes, BitVec.toNat_ofNat]
        exact ⟨Or.inr (by omega), trivial⟩
      arena := by decide
      domainArena := by rw [domain_word]; decide
      domainLow := by rw [domain_word]; decide
      domainAligned := by rw [domain_word]; decide
      heapArena := fun l a o ha ho => by
        have band := obj ha ho
        have : (0x803837b0 : Nat) ≤ Vsa.Sim.DlHeap.heapEnd := by decide
        omega
      even := words.even
      words := words
      heapLow := fun l a o ha ho => by
        have band := obj ha ho
        have : Layout.sym_bss_end + 8 ≤ (0x80281008 : Nat) := by decide
        omega
      codeLow := by decide
      codeArena := by rw [code_size]; decide
      atomLow := by decide
      atomArena := by decide
      codeAtoms := by rw [code_size]; decide
      heapCode := fun l a o ha ho => by
        have band := obj ha ho
        rw [code_size]
        simp only [OutWRange, WhileMinHeap.place]
        exact ⟨Or.inl (by omega), trivial⟩
      heapAtoms := fun l a o ha ho => by
        have band := obj ha ho
        simp only [OutWRange, WhileMinHeap.place, OCaml.Vm.Sim.atomTableBytes]
        exact ⟨Or.inl (by omega), trivial⟩
      heapChannels := fun _ _ _ _ _ _ _ _ _ hb => by cases hb
      primsRam := fun i name hi => by
        have bound : i < whileMin.prims.size := (Array.getElem?_eq_some_iff.mp hi).1
        have size : whileMin.prims.size ≤ 512 := by decide +kernel
        have ht : Layout.sym_tohost + 8 ≤ 0x8038fb10 := by decide
        rw [prim_table_word]
        simp only [BitVec.toNat_ofNat]
        exact ⟨by omega, by omega, Or.inr (by omega)⟩
      channelArena := fun _ _ _ _ ha => by cases ha
      primsArena := fun i name hi => by
        have bound : i < whileMin.prims.size := (Array.getElem?_eq_some_iff.mp hi).1
        have size : whileMin.prims.size ≤ 512 := by decide +kernel
        have he : (0x8038fb10 : Nat) + 8 * 512 + 8 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
        rw [prim_table_word]
        simp only [BitVec.toNat_ofNat]
        omega
      heapPrims := fun l a o ha ho i name hi => by
        have band := obj ha ho
        rw [prim_table_word]
        simp only [OutWRange, BitVec.toNat_ofNat]
        exact ⟨Or.inl (by omega), trivial⟩
      domainCode := by rw [domain_word, code_size]; simp only [OutWRange, WhileMinHeap.place]; decide
      domainHeap := fun l a o ha ho => by
        have band := obj ha ho
        rw [domain_word]
        simp only [OutWRange, BitVec.toNat_ofNat, Layout.domainStateBytes]
        exact ⟨Or.inr (by omega), trivial⟩
      domainChannels := fun id ch a _ ha => by cases ha
      domainPrims := fun i name _ => by
        rw [domain_word, prim_table_word]
        simp only [OutWRange, BitVec.toNat_ofNat, Layout.domainStateBytes]
        exact ⟨Or.inr (by omega), trivial⟩ }

theorem stackGeometry :
    OCaml.Vm.Sim.StackGeometry whileMin whileMin.init cut WhileMinHeap.place (fun _ => none) WhileMinEntry.high :=
  stackGeometry_of memory_equiv

theorem stackGeometry_fillZero :
    OCaml.Vm.Sim.StackGeometry whileMin whileMin.init (Vsa.Densify.fillZero cut) WhileMinHeap.place
      (fun _ => none) WhileMinEntry.high :=
  stackGeometry_of (fun a => ((Vsa.Densify.memEqv_fillZeroMem cut.σ.mem) a).symm.trans (memory_equiv a))
end OCaml.Vm.Boot.WhileMin
