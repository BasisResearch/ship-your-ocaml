import OCaml.Vm.Primitives.Format.VsnprintfLong
import OCaml.Vm.Boot.WhileMinRegisterData
import Vsa.Sim.Boot.Image
import Vsa.Sim.GprCases

/-! A satisfiable native instance of the checked `caml_alloc_sprintf` layout.
This is an entry-state witness, not a startup reachability claim. It uses the
real caller's buffer, all seven spill slots, parsed-format address and return PC.
-/
namespace OCaml.Vm.Primitives.Format.VsnprintfCaller
open Vsa.Machine Vsa.MemRepr Vsa.Sim Vsa.Sim.Boot
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

abbrev sp : Nat := 0x87fff000
abbrev s : Nat := sp + 48
abbrev dst : Nat := sp + 16
abbrev ap : Nat := sp + 184
abbrev fmt : Nat := sp + 240

def dataAddresses : List Nat :=
  accAddrs 0x8005a398 368 ++ accAddrs 0x80053180 2 ++
  accAddrs 0x800648f8 8 ++ accAddrs fmt 4

def byte (a : Nat) : BitVec 8 :=
  if 0x8005a398 ≤ a ∧ a < 0x8005a508 then snpROImg a
  else if a = 0x80053180 then 0x2e#8
  else if 0x80064588 ≤ a ∧ a < 0x80064590 then natBytes 0x80064588 0x80045798 a
  else if 0x800645a0 ≤ a ∧ a < 0x800645a8 then natBytes 0x800645a0 0x80053180 a
  else if a = 0x80064600 then 1#8
  else if 0x800648f8 ≤ a ∧ a < 0x80064900 then natBytes 0x800648f8 0x80063b90 a
  else if a = fmt then 37#8
  else if a = fmt + 1 then 0x6c#8
  else if a = fmt + 2 then 0x64#8
  else if a = ap then 42#8
  else if inRangesB snpCodeRanges a then snpCodeImg a
  else 0#8

/-- Keep the finite memory construction behind its total-byte interface. -/
@[irreducible] def memory : Mem := loaderMem [(0x80000000, 0x65000), (sp - 1024, 1296)] byte

theorem memory_eq : memory = loaderMem [(0x80000000, 0x65000), (sp - 1024, 1296)] byte := by
  unfold memory
  rfl

abbrev live (a : Nat) : Prop := 0x80000000 ≤ a ∧ a < 0x80065000

theorem memory_get (a : Nat)
    (inside : live a ∨ sp - 1024 ≤ a ∧ a < sp + 272) : memory[a]? = some (byte a) := by
  have covered : inPieces [(0x80000000, 0x65000), (sp - 1024, 1296)] a = true := by
    simpa only [inPieces, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, decide_eq_true_eq, live, sp, Nat.reduceAdd, Nat.reduceSub] using inside
  have get := loaderMem_get [(0x80000000, 0x65000), (sp - 1024, 1296)] byte a
  rw [covered] at get
  exact (congrArg (fun m : Mem => m[a]?) memory_eq).trans get

theorem memory_byte (a : Nat)
    (inside : live a ∨ sp - 1024 ≤ a ∧ a < sp + 272) : imgM memory a = byte a := by
  unfold imgM
  rw [memory_get a inside]
  rfl

theorem memory_load (k : MKind) (a : Nat)
    (inside : ∀ i, i < widthOfM k → live (a + i) ∨ sp - 1024 ≤ a + i ∧ a + i < sp + 272) :
    ldv k memory a = ldvf k byte a := by
  have bytes : bytesAt (imgM memory) a (widthOfM k) = bytesAt byte a (widthOfM k) :=
    List.map_congr_left fun i hi => memory_byte _ (inside i (List.mem_range.mp hi))
  exact congrArg (bytesVal k) bytes

theorem data_bounds {a : Nat} (mem : a ∈ dataAddresses) :
    (0x8005a398 ≤ a ∧ a < 0x8005a508) ∨ (0x80053180 ≤ a ∧ a < 0x80053182) ∨
    (0x800648f8 ≤ a ∧ a < 0x80064900) ∨ (fmt ≤ a ∧ a < fmt + 4) := by
  simpa only [dataAddresses, List.mem_append, mem_accAddrs_iff,
    Nat.reduceAdd, fmt, or_assoc] using mem

theorem entry_geometry : VsnGeom s dst 128 :=
  ⟨(vsnprintf_layout (sp := sp) (by decide) (by decide) (by decide)).geom, .inr (by decide)⟩

def registers : Nat → BitVec 64 := fun r =>
  if r = 1 then 0x80013f10#64 else if r = 2 then BitVec.ofNat 64 sp
  else if r = 10 then BitVec.ofNat 64 dst else if r = 11 then 128#64
  else if r = 12 then BitVec.ofNat 64 fmt else if r = 13 then BitVec.ofNat 64 ap
  else (gprGet (Boot.WhileMinRegisters.state memory) r).getD 0

theorem entry : VsnLongEntry memory dataAddresses s dst 128 fmt ap 42#64 registers memory := by
  have data_mem : ∀ a ∈ dataAddresses, live a ∨ sp - 1024 ≤ a ∧ a < sp + 272 := by
    intro a ha
    have := data_bounds ha
    unfold live; dsimp [fmt, sp] at *; omega
  have tab_mem : InDA dataAddresses 0x8005a398 0x8005a508 := by
    intro a lower upper
    simp only [dataAddresses, List.mem_append, mem_accAddrs_iff]
    omega
  refine ⟨entry_geometry, rfl, rfl, rfl, rfl, rfl, by decide,
    ⟨?_, ?_, ?_, ?_, ⟨tab_mem, ?_⟩⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, by decide, by decide, by decide⟩,
    ?_, ?_, ?_, ?_, ?_,
    ((vsnprintf_layout (sp := sp) (by decide) (by decide) (by decide)).args.head (by decide)),
    .inr (by decide)⟩
  · intro a ha; have := data_bounds ha; dsimp [fmt, sp] at *; omega
  · intro a ha; have := data_bounds ha; dsimp [fmt, sp] at *; omega
  · intro a ha; have := data_bounds ha; dsimp [s, fmt, sp] at *; omega
  · intro a ha; have := data_bounds ha; dsimp [dst, fmt, sp] at *; omega
  · intro a lower upper
    rw [memory_byte a (.inl (by unfold live; omega))]
    simp only [byte, lower, upper, and_self, ite_true]
  · intro a lower upper
    simp only [dataAddresses, List.mem_append, mem_accAddrs_iff]; omega
  · rw [memory_byte _ (.inl (by decide))]; decide
  · rw [memory_byte _ (.inl (by decide))]; decide
  · intro a lower upper
    simp only [dataAddresses, List.mem_append, mem_accAddrs_iff]; omega
  · calc
      _ = ldvf .ld byte 0x800645a0 := by
        apply memory_load; intro i hi; exact .inl (by simp only [widthOfM] at hi; unfold live; omega)
      _ = _ := by decide +kernel
  · calc
      _ = ldvf .ld byte 0x80064588 := by
        apply memory_load; intro i hi; exact .inl (by simp only [widthOfM] at hi; unfold live; omega)
      _ = _ := by decide +kernel
  · calc
      _ = ldvf .lbu byte 0x80064600 := by
        apply memory_load; intro i hi; exact .inl (by simp only [widthOfM] at hi; unfold live; omega)
      _ = _ := by decide +kernel
  · intro a lower upper
    simp only [dataAddresses, List.mem_append, mem_accAddrs_iff]; omega
  · rw [memory_byte _ (.inr (by decide))]; decide
  · rw [memory_byte _ (.inr (by decide))]; decide
  · rw [memory_byte _ (.inr (by decide))]; decide
  · rw [memory_byte _ (.inr (by decide))]; decide
  · calc
      _ = ldvf .ld byte ap := by
        apply memory_load; intro i hi; exact .inr (by simp only [widthOfM] at hi; dsimp [sp, ap]; omega)
      _ = _ := by decide +kernel

open LeanRV64DExecutable in
def state : MState :=
  let base := Boot.WhileMinRegisters.state memory
  { base with regs := (((((((base.regs.insert .PC 0x8004018c#64).insert .x1 0x80013f10#64).insert .x2 (BitVec.ofNat 64 sp)).insert .x10 (BitVec.ofNat 64 dst)).insert .x11 128#64).insert .x12 (BitVec.ofNat 64 fmt)).insert .x13 (BitVec.ofNat 64 ap)) }

def before : Config := ⟨state, 0, 0⟩

theorem good_state : GoodState state := by
  have g0 := Boot.WhileMinRegisters.good_state memory
  have g1 := g0.insert_nonpinned (r := .PC) (by decide) 0x8004018c#64
  have g2 := g1.insert_nonpinned (r := .x1) (by decide) 0x80013f10#64
  have g3 := g2.insert_nonpinned (r := .x2) (by decide) (BitVec.ofNat 64 sp)
  have g4 := g3.insert_nonpinned (r := .x10) (by decide) (BitVec.ofNat 64 dst)
  have g5 := g4.insert_nonpinned (r := .x11) (by decide) 128#64
  have g6 := g5.insert_nonpinned (r := .x12) (by decide) (BitVec.ofNat 64 fmt)
  have g7 := g6.insert_nonpinned (r := .x13) (by decide) (BitVec.ofNat 64 ap)
  exact g7

structure CodeAt (p : Nat × BitVec 8) : Prop where
  inside : inRangesB snpCodeRanges p.1 = true
  lower : 0x80000000 ≤ p.1
  upper : p.1 < 0x80053000
  value : p.2 = snpCodeImg p.1

theorem code_bounds {p : Nat × BitVec 8} (mem : p ∈ snpText) : CodeAt p := by
  obtain ⟨piece, hp, inside, value⟩ := mem_piecesText_iff.mp mem
  simp only [snpPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst piece
  have bounds := inRangesB_within (rs := snpCodeRanges) (lo := 0x80000000) (hi := 0x80053000) (by decide) inside
  exact ⟨inside, bounds.1, bounds.2, value⟩

theorem code_live : ∀ p ∈ snpText, live p.1 := by
  intro p hp
  have h := code_bounds hp
  exact ⟨h.lower, by have high := h.upper; omega⟩

theorem code_byte {p : Nat × BitVec 8} (mem : p ∈ snpText) : imgM memory p.1 = p.2 := by
  have h := code_bounds mem
  rw [memory_byte _ (.inl (code_live p mem))]
  have low := h.lower
  have high := h.upper
  simp (disch := omega) only [byte, fmt, ap, sp, h.inside, if_pos, if_neg]
  exact h.value.symm

theorem separate : LocalSeparation roR (snpText ++ dataOf memory dataAddresses) nRegs (snpS s dst 128) := by
  constructor
  · intro p hp
    simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    decide
  · intro p hp
    rcases List.mem_append.mp hp with code | data
    · have h := code_bounds code
      have lower := h.lower
      have upper := h.upper
      simp only [snpS, VsaIris.Stdio.stdioFoot, VsaIris.Stdio.InRange, s, sp, dst, snpNeed, snpAbove]
      omega
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp data
      have h := data_bounds ha
      simp only [snpS, VsaIris.Stdio.stdioFoot, VsaIris.Stdio.InRange, s, sp, dst, fmt, snpNeed, snpAbove] at *
      omega

theorem good : VsaOk live before := by
  refine ⟨good_state, by decide, ?_, ?_, ?_⟩
  · intro n lo hi
    gpr_cases n =>
      simp only [before, state, Boot.WhileMinRegisters.state, gprGet]
      simp [Std.ExtDHashMap.get?_insert,
        Boot.WhileMinRegisters.get_x1, Boot.WhileMinRegisters.get_x2, Boot.WhileMinRegisters.get_x3,
        Boot.WhileMinRegisters.get_x4, Boot.WhileMinRegisters.get_x5, Boot.WhileMinRegisters.get_x6,
        Boot.WhileMinRegisters.get_x7, Boot.WhileMinRegisters.get_x8, Boot.WhileMinRegisters.get_x9,
        Boot.WhileMinRegisters.get_x10, Boot.WhileMinRegisters.get_x11, Boot.WhileMinRegisters.get_x12,
        Boot.WhileMinRegisters.get_x13, Boot.WhileMinRegisters.get_x14, Boot.WhileMinRegisters.get_x15,
        Boot.WhileMinRegisters.get_x16, Boot.WhileMinRegisters.get_x17, Boot.WhileMinRegisters.get_x18,
        Boot.WhileMinRegisters.get_x19, Boot.WhileMinRegisters.get_x20, Boot.WhileMinRegisters.get_x21,
        Boot.WhileMinRegisters.get_x22, Boot.WhileMinRegisters.get_x23, Boot.WhileMinRegisters.get_x24,
        Boot.WhileMinRegisters.get_x25, Boot.WhileMinRegisters.get_x26, Boot.WhileMinRegisters.get_x27,
        Boot.WhileMinRegisters.get_x28, Boot.WhileMinRegisters.get_x29, Boot.WhileMinRegisters.get_x30,
        Boot.WhileMinRegisters.get_x31]
  · intro a ha
    change (memory[a]?).isSome = true
    rw [memory_get a (.inl ha)]
    rfl
  · change state.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = _
    simp [state, Boot.WhileMinRegisters.state, Std.ExtDHashMap.get?_insert,
      Boot.WhileMinRegisters.get_htif_payload_writes, Boot.WhileMinRegisters.value_htif_payload_writes]

theorem observations : ∀ r ∈ nRegs, r ≠ PC → (vsaModel live).reg before r = registers r := by
  intro r hr ne
  simp only [nRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (ne rfl)
    | simp [vsaModel, vsaReg, before, state, registers, Boot.WhileMinRegisters.state, gprGet,
        Std.ExtDHashMap.get?_insert, PC]

theorem input : SymbolicInput live (snpText ++ dataOf memory dataAddresses)
    nRegs (snpS s dst 128) registers memory before := by
  refine ⟨good, ⟨?_, ?_⟩, observations, ?_⟩
  · intro p hp
    simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    simp [vsaModel, vsaReg, before, state, Boot.WhileMinRegisters.state, gprGet,
      Std.ExtDHashMap.get?_insert, Boot.WhileMinRegisters.get_x3,
      Boot.WhileMinRegisters.value_x3, Vsa.Sim.LibraryLayout.gpV, gp, PC]
  · intro p hp
    change (before.σ.mem[p.1]?).getD 0 = p.2
    rw [show before.σ.mem = memory from rfl]
    change imgM memory p.1 = p.2
    rcases List.mem_append.mp hp with code | data
    · exact code_byte code
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp data
      rfl

  · intro a _
    change (before.σ.mem[a]?).getD 0 = imgM memory a
    rw [show before.σ.mem = memory from rfl]
    rfl

/-- A real native entry with the checked 128-byte buffer has an actual
entry-to-return run and returns the two decimal bytes for its spilled 42.
No execution is supplied as a hypothesis. -/
theorem returns : ∃ after, Steps before after ∧
    LocalPost live roR (snpText ++ dataOf memory dataAddresses) nRegs (snpS s dst 128)
      (VsnResult s dst 128 registers memory (strBytes "42")) before after := by
  have summary := vsnprintf_long_summary before code_live entry separate input
  apply summary.run before
  refine ⟨?_, rfl⟩
  change state.regs.get? LeanRV64DExecutable.Register.PC = _
  simp [state, Boot.WhileMinRegisters.state, Std.ExtDHashMap.get?_insert]

/-- Machine observations at the real caller continuation for the concrete
signed-long input 42, including both digits, NUL and restored caller stack. -/
structure Returned (after : Config) : Prop where
  pc : OCaml.Vm.pcOf after = some 0x80013f10#64
  length : OCaml.Vm.gpr after 10 = some 2#64
  stack : OCaml.Vm.gpr after 2 = some (BitVec.ofNat 64 sp)
  first : (vsaModel live).mem after dst = 0x34#8
  second : (vsaModel live).mem after (dst + 1) = 0x32#8
  nul : (vsaModel live).mem after (dst + 2) = 0#8
  good : VsaOk live after

theorem returned : ∃ after, Steps before after ∧ Returned after := by
  obtain ⟨after, run, post⟩ := returns
  refine ⟨after, run, ?_⟩
  refine ⟨library_pc post.good post.result.pc,
    library_gpr post.good (by decide) (by decide) post.result.length,
    library_gpr post.good (by decide) (by decide) post.result.sp, ?_, ?_, post.result.nul, post.good⟩
  · exact post.result.bytes 0 (by decide)
  · exact post.result.bytes 1 (by decide)

end OCaml.Vm.Primitives.Format.VsnprintfCaller
