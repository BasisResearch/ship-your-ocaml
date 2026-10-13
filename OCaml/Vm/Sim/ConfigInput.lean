import OCaml.Vm.Sim.StringAllocReturn
import OCaml.Vm.Primitives.CamlSysGetConfig
import OCaml.Vm.Primitives.Memmove
import OCaml.Vm.Boot.Startup.LibraryText

/-!
# `caml_sys_get_config`'s stage inputs at the callee entry

The generated stage contracts (`ConfigTupleCopied`, `…Allocated`,
`…Finished`) take their memory accesses and layout as inputs. This file
supplies them at the C_CALL callee entry from `StringAllocEntry`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.ConfigTuple
  LeanRV64DExecutable
open ArgvTuple (frameSp memoryView lpins8_of_view memoryView_gpr)
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Memcpy

/-- The prepare block's two loads: the domain pointer and the old
`local_roots`, both after the four register saves. -/
def prepareLoads (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64) : List (List (BitVec 8)) :=
  [read8 (writeLog m (savedLog R)) DoubleAllocation.domainGlobal.toNat,
   read8 (writeLog m (savedLog R))
     (bytesVal .ld (read8 (writeLog m (savedLog R)) DoubleAllocation.domainGlobal.toNat) + 288#64).toNat]

/-- The prepare block's slots and words, as windows. -/
structure PrepareLayout (R : Nat → BitVec 64) (domain : BitVec 64) : Prop where
  saves : ∀ k ∈ [80, 88, 96, 104], WriteWindow (frameSp (R 2) + BitVec.ofNat 64 k) 8
  slots : ∀ k ∈ [0, 8, 16, 24, 32, 40, 48], WriteWindow (frameSp (R 2) + BitVec.ofNat 64 k) 8
  domainRead : ReadWindow DoubleAllocation.domainGlobal 8
  rootsWrite : WriteWindow (domain + 288#64) 8

theorem prepare_access (m : Std.ExtHashMap Nat (BitVec 8)) (R : Nat → BitVec 64)
    (hl : PrepareLayout R (bytesVal .ld ((prepareLoads m R).getD 0 []))) :
    AccessPlan m (prepare_input R) (prepareLoads m R) prepare_body := by
  have s80 := hl.saves 80 (by simp)
  have s88 := hl.saves 88 (by simp)
  have s96 := hl.saves 96 (by simp)
  have s104 := hl.saves 104 (by simp)
  have t0 := hl.slots 0 (by simp)
  have t8 := hl.slots 8 (by simp)
  have t16 := hl.slots 16 (by simp)
  have t24 := hl.slots 24 (by simp)
  have t32 := hl.slots 32 (by simp)
  have t40 := hl.slots 40 (by simp)
  have t48 := hl.slots 48 (by simp)
  have rw' := hl.rootsWrite
  simp only [prepareLoads, List.getD_cons_zero] at rw'
  simp only [AccessPlan, prepare_body]
  refine ⟨True.intro, ?_, ?_, ?_, ?_, True.intro, True.intro, ?_, True.intro, True.intro, ?_, True.intro, ?_,
    True.intro, True.intro, True.intro, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · apply s104.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply s96.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply s80.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply s88.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply hl.domainRead.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
    · apply lpins8_of_view (m' := writeLog m (savedLog R))
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, savedLog, writeLog, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
      · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply rw'.read.ld rfl
    · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
    · apply lpins8_of_view (m' := writeLog m (savedLog R))
      · simp [stepMemM, wentryM, widthOfM, eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, savedLog, writeLog, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
      · simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply rw'.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t24.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t48.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t16.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t0.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t8.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t32.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]
  · apply t40.sd rfl
    simp [eaddrM, stepGM, stepLdsM, wvalM, prepare_input, srcVal, lookupG, eraseG, imm20Of, prepareLoads, frameSp, DoubleAllocation.domainGlobal, Layout.sym_Caml_state, Functions.sign_extend, Sail.BitVec.signExtend, -BitVec.toNat_add]

/-- `gp` holds `gpV`: the library's read-only register. -/
theorem roR_of_gp {live : Nat → Prop} {c : Config} (gp : gpr c 3 = some gpV) :
    ROHolds (vsaModel live) c roR [] := by
  refine ⟨fun q hq => ?_, fun _ hq => nomatch hq⟩
  obtain rfl := List.mem_singleton.1 hq
  change vsaReg c 3 = _
  simp only [vsaReg]
  change (gpr c 3).getD 0 = _
  rw [gp]; rfl

/-- `OCAML_OS_TYPE`'s bytes and terminator in `.rodata`. -/
def osTypeZ : List (BitVec 8) := [0x55#8, 0x6e#8, 0x69#8, 0x78#8, 0#8]

theorem osType_rodata {c : Config} (image : ExecutableImage c) :
    ∀ i, i < 5 → (c.σ.mem[osTypeAddress.toNat + i]?).getD 0 = osTypeZ.getD i 0 := by
  intro i hi
  have base : osTypeAddress.toNat = Image.rodataBase + 11000 := by decide
  rw [base, Nat.add_assoc, image.rodata (11000 + i) (by simp only [Image.rodataSize]; omega)]
  simp only [Option.getD_some]
  rcases i with _ | _ | _ | _ | _ | i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · omega

theorem frameSp_eq {R : Nat → BitVec 64} {N : Nat} (h2 : R 2 = BitVec.ofNat 64 N) (hN : 112 ≤ N) (hN' : N < 2 ^ 64) :
    frameSp (R 2) = BitVec.ofNat 64 (N - 112) := by
  rw [h2]; exact frameSp_ofNat hN hN'

/-- A word slot `k` bytes below the native frame. -/
theorem frame_below_window {N k : Nat} (hN : Vsa.Sim.DlHeap.heapEnd + 4096 ≤ N) (hN' : N ≤ Layout.sym_stack_top)
    (al : N % 16 = 0) (hk : k ≤ 3000) (hk8 : k % 8 = 0) :
    WriteWindow (BitVec.ofNat 64 (N - 112) - BitVec.ofNat 64 k) 8 := by
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  rw [he] at hN
  simp only [Layout.sym_stack_top] at hN'
  rw [ofNat_sub_small (by omega) (by omega)]
  exact window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega) (by omega)

/-- A word slot `k` bytes above the native frame's base. -/
theorem frame_above_window {N k : Nat} (hN : Vsa.Sim.DlHeap.heapEnd + 4096 ≤ N) (hN' : N ≤ Layout.sym_stack_top)
    (al : N % 16 = 0) (hk : k + 8 ≤ 112) (hk8 : k % 8 = 0) :
    WriteWindow (BitVec.ofNat 64 (N - 112) + BitVec.ofNat 64 k) 8 := by
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  rw [he] at hN
  simp only [Layout.sym_stack_top] at hN'
  rw [ofNat_add_small]
  exact window_of_nat (by simp only [Layout.sym_tohost]; omega) (by omega) (by omega)

theorem vsa_mem_view {live : Nat → Prop} (c : Config) (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    (vsaModel live).mem (memoryView c mem) a = (mem[a]?).getD 0 := rfl

/-- The copy's source window, `"Unix\0"`. -/
abbrev osTypeData : List Nat := List.range' osTypeAddress.toNat 5

/-- **The copy's sizing inputs** on the memory after the prepare block. -/
theorem config_sized {c : Config} {N D Y : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (image : ExecutableImage c) (gp : gpr c 3 = some gpV)
    (hN : Vsa.Sim.DlHeap.heapEnd + 4096 ≤ N) (hN' : N ≤ Layout.sym_stack_top) (al : N % 16 = 0)
    (hD : D + 1000 < 2 ^ 32) (h2 : R 2 = BitVec.ofNat 64 N)
    (prepIn : LogInW (configWindows N D Y) (prepareLog R (BitVec.ofNat 64 D) roots))
    (dataLow : Layout.sym_bss_end ≤ D) (youngLow : Layout.sym_bss_end + 48 ≤ Y) :
    StringCopy.SizedMemory imageLive (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)) osTypeData
      prepare_call.link (frameSp (R 2)) osTypeAddress.toNat osType.length
      (imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))
      (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))) := by
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have hst : Layout.sym_stack_top = 0x88000000 := rfl
  rw [he] at hN; rw [hst] at hN'
  have F := frameSp_eq h2 (by omega) (by omega)
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  rw [bss] at dataLow youngLow
  -- addresses below `.bss` miss the prepare stores
  have low : ∀ x, x < 0x8007d138 → OutL (prepareLog R (BitVec.ofNat 64 D) roots) x := fun x hx =>
    outL_of_range (outLRange_of_windows (a := x) (n := 1) prepIn (by
      simp only [configWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega))
      (Nat.le_refl _) (by omega)
  have keep : ∀ x, x < 0x8007d138 →
      (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))[x]? = c.σ.mem[x]? :=
    fun x hx => writeLog_out _ _ _ (low x hx)
  have saveAddr : ∀ k ∈ [8, 24], (frameSp (R 2) - BitVec.ofNat 64 k).toNat = N - 112 - k := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [F, ofNat_sub_small (by omega) (by omega), toNat_ofNat_small (by omega)]
  have s8 := saveAddr 8 (by simp)
  have s24 := saveAddr 24 (by simp)
  refine { returnSlot := ?_, sourceSlot := ?_, saveImage := ?_, saveLibrary := ?_,
           libraryImage := imageLive_image, codeLive := snpText_image, readOnly := ?_, «string» := ?_ }
  · rw [F]; exact frame_below_window (by rw [he]; omega) (by rw [hst]; omega) al (by decide) (by decide)
  · rw [F]; exact frame_below_window (by rw [he]; omega) (by rw [hst]; omega) al (by decide) (by decide)
  · simp only [StringCopy.saveLog, StringCopy.entryRegisters]
    refine ⟨?_, ?_⟩ <;> simp only [OutLRange, s8, s24, Image.textBase, Image.textSize, Image.rodataBase,
      Image.rodataSize, and_true] <;> omega
  · intro p hp
    have below : p.1 < 0x80055c78 + 5 := by
      rcases List.mem_append.1 hp with h | h
      · have := snpText_below p h; omega
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
        obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hx
        rw [show osTypeAddress.toNat = 0x80055c78 from rfl]; omega
    simp only [StringCopy.saveLog, StringCopy.entryRegisters, OutL, s8, s24, and_true]
    omega
  · have gpv : gpr (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))) 3 = some gpV := by
      rw [memoryView_gpr]; exact gp
    refine ⟨(roR_of_gp (live := imageLive) gpv).1, fun p hp => ?_⟩
    rcases List.mem_append.1 hp with h | h
    · have below := snpText_below p h
      rw [vsa_mem_view, keep _ (by omega), OCaml.Vm.Boot.Startup.snp_text_loaded image p h]; rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
      rw [vsa_mem_view]; simp only [imgM]
  · have src : ∀ i, i < 5 → imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))
        (osTypeAddress.toNat + i) = osTypeZ.getD i 0 := fun i hi => by
      simp only [imgM]
      rw [keep _ (by rw [show osTypeAddress.toNat = 0x80055c78 from rfl]; omega)]
      exact osType_rodata image i hi
    have a0 : osTypeAddress.toNat = 0x80055c78 := rfl
    refine ⟨fun x lo hi => Or.inl ⟨List.mem_range'.2 ⟨x - osTypeAddress.toNat, by
        simp only [osType_length] at hi; omega, by omega⟩, rfl⟩, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [osType_length] at hi
      rw [src i (by omega)]
      rcases i with _ | _ | _ | _ | i <;> first | decide | omega
    · rw [osType_length, src 4 (by decide)]; decide
    · rw [a0]; decide
    · rw [a0, osType_length]; decide
    · rw [a0, osType_length]; decide

/-- A word apart from the native frame and from `local_roots` misses the
prepare stores. -/
theorem prepare_out {N D x : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (hN : 4096 ≤ N) (hN' : N < 2 ^ 32) (hD : D + 1000 < 2 ^ 32) (h2 : R 2 = BitVec.ofNat 64 N)
    (roots' : x + 8 ≤ D + 288 ∨ D + 296 ≤ x) (frame : x + 8 ≤ N - 112 ∨ N ≤ x) :
    OutLRange (prepareLog R (BitVec.ofNat 64 D) roots) x 8 := by
  simp only [prepareLog, savedLog, frameSp, h2, OutLRange, List.cons_append, List.nil_append,
    Layout.off_local_roots, frameSp_ofNat (N := N) (by omega) (by omega), ← BitVec.ofNat_add,
    BitVec.toNat_ofNat, Nat.reducePow, and_true]
  omega

theorem view_word {c : Config} {log : List WEntry} {x : Nat} (out : OutLRange log x 8) :
    word (memoryView c (writeLog c.σ.mem log)) x = word c x := by
  change bytesT (writeLog c.σ.mem log) x 8 = bytesT c.σ.mem x 8
  rw [bytesT_writeLog_out _ out]

/-- A store window of any width in RAM above `tohost`, from naturals. -/
theorem window_nat_width {n w : Nat} (lo : Layout.sym_tohost + 16 ≤ n) (hi : n + w ≤ 0x100000000)
    (al : n % w = 0) : WriteWindow (BitVec.ofNat 64 n) w := by
  have e : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_small (by omega)
  have t : 0x80000000 + 16 ≤ Layout.sym_tohost + 16 := by decide
  exact ⟨by rw [e]; omega, by rw [e]; exact hi, by rw [e]; exact lo, by rw [e]; exact al⟩

/-- The entry's numbers for the copy and the triple. -/
structure ConfigNumbers (N D Y Lm : Nat) : Prop where
  nativeLow : 0x86800000 + 4096 ≤ N
  nativeHigh : N ≤ 0x88000000
  nativeAligned : N % 16 = 0
  domainLow : 0x8007d138 ≤ D
  domainHigh : D + 928 ≤ 0x86800000
  domainAligned : D % 8 = 0
  youngHigh : Y ≤ 0x86800000
  youngAligned : Y % 8 = 0
  limitLow : 0x8007d138 ≤ Lm
  room : Lm + 48 ≤ Y
  apart : D + 928 ≤ Lm ∨ Y ≤ D

theorem ConfigNumbers.of_entry {c : Config} {N D Y Lm : Nat} (e : StringAllocEntry c N D Y Lm 48) :
    ConfigNumbers N D Y Lm :=
  ⟨e.nativeLow, e.nativeHigh, e.nativeAligned, e.domainLow, e.domainHigh, e.domainAligned, e.youngHigh,
    e.youngAligned, e.limitLow, e.room, e.domainApart⟩

theorem nurseryHeader4 (Y : Nat) (h : 16 ≤ Y) (h' : Y < 2 ^ 64) :
    StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) (BitVec.ofNat 64 4) = BitVec.ofNat 64 (Y - 16) := by
  simp only [StringAllocation.nurseryHeader, span4]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem youngSlot_eq (D : Nat) (h : D + 8 < 2 ^ 64) :
    DoubleAllocation.youngSlot (BitVec.ofNat 64 D) = BitVec.ofNat 64 (D + 8) := by
  simp only [DoubleAllocation.youngSlot, Layout.off_young_ptr, ← BitVec.ofNat_add]

theorem limitSlot_eq (D : Nat) : DoubleAllocation.limitSlot (BitVec.ofNat 64 D) = BitVec.ofNat 64 D := by
  simp only [DoubleAllocation.limitSlot, Layout.off_young_limit, ← BitVec.ofNat_add, Nat.add_zero]

/-- A log above `.bss` misses the executable image. -/
theorem imageOutside_of_above {log : List WEntry} (above : ∀ e ∈ log, Layout.sym_bss_end ≤ e.1) :
    ImageOutside log := by
  have t : Image.textBase + Image.textSize ≤ Layout.sym_bss_end := by decide
  have r : Image.rodataBase + Image.rodataSize ≤ Layout.sym_bss_end := by decide
  refine ⟨Gc.outLRange_of_forall fun e he => .inl ?_, Gc.outLRange_of_forall fun e he => .inl ?_⟩
  · have := above e he; omega
  · have := above e he; omega

/-- **The copy's allocation inputs** on the memory after the prepare block. -/
theorem config_allocate {c : Config} {N D Y Lm : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (nums : ConfigNumbers N D Y Lm) (h2 : R 2 = BitVec.ofNat 64 N)
    (wD : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (wY : word c (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y)
    (wL : word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm)
    (sized : StringCopy.SizedMemory imageLive (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))
      osTypeData prepare_call.link (frameSp (R 2)) osTypeAddress.toNat osType.length
      (imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))
      (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))) :
    StringCopy.AllocateMemory imageLive (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)) osTypeData
      prepare_call.link (frameSp (R 2)) osTypeAddress.toNat osType.length
      (imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))
      (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have F := frameSp_eq h2 (by omega) (by omega)
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have hY := nurseryHeader4 Y (by omega) (by omega)
  have ys := youngSlot_eq D (by omega)
  have ls := limitSlot_eq D
  have gd : DoubleAllocation.domainGlobal.toNat = Layout.sym_Caml_state := rfl
  have cs : Layout.sym_Caml_state = 0x80064d08 := rfl
  have out : ∀ x, (x + 8 ≤ D + 288 ∨ D + 296 ≤ x) → x + 8 ≤ N - 112 →
      OutLRange (prepareLog R (BitVec.ofNat 64 D) roots) x 8 := fun x r f =>
    prepare_out (by omega) (by omega) (by omega) h2 r (.inl f)
  have len4 : (BitVec.ofNat 64 osType.length : BitVec 64) = BitVec.ofNat 64 4 := by rw [osType_length]
  simp only [osType_length] at sized ⊢
  rw [F] at sized ⊢
  have sub : ∀ k, k ≤ 200 → BitVec.ofNat 64 (N - 112) - BitVec.ofNat 64 k = BitVec.ofNat 64 (N - 112 - k) :=
    fun k hk => ofNat_sub_small (by omega) (by omega)
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  refine { sized with
    lengthSlot := ?_, lengthImage := ?_, metadata := ?_, metadataOutside := ?_, geometry := ?_, separate := ?_ }
  · rw [sub 32 (by decide)]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  · simp only [StringCopy.sizeLog, StringCopy.lengthRegisters, StringCopy.entryRegisters, sub 32 (by decide),
      nat _ (show N - 112 - 32 < 2 ^ 64 by omega)]
    exact ⟨⟨.inl (by simp only [Image.textBase, Image.textSize]; omega), trivial⟩,
      ⟨.inl (by simp only [Image.rodataBase, Image.rodataSize]; omega), trivial⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [gd, view_word (out _ (by rw [cs]; omega) (by rw [cs]; omega)), wD]
    · rw [ys, nat _ (by omega), view_word (out _ (by omega) (by omega))]
      simpa only [Layout.off_young_ptr] using wY
    · rw [ls, nat _ (by omega), view_word (out _ (by omega) (by omega))]
      simpa only [Layout.off_young_limit, Nat.add_zero] using wL
  · simp only [StringCopy.prefixLog, StringCopy.saveLog, StringCopy.entryRegisters, StringCopy.sizeLog,
      StringCopy.lengthRegisters, sub 8 (by decide), sub 24 (by decide), sub 32 (by decide),
      nat _ (show N - 112 - 8 < 2 ^ 64 by omega), nat _ (show N - 112 - 24 < 2 ^ 64 by omega),
      nat _ (show N - 112 - 32 < 2 ^ 64 by omega), List.cons_append, List.nil_append]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [OutLRange, gd, ys, ls, nat _ (show D + 8 < 2 ^ 64 by omega),
      nat _ (show D < 2 ^ 64 by omega), cs, and_true] <;> omega
  · have s40 : BitVec.ofNat 64 (N - 112) - 32#64 - 8#64 = BitVec.ofNat 64 (N - 152) := by
      rw [sub 32 (by decide), ofNat_sub_small (by omega) (by omega), show N - 112 - 32 - 8 = N - 152 by omega]
    have last : BitVec.ofNat 64 (Y - 16) + 8#64 + StringAllocation.stringSpan 4#64 - 8#64 = BitVec.ofNat 64 (Y - 8) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, span4]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
    have pad : BitVec.ofNat 64 (Y - 16) + 8#64 + (StringAllocation.stringSpan 4#64 - 1#64) = BitVec.ofNat 64 (Y - 1) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, span4]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
    have hY' : StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) 4#64 = BitVec.ofNat 64 (Y - 16) := hY
    refine { stackWrite := ?_, youngWrite := ?_, limitRead := ?_, headerWrite := ?_, lastWrite := ?_,
             paddingWrite := ?_, small := by decide, room := ?_, stackImage := ?_, reserveImage := ?_,
             initializeImage := ?_ }
    · rw [s40]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [ys]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [ls]; exact (window_of_nat (by rw [tohost]; omega) (by omega) (by omega)).read
    · rw [hY']; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [hY', last]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [hY', pad]; exact window_nat_width (by rw [tohost]; omega) (by omega) (by omega)
    · rw [hY']
      simp only [guardB]
      exact Vsa.Sim.bltu_false_of_ge _ _ (by rw [nat _ (by omega), nat _ (by omega)]; omega)
    · apply imageOutside_of_above
      intro e he
      simp only [savedRaLog, s40, List.mem_singleton] at he
      subst he
      rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
    · apply imageOutside_of_above
      intro e he
      simp only [StringAllocation.reservationLog, ys, List.mem_singleton] at he
      subst he
      rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
    · apply imageOutside_of_above
      intro e he
      simp only [StringAllocation.initializationLog, StringAllocation.reservedRegisters, hY', List.mem_cons,
        List.not_mem_nil, or_false] at he
      simp only [Layout.sym_bss_end]
      rcases he with rfl | rfl | rfl
      · dsimp only; rw [nat _ (by omega)]; omega
      · dsimp only
        rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, span4]
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
      · dsimp only
        rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, span4]
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  · have s40 : BitVec.ofNat 64 (N - 112) - 32#64 - 8#64 = BitVec.ofNat 64 (N - 152) := by
      rw [sub 32 (by decide), ofNat_sub_small (by omega) (by omega), show N - 112 - 32 - 8 = N - 152 by omega]
    have hY' : StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) 4#64 = BitVec.ofNat 64 (Y - 16) := hY
    have sp4 : StringAllocation.stringSpan 4#64 = 8#64 := span4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [savedRaLog, StringAllocation.reservationLog, StringAllocation.initializationLog,
        StringAllocation.reservedRegisters, s40, hY', sp4, gd, ys, ls, cs, OutLRange, List.cons_append,
        List.nil_append, nat _ (show N - 152 < 2 ^ 64 by omega), nat _ (show D + 8 < 2 ^ 64 by omega),
        nat _ (show D < 2 ^ 64 by omega), nat _ (show Y - 16 < 2 ^ 64 by omega), and_true] <;>
      (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]) <;> omega

/-- memcpy's code bytes lie in `.text`. -/
theorem mText_bounds {p : Nat × BitVec 8} (hp : p ∈ mText) : 0x80042848 ≤ p.1 ∧ p.1 < 0x80042848 + 296 := by
  obtain ⟨⟨b, k⟩, member, rfl⟩ := List.mem_map.1 hp
  have get := List.mem_zipIdx_iff_getElem?.1 member
  simp only at get
  have bound : k < memcpyCode.length := by
    rcases Nat.lt_or_ge k memcpyCode.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at get
      cases get
  have length : memcpyCode.length = 296 := by decide +kernel
  change 0x80042848 ≤ memcpyBase + k ∧ memcpyBase + k < 0x80042848 + 296
  unfold memcpyBase
  omega

theorem mText_image : ∀ p ∈ mText, imageLive p.1 := fun p hp => by
  have := mText_bounds hp
  exact .inl ⟨by simp only [Image.textBase]; omega, by simp only [Image.textBase, Image.textSize]; omega⟩

theorem resultWord4 (Y : Nat) (h : 16 ≤ Y) (h' : Y < 2 ^ 64) :
    StringCopy.resultWord (BitVec.ofNat 64 Y) 4 = BitVec.ofNat 64 (Y - 8) := by
  simp only [StringCopy.resultWord]
  rw [show (BitVec.ofNat 64 4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, nurseryHeader4 Y h h', ofNat_add_small]
  congr 1; omega

/-- **The copy's memcpy inputs**, completing `CopyMemory`. -/
theorem config_copy {c : Config} {N D Y Lm : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    (nums : ConfigNumbers N D Y Lm) (h2 : R 2 = BitVec.ofNat 64 N) (image : ExecutableImage c)
    (prepIn : LogInW (configWindows N D Y) (prepareLog R (BitVec.ofNat 64 D) roots))
    (alloc : StringCopy.AllocateMemory imageLive (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))
      osTypeData prepare_call.link (frameSp (R 2)) osTypeAddress.toNat osType.length
      (imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))
      (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))) :
    StringCopy.CopyMemory imageLive (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)) osTypeData
      prepare_call.link (frameSp (R 2)) osTypeAddress.toNat osType.length
      (imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots)))
      (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm)
      (memoryView c (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have F := frameSp_eq h2 (by omega) (by omega)
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have hY := nurseryHeader4 Y (by omega) (by omega)
  have rW := resultWord4 Y (by omega) (by omega)
  have ys := youngSlot_eq D (by omega)
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have sub : ∀ k, k ≤ 200 → BitVec.ofNat 64 (N - 112) - BitVec.ofNat 64 k = BitVec.ofNat 64 (N - 112 - k) :=
    fun k hk => ofNat_sub_small (by omega) (by omega)
  have a0 : osTypeAddress.toNat = 0x80055c78 := rfl
  have bss : Layout.sym_bss_end = 0x8007d138 := rfl
  have low : ∀ x, x < 0x8007d138 → OutL (prepareLog R (BitVec.ofNat 64 D) roots) x := fun x hx =>
    outL_of_range (outLRange_of_windows (a := x) (n := 1) prepIn (by
      simp only [configWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega))
      (Nat.le_refl _) (by omega)
  simp only [osType_length] at alloc ⊢
  rw [F] at alloc ⊢
  have hY' : StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) 4#64 = BitVec.ofNat 64 (Y - 16) := hY
  have sp4 : StringAllocation.stringSpan 4#64 = 8#64 := span4
  have lowPoint : ∀ p ∈ mText ++ srcText osTypeAddress.toNat 4
      (imgM (writeLog c.σ.mem (prepareLog R (BitVec.ofNat 64 D) roots))), p.1 < 0x80055c78 + 4 := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · have := mText_bounds h; omega
    · obtain ⟨-, hi, -⟩ := mem_srcText h; rw [a0] at hi; exact hi
  refine { alloc with
    callerSeparate := ?_, copyGeometry := ?_, copyCodeLive := mText_image, copyImage := ?_,
    copyTextSeparate := ?_, copyReadOnly := ?_, copyReadsOutside := ?_, returnOutsideCopy := ?_ }
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [StringCopy.sizeLog, StringCopy.lengthRegisters, StringCopy.entryRegisters,
        StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
        StringAllocation.initializationLog, StringAllocation.reservedRegisters, hY', sp4, ys, sub 8 (by decide),
        sub 24 (by decide), sub 32 (by decide), OutLRange, List.cons_append, List.nil_append,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true] <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
      simp only [rW, nat _ (show Y - 8 < 2 ^ 64 by omega), nat _ (show osTypeAddress.toNat < 2 ^ 64 by rw [a0]; omega),
        a0, Layout.sym_tohost, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> omega
  · refine ⟨fun i hi h => ?_, fun i hi h => ?_⟩ <;>
      simp only [InExt, rW, nat _ (show Y - 8 < 2 ^ 64 by omega), Image.textBase, Image.textSize, Image.rodataBase,
        Image.rodataSize] at h hi <;> omega
  · intro p hp h
    have := lowPoint p hp
    simp only [InExt, rW, nat _ (show Y - 8 < 2 ^ 64 by omega)] at h
    omega
  · refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
    rw [vsa_mem_view]
    rcases List.mem_append.1 hp with h | h
    · have := mText_bounds h
      rw [writeLog_out _ _ _ (low _ (by omega)), OCaml.Vm.Boot.Startup.memcpy_text_loaded image p h]; rfl
    · obtain ⟨-, -, value⟩ := mem_srcText h
      rw [value]; rfl
  · intro p hp
    have := lowPoint p hp
    simp only [StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog, StringCopy.entryRegisters,
      StringCopy.sizeLog, StringCopy.lengthRegisters, StringAllocation.constructorLog, savedRaLog,
      StringAllocation.reservationLog, StringAllocation.initializationLog, StringAllocation.reservedRegisters,
      hY', sp4, ys, sub 8 (by decide), sub 24 (by decide), sub 32 (by decide), OutL, List.cons_append,
      List.nil_append, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · right
    rw [rW, sub 8 (by decide), nat _ (by omega), nat _ (by omega)]; omega

theorem smallHeader (Y : Nat) (h : 48 ≤ Y) (h' : Y < 2 ^ 64) :
    SmallAllocation.nurseryHeader (BitVec.ofNat 64 (Y - 16)) 3#64 = BitVec.ofNat 64 (Y - 48) := by
  simp only [SmallAllocation.nurseryHeader, shift3]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem blockYoung_eq (Y : Nat) (h : 16 ≤ Y) (h' : Y < 2 ^ 64) :
    StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64 = BitVec.ofNat 64 (Y - 16) := by
  rw [osType_length, resultWord4 Y h h']
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_sub_small (by omega) (by omega),
    show Y - 8 - 8 = Y - 16 by omega]

/-- **The triple's nursery inputs** on the memory after the string copy. -/
theorem config_small {c : Config} {N D Y Lm : Nat} {R : Nat → BitVec 64} {roots : BitVec 64}
    {g : Nat → BitVec 8} (nums : ConfigNumbers N D Y Lm) (h2 : R 2 = BitVec.ofNat 64 N)
    (wD : word c Layout.sym_Caml_state = BitVec.ofNat 64 D)
    (wL : word c (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm) :
    SmallAllocation.NurseryMemory allocate_call.link 3#64 0#64 (BitVec.ofNat 64 D)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) (BitVec.ofNat 64 Lm)
      (memoryView c (writeLog c.σ.mem
        (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g))) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have F := frameSp_eq h2 (by omega) (by omega)
  have ys := youngSlot_eq D (by omega)
  have ls := limitSlot_eq D
  have gd : DoubleAllocation.domainGlobal.toNat = Layout.sym_Caml_state := rfl
  have cs : Layout.sym_Caml_state = 0x80064d08 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have inside := beforeSmallLog_in (R := R) (roots := roots) (g := g) (Y := Y) (D := D) (N := N)
    (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have out : ∀ x, (x + 8 ≤ N - 152 ∨ N ≤ x) → (x + 8 ≤ Y - 48 ∨ Y ≤ x) → (x + 8 ≤ D + 8 ∨ D + 16 ≤ x) →
      (x + 8 ≤ D + 288 ∨ D + 296 ≤ x) →
      OutLRange (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g) x 8 :=
    fun x a1 a2 a3 a4 => outLRange_of_windows inside (by
      simp only [configWindows, OutWRange, Layout.off_young_ptr, Layout.off_local_roots, and_true]; omega)
  have BY := blockYoung_eq Y (by omega) (by omega)
  have SH := smallHeader Y (by omega) (by omega)
  rw [BY]
  have wv : ∀ x, OutLRange (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g) x 8 →
      word (memoryView c (writeLog c.σ.mem
        (beforeSmallLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y) osType.length g))) x = word c x :=
    fun x h => view_word h
  refine { domainValue := ?_, youngValue := ?_, limitValue := ?_, youngWrite := ?_, limitRead := ?_,
           headerWrite := ?_, room := ?_, reserveImage := ?_, initializeImage := ?_, domainAfterHeader := ?_,
           youngAfterHeader := ?_ }
  · rw [gd, wv _ (out _ (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega)), wD]
  · change bytesT (writeLog c.σ.mem _) _ 8 = _
    rw [beforeSmallLog_split, word_last_store]
    · rw [osType_length, span4]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]; omega
    · rw [ys, nat _ (by omega)]
      simp only [StringAllocation.initializationLog, StringAllocation.reservedRegisters, osType_length,
        nurseryHeader4 Y (by omega) (by omega), resultWord4 Y (by omega) (by omega), span4, byteCopyLog,
        allocateLog, allocateRegisters, F, OutLRange, List.cons_append, List.nil_append, List.range_succ,
        List.range_zero, List.map_cons, List.map_nil, List.append_assoc,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
      omega
  · rw [ls, nat _ (by omega), wv _ (out _ (by omega) (by omega) (by omega) (by omega))]
    simpa only [Layout.off_young_limit, Nat.add_zero] using wL
  · rw [ys]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  · rw [ls]; exact (window_of_nat (by rw [tohost]; omega) (by omega) (by omega)).read
  · rw [SH]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  · rw [SH]; simp only [guardB]
    exact Vsa.Sim.bltu_false_of_ge _ _ (by rw [nat _ (by omega), nat _ (by omega)]; omega)
  · apply imageOutside_of_above
    intro e he
    simp only [StringAllocation.reservationLog, ys, List.mem_singleton] at he
    subst he
    rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
  · apply imageOutside_of_above
    intro e he
    simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH, List.mem_singleton] at he
    subst he
    rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
  · rw [gd]
    change bytesT (writeLog (writeLog c.σ.mem _) _) _ 8 = _
    rw [bytesT_writeLog_out _ (by
      simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog, SmallAllocation.initializationLog,
        SmallAllocation.reservedRegisters, SH, ys, cs, OutLRange, List.cons_append, List.nil_append,
        nat _ (show D + 8 < 2 ^ 64 by omega), nat _ (show Y - 48 < 2 ^ 64 by omega), and_true]
      omega)]
    exact (wv _ (out _ (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega) (by rw [cs]; omega))).trans wD
  · simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog]
    rw [show ∀ (e : WEntry) (l : List WEntry), [e] ++ l = [] ++ e :: l from fun _ _ => rfl, word_last_store]
    · rfl
    · simp only [SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH, ys, OutLRange,
        nat _ (show D + 8 < 2 ^ 64 by omega), nat _ (show Y - 48 < 2 ^ 64 by omega), and_true]
      omega

theorem tripleWord_eq (Y : Nat) (h : 48 ≤ Y) (h' : Y < 2 ^ 64) :
    tripleWord (BitVec.ofNat 64 (Y - 16)) = BitVec.ofNat 64 (Y - 40) := by
  simp only [tripleWord]
  rw [smallHeader Y h h', show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_add_small]
  congr 1; omega

/-- **The triple's layout** around the native frame `F = N - 112`. -/
theorem config_finish_layout {N D Y Lm : Nat} {roots : BitVec 64} (nums : ConfigNumbers N D Y Lm) :
    FinishLayout (BitVec.ofNat 64 (N - 112)) (BitVec.ofNat 64 (Y - 40)) (BitVec.ofNat 64 (Y - 8))
      (BitVec.ofNat 64 D) roots := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have gd : DoubleAllocation.domainGlobal = BitVec.ofNat 64 0x80064d08 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have add : ∀ x k, x + k < 2 ^ 64 → BitVec.ofNat 64 x + BitVec.ofNat 64 k = BitVec.ofNat 64 (x + k) :=
    fun x k _ => ofNat_add_small
  have w : ∀ n, 0x80061fc0 + 16 ≤ n → n + 8 ≤ 0x100000000 → n % 8 = 0 → WriteWindow (BitVec.ofNat 64 n) 8 :=
    fun n lo hi al => window_of_nat (by rw [tohost]; exact lo) hi al
  have roots288 : BitVec.ofNat 64 D + BitVec.ofNat 64 Layout.off_local_roots = BitVec.ofNat 64 (D + 288) := by
    rw [ofNat_add_small]; rfl
  refine { stringSlot := ?_, resultSlot := ?_, firstField := ?_, secondField := ?_, thirdField := ?_,
           domainRead := ?_, rootsWrite := ?_, savedRa := ?_, savedS0 := ?_, savedS1 := ?_, savedS2 := ?_,
           resultOutsideFields := ?_, domainOutside := ?_, savedOutside := ?_, rootsOutsideFields := ?_,
           image := ?_ }
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · exact w _ (by omega) (by omega) (by omega)
  · exact w _ (by omega) (by omega) (by omega)
  · rw [add _ _ (by omega)]; exact w _ (by omega) (by omega) (by omega)
  · rw [add _ _ (by omega)]; exact w _ (by omega) (by omega) (by omega)
  · rw [gd]; exact (w _ (by omega) (by omega) (by decide)).read
  · rw [roots288]; exact w _ (by omega) (by omega) (by omega)
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · rw [add _ _ (by omega)]; exact (w _ (by omega) (by omega) (by omega)).read
  · simp only [OutLRange, add _ _ (show Y - 40 + 8 < 2 ^ 64 by omega), add _ _ (show Y - 40 + 16 < 2 ^ 64 by omega),
      nat _ (show Y - 40 < 2 ^ 64 by omega), nat _ (show Y - 40 + 8 < 2 ^ 64 by omega),
      nat _ (show Y - 40 + 16 < 2 ^ 64 by omega), nat _ (show N - 112 < 2 ^ 64 by omega), and_true]
    omega
  · simp only [tripleLog, List.take, OutLRange, gd, add _ _ (show Y - 40 + 8 < 2 ^ 64 by omega),
      add _ _ (show Y - 40 + 16 < 2 ^ 64 by omega), nat _ (show Y - 40 < 2 ^ 64 by omega),
      nat _ (show Y - 40 + 8 < 2 ^ 64 by omega), nat _ (show Y - 40 + 16 < 2 ^ 64 by omega),
      nat _ (show N - 112 < 2 ^ 64 by omega), nat _ (show 0x80064d08 < 2 ^ 64 by omega), and_true]
    omega
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    simp only [tripleLog, OutLRange, roots288, add _ _ (show Y - 40 + 8 < 2 ^ 64 by omega),
      add _ _ (show Y - 40 + 16 < 2 ^ 64 by omega), nat _ (show Y - 40 < 2 ^ 64 by omega),
      nat _ (show Y - 40 + 8 < 2 ^ 64 by omega), nat _ (show Y - 40 + 16 < 2 ^ 64 by omega),
      nat _ (show N - 112 < 2 ^ 64 by omega), nat _ (show D + 288 < 2 ^ 64 by omega), and_true]
    rcases hk with rfl | rfl | rfl | rfl <;>
      rw [add _ _ (by omega), nat _ (by omega)] <;> omega
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    simp only [rootsEntry, OutLRange, roots288, nat _ (show Y - 40 < 2 ^ 64 by omega),
      nat _ (show D + 288 < 2 ^ 64 by omega), and_true]
    rcases hk with rfl | rfl | rfl <;> omega
  · apply imageOutside_of_above
    intro e he
    simp only [tripleLog, roots288, add _ _ (show Y - 40 + 8 < 2 ^ 64 by omega),
      add _ _ (show Y - 40 + 16 < 2 ^ 64 by omega), List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [Layout.sym_bss_end]
    rcases he with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [nat _ (by omega)] <;> omega

/-- **The four register saves survive every later store.** -/
theorem config_savedTail {N D Y Lm : Nat} {R : Nat → BitVec 64} {roots : BitVec 64} {g : Nat → BitVec 8}
    (nums : ConfigNumbers N D Y Lm) (h2 : R 2 = BitVec.ofNat 64 N) :
    ∀ k ∈ [80, 88, 96, 104], OutLRange
      (afterSavedLog R (BitVec.ofNat 64 D) roots (BitVec.ofNat 64 Y)
        (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) osType.length g)
      (frameSp (R 2) + BitVec.ofNat 64 k).toNat 8 := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  intro k hk
  have F := frameSp_eq h2 (by omega) (by omega)
  have hk' : k + 8 ≤ 112 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  rw [F, ofNat_add_small, toNat_ofNat_small (by omega)]
  simp only [afterSavedLog, prepareLog, savedLog, List.drop, List.cons_append, List.nil_append,
    StringCopy.completeLog, StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog,
    StringCopy.entryRegisters, StringCopy.sizeLog, StringCopy.lengthRegisters,
    StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
    StringAllocation.initializationLog, StringAllocation.reservedRegisters, StringAllocation.nurseryHeader,
    StringCopy.resultWord, DoubleAllocation.youngSlot, osType_length, span4, byteCopyLog,
    afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
    SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SmallAllocation.nurseryHeader, shift3,
    frameSp, h2, frameSp_ofNat (N := N) (by omega) (by omega), Layout.off_local_roots, Layout.off_young_ptr,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.append_assoc, OutLRange,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> omega

/-- The copied string object misses the triple's stores. -/
theorem config_stringOutsideTriple {N D Y Lm : Nat} {roots : BitVec 64} (nums : ConfigNumbers N D Y Lm) :
    ObjectOutside (tripleLog (BitVec.ofNat 64 (N - 112)) (BitVec.ofNat 64 (Y - 40)) (BitVec.ofNat 64 (Y - 8))
        (BitVec.ofNat 64 D) roots)
      (Y - 8) (.bytes (List.replicate 4 0)) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have w : (Obj.bytes (List.replicate 4 (0 : UInt8))).wosize = 1 := rfl
  refine ⟨?_, ?_⟩ <;> (try rw [w]) <;>
    simp only [tripleLog, OutLRange, Layout.off_local_roots, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.reducePow, and_true] <;> omega

/-- The triple's header misses the triple's stores. -/
theorem config_headerOutsideTriple {N D Y Lm : Nat} {roots : BitVec 64} (nums : ConfigNumbers N D Y Lm) :
    OutLRange (tripleLog (BitVec.ofNat 64 (N - 112)) (BitVec.ofNat 64 (Y - 40)) (BitVec.ofNat 64 (Y - 8))
        (BitVec.ofNat 64 D) roots) (Y - 48) 8 := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  simp only [tripleLog, OutLRange, Layout.off_local_roots, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
    Nat.reducePow, and_true]
  omega

/-- The copied string and the result slot miss the triple's reservation. -/
theorem config_afterCopy {N D Y Lm : Nat} {R : Nat → BitVec 64} (nums : ConfigNumbers N D Y Lm)
    (h2 : R 2 = BitVec.ofNat 64 N) :
    ObjectOutside (afterCopyLog R (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y)
        (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64) osType.length)
      (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length).toNat (.bytes (List.replicate osType.length 0)) ∧
    OutLRange (SmallAllocation.constructorLog allocate_call.link 3#64 0#64 (BitVec.ofNat 64 D)
        (StringCopy.resultWord (BitVec.ofNat 64 Y) osType.length - 8#64)) (frameSp (R 2) + 8#64).toNat 8 ∧
    ImageOutside (allocateLog (allocateRegisters R (BitVec.ofNat 64 Y) osType.length)) := by
  obtain ⟨nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap⟩ := nums
  have F := frameSp_eq h2 (by omega) (by omega)
  have BY := blockYoung_eq Y (by omega) (by omega)
  have SH := smallHeader Y (by omega) (by omega)
  have rW := resultWord4 Y (by omega) (by omega)
  have w : (Obj.bytes (List.replicate osType.length (0 : UInt8))).wosize = 1 := rfl
  rw [BY]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [osType_length, rW, afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
      StringAllocation.reservationLog, SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH,
      DoubleAllocation.youngSlot, F, OutLRange, List.cons_append, List.nil_append, Layout.off_young_ptr,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · rw [w]
    simp only [osType_length, rW, afterCopyLog, allocateLog, allocateRegisters, SmallAllocation.constructorLog,
      StringAllocation.reservationLog, SmallAllocation.initializationLog, SmallAllocation.reservedRegisters, SH,
      DoubleAllocation.youngSlot, F, OutLRange, List.cons_append, List.nil_append, Layout.off_young_ptr,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · simp only [SmallAllocation.constructorLog, StringAllocation.reservationLog, SmallAllocation.initializationLog,
      SmallAllocation.reservedRegisters, SH, DoubleAllocation.youngSlot, F, OutLRange, List.cons_append,
      List.nil_append, Layout.off_young_ptr, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · apply imageOutside_of_above
    intro e he
    simp only [allocateLog, allocateRegisters, F, ← BitVec.ofNat_add, List.mem_singleton] at he
    subst he
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Layout.sym_bss_end]
    omega

end OCaml.Vm.Sim
