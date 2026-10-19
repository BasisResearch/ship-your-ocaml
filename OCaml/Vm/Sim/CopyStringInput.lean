import OCaml.Vm.Sim.StringAllocReturn
import OCaml.Vm.Primitives.StringCopyMachine
import OCaml.Vm.Primitives.Memmove
import OCaml.Vm.Boot.Startup.LibraryText

/-!
# `caml_copy_string`'s memory inputs at a native call site

The generated copy-string contract (`StringCopy.CopyMemory`) takes its stack
slots, nursery metadata, string nursery geometry, library image and source
bytes as inputs. `copy_memory_at` supplies them from scalar facts about the
config at the call (`CopySite`): the native stack pointer, the domain record,
the nursery, and the source C string. The string allocators
(`caml_sys_get_config`, `caml_sys_executable_name`, `caml_sys_get_argv`)
instantiate it.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable
open ArgvTuple (frameSp memoryView)
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Memcpy

/-- `gp` holds `gpV`: the library's read-only register. -/
theorem roR_of_gp {live : Nat → Prop} {c : Config} (gp : gpr c 3 = some gpV) :
    ROHolds (vsaModel live) c roR [] := by
  refine ⟨fun q hq => ?_, fun _ hq => nomatch hq⟩
  obtain rfl := List.mem_singleton.1 hq
  change vsaReg c 3 = _
  simp only [vsaReg]
  change (gpr c 3).getD 0 = _
  rw [gp]; rfl

theorem vsa_mem_view {live : Nat → Prop} (c : Config) (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    (vsaModel live).mem (memoryView c mem) a = (mem[a]?).getD 0 := rfl

/-- A store window of any width in RAM above `tohost`, from naturals. -/
theorem window_nat_width {n w : Nat} (lo : Layout.sym_tohost + 16 ≤ n) (hi : n + w ≤ 0x100000000)
    (al : n % w = 0) : WriteWindow (BitVec.ofNat 64 n) w := by
  have e : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_small (by omega)
  have t : 0x80000000 + 16 ≤ Layout.sym_tohost + 16 := by decide
  exact ⟨by rw [e]; omega, by rw [e]; exact hi, by rw [e]; exact lo, by rw [e]; exact al⟩

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


/-- **The scalar facts at a `caml_copy_string` call**: the native stack
pointer `S`, the domain record `D`, the nursery `[Lm, Y)` with room for the
string block, and the source C string of `len` bytes at `a`, apart from the
call's stores. `spanN` is the string's padded payload (`stringSpan len`). -/
structure CopySite (cv : Config) (S D Y Lm a len spanN : Nat) : Prop where
  image : ExecutableImage cv
  gp : gpr cv 3 = some gpV
  nativeLow : 0x86800000 + 64 ≤ S
  nativeHigh : S ≤ 0x88000000
  nativeAligned : S % 16 = 0
  domainLow : 0x8007d138 ≤ D
  domainHigh : D + 928 ≤ 0x86800000
  domainAligned : D % 8 = 0
  youngHigh : Y ≤ 0x86800000
  youngAligned : Y % 8 = 0
  limitLow : 0x8007d138 ≤ Lm
  room : Lm + 8 + spanN ≤ Y
  apart : D + 928 ≤ Lm ∨ Y ≤ D
  span : StringAllocation.stringSpan (BitVec.ofNat 64 len) = BitVec.ofNat 64 spanN
  spanFits : len < spanN ∧ spanN % 8 = 0 ∧ spanN ≤ 4096
  small : guardB .BLTU 256#64 (StringAllocation.stringWords (BitVec.ofNat 64 len)) = false
  wD : word cv Layout.sym_Caml_state = BitVec.ofNat 64 D
  wY : word cv (D + Layout.off_young_ptr) = BitVec.ofNat 64 Y
  wL : word cv (D + Layout.off_young_limit) = BitVec.ofNat 64 Lm
  srcLow : 0x80000000 ≤ a
  srcHtif : a + len + 8 ≤ 0x80061fc0 ∨ 0x80061fd0 ≤ a
  srcNursery : a + len + 1 ≤ Lm
  srcDomain : a + len + 1 ≤ D ∨ D + 928 ≤ a
  bytesNz : ∀ i, i < len → imgM cv.σ.mem (a + i) ≠ 0
  bytesNul : imgM cv.σ.mem (a + len) = 0

theorem nurseryHeader_eq {Y len spanN : Nat}
    (span : StringAllocation.stringSpan (BitVec.ofNat 64 len) = BitVec.ofNat 64 spanN)
    (h : 8 + spanN ≤ Y) (h' : Y < 2 ^ 64) :
    StringAllocation.nurseryHeader (BitVec.ofNat 64 Y) (BitVec.ofNat 64 len) = BitVec.ofNat 64 (Y - 8 - spanN) := by
  simp only [StringAllocation.nurseryHeader, span]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem resultWord_eq {Y len spanN : Nat}
    (span : StringAllocation.stringSpan (BitVec.ofNat 64 len) = BitVec.ofNat 64 spanN)
    (h : 8 + spanN ≤ Y) (h' : Y < 2 ^ 64) :
    StringCopy.resultWord (BitVec.ofNat 64 Y) len = BitVec.ofNat 64 (Y - spanN) := by
  simp only [StringCopy.resultWord]
  rw [nurseryHeader_eq span h h', show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat_add_small]
  congr 1; omega

/-- **`caml_copy_string`'s memory inputs** at a `CopySite`, for any caller
return address `ra`. -/
theorem copy_memory_at {cv : Config} {S D Y Lm a len spanN : Nat} (ra : BitVec 64)
    (site : CopySite cv S D Y Lm a len spanN) :
    StringCopy.CopyMemory imageLive cv.σ.mem (List.range' a (len + 1)) ra (BitVec.ofNat 64 S) a len
      (imgM cv.σ.mem) (BitVec.ofNat 64 D) (BitVec.ofNat 64 Y) (BitVec.ofNat 64 Lm) cv := by
  obtain ⟨image, gp, nl, nh, na, dl, dh, da, yh, ya, ll, rm, ap, span, ⟨lt, sa, sb⟩, small, wD, wY, wL,
    srcLow, srcHtif, srcN, srcD, nz, nul⟩ := site
  have tohost : Layout.sym_tohost = 0x80061fc0 := rfl
  have nat : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n h => toNat_ofNat_small h
  have sub : ∀ k, k ≤ 64 → BitVec.ofNat 64 S - BitVec.ofNat 64 k = BitVec.ofNat 64 (S - k) :=
    fun k hk => ofNat_sub_small (by omega) (by omega)
  have hH := nurseryHeader_eq span (Y := Y) (by omega) (by omega)
  have rW := resultWord_eq span (Y := Y) (by omega) (by omega)
  have ys := youngSlot_eq D (by omega)
  have ls := limitSlot_eq D
  have gd : DoubleAllocation.domainGlobal.toNat = Layout.sym_Caml_state := rfl
  have cs : Layout.sym_Caml_state = 0x80064d08 := rfl
  have s40 : BitVec.ofNat 64 S - 32#64 - 8#64 = BitVec.ofNat 64 (S - 40) := by
    rw [sub 32 (by decide), ofNat_sub_small (by omega) (by omega), show S - 32 - 8 = S - 40 by omega]
  have last : BitVec.ofNat 64 (Y - 8 - spanN) + 8#64 + BitVec.ofNat 64 spanN - 8#64 = BitVec.ofNat 64 (Y - 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  have pad : BitVec.ofNat 64 (Y - 8 - spanN) + 8#64 + (BitVec.ofNat 64 spanN - 1#64) = BitVec.ofNat 64 (Y - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  have lowPoint : ∀ p ∈ mText ++ srcText a len (imgM cv.σ.mem), (a ≤ p.1 ∧ p.1 < a + len) ∨ p.1 < 0x80053180 := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · have := mText_bounds h; right; omega
    · obtain ⟨lo, hi, -⟩ := mem_srcText h; left; exact ⟨lo, hi⟩
  have s8 : (BitVec.ofNat 64 S - 8#64).toNat = S - 8 := by rw [sub 8 (by decide), nat _ (by omega)]
  have s24 : (BitVec.ofNat 64 S - 24#64).toNat = S - 24 := by rw [sub 24 (by decide), nat _ (by omega)]
  have he : Vsa.Sim.DlHeap.heapEnd = 0x86800000 := rfl
  have ws : ∀ k, 8 ≤ k → k ≤ 64 → k % 8 = 0 → WriteWindow (BitVec.ofNat 64 S - BitVec.ofNat 64 k) 8 := fun k a b c => by
    rw [sub k b]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
  refine { returnSlot := ws 8 (by decide) (by decide) (by decide),
           sourceSlot := ws 24 (by decide) (by decide) (by decide),
           saveImage := ?_, saveLibrary := ?_, libraryImage := imageLive_image, codeLive := snpText_image,
           readOnly := ⟨(roR_of_gp gp).1, ?_⟩, «string» := ?_,
           lengthSlot := ws 32 (by decide) (by decide) (by decide), lengthImage := ?_,
           metadata := ⟨?_, ?_, ?_⟩, metadataOutside := ?_, geometry := ?_, separate := ?_,
           callerSeparate := ?_, copyGeometry := ?_, copyCodeLive := mText_image, copyImage := ?_,
           copyTextSeparate := ?_, copyReadOnly := ⟨(fun _ h => nomatch h), ?_⟩, copyReadsOutside := ?_,
           returnOutsideCopy := ?_ }
  · apply imageOutside_of_above
    intro e he'
    simp only [StringCopy.saveLog, StringCopy.entryRegisters, List.mem_cons, List.not_mem_nil, or_false] at he'
    simp only [Layout.sym_bss_end]
    rcases he' with rfl | rfl
    · dsimp only; rw [s8]; omega
    · dsimp only; rw [s24]; omega
  · intro p hp
    have below : p.1 < a + len + 1 ∨ p.1 < 0x80053180 := by
      rcases List.mem_append.1 hp with h | h
      · right; exact snpText_below p h
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
        obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hx
        left; omega
    simp only [StringCopy.saveLog, StringCopy.entryRegisters, OutL, s8, s24, and_true]
    omega
  · intro p hp
    change (cv.σ.mem[p.1]?).getD 0 = p.2
    rcases List.mem_append.1 hp with h | h
    · rw [OCaml.Vm.Boot.Startup.snp_text_loaded image p h]; rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
      rfl
  · refine ⟨fun x lo hi => Or.inl ⟨List.mem_range'.2 ⟨x - a, by omega, by omega⟩, rfl⟩, nz, nul, srcLow,
      by omega, by omega⟩
  · apply imageOutside_of_above
    intro e he'
    simp only [StringCopy.sizeLog, StringCopy.lengthRegisters, StringCopy.entryRegisters, List.mem_singleton] at he'
    subst he'
    rw [sub 32 (by decide), nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
  · rw [gd, cs, ← cs]; exact wD
  · rw [ys, nat _ (by omega)]; simpa only [Layout.off_young_ptr] using wY
  · rw [ls, nat _ (by omega)]; simpa only [Layout.off_young_limit, Nat.add_zero] using wL
  · simp only [StringCopy.prefixLog, StringCopy.saveLog, StringCopy.entryRegisters, StringCopy.sizeLog,
      StringCopy.lengthRegisters, sub 8 (by decide), sub 24 (by decide), sub 32 (by decide),
      nat _ (show S - 8 < 2 ^ 64 by omega), nat _ (show S - 24 < 2 ^ 64 by omega),
      nat _ (show S - 32 < 2 ^ 64 by omega), List.cons_append, List.nil_append]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [OutLRange, gd, ys, ls, nat _ (show D + 8 < 2 ^ 64 by omega),
      nat _ (show D < 2 ^ 64 by omega), cs, and_true] <;> omega
  · refine { stackWrite := ?_, youngWrite := ?_, limitRead := ?_, headerWrite := ?_, lastWrite := ?_,
             paddingWrite := ?_, small := small, room := ?_, stackImage := ?_, reserveImage := ?_,
             initializeImage := ?_ }
    · rw [s40]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [ys]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [ls]; exact (window_of_nat (by rw [tohost]; omega) (by omega) (by omega)).read
    · rw [hH]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [hH, span, last]; exact window_of_nat (by rw [tohost]; omega) (by omega) (by omega)
    · rw [hH, span, pad]; exact window_nat_width (by rw [tohost]; omega) (by omega) (by omega)
    · rw [hH]; simp only [guardB]
      exact Vsa.Sim.bltu_false_of_ge _ _ (by rw [nat _ (by omega), nat _ (by omega)]; omega)
    · apply imageOutside_of_above
      intro e he'
      simp only [savedRaLog, s40, List.mem_singleton] at he'
      subst he'
      rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
    · apply imageOutside_of_above
      intro e he'
      simp only [StringAllocation.reservationLog, ys, List.mem_singleton] at he'
      subst he'
      rw [nat _ (by omega)]; simp only [Layout.sym_bss_end]; omega
    · apply imageOutside_of_above
      intro e he'
      simp only [StringAllocation.initializationLog, StringAllocation.reservedRegisters, hH, span,
        List.mem_cons, List.not_mem_nil, or_false] at he'
      simp only [Layout.sym_bss_end]
      rcases he' with rfl | rfl | rfl <;> dsimp only <;>
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [savedRaLog, StringAllocation.reservationLog, StringAllocation.initializationLog,
        StringAllocation.reservedRegisters, s40, hH, span, gd, ys, ls, cs, OutLRange, List.cons_append,
        List.nil_append, nat _ (show S - 40 < 2 ^ 64 by omega), nat _ (show D + 8 < 2 ^ 64 by omega),
        nat _ (show D < 2 ^ 64 by omega), nat _ (show Y - 8 - spanN < 2 ^ 64 by omega), and_true] <;>
      (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]) <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [StringCopy.sizeLog, StringCopy.lengthRegisters, StringCopy.entryRegisters,
        StringAllocation.constructorLog, savedRaLog, StringAllocation.reservationLog,
        StringAllocation.initializationLog, StringAllocation.reservedRegisters, hH, span, ys, sub 8 (by decide),
        sub 24 (by decide), sub 32 (by decide), OutLRange, List.cons_append, List.nil_append,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true] <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
      simp only [rW, nat _ (show Y - spanN < 2 ^ 64 by omega), nat _ (show a < 2 ^ 64 by omega),
        Layout.sym_tohost] <;> omega
  · refine ⟨fun i hi h => ?_, fun i hi h => ?_⟩ <;>
      simp only [InExt, rW, nat _ (show Y - spanN < 2 ^ 64 by omega), Image.textBase, Image.textSize,
        Image.rodataBase, Image.rodataSize] at h hi <;> omega
  · intro p hp h
    have := lowPoint p hp
    simp only [InExt, rW, nat _ (show Y - spanN < 2 ^ 64 by omega)] at h
    omega
  · intro p hp
    change (cv.σ.mem[p.1]?).getD 0 = p.2
    rcases List.mem_append.1 hp with h | h
    · rw [OCaml.Vm.Boot.Startup.memcpy_text_loaded image p h]; rfl
    · obtain ⟨-, -, value⟩ := mem_srcText h
      rw [value]; rfl
  · intro p hp
    have := lowPoint p hp
    simp only [StringCopy.allocationLog, StringCopy.prefixLog, StringCopy.saveLog, StringCopy.entryRegisters,
      StringCopy.sizeLog, StringCopy.lengthRegisters, StringAllocation.constructorLog, savedRaLog,
      StringAllocation.reservationLog, StringAllocation.initializationLog, StringAllocation.reservedRegisters,
      hH, span, ys, sub 8 (by decide), sub 24 (by decide), sub 32 (by decide), OutL, List.cons_append,
      List.nil_append, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, and_true]
    omega
  · right
    rw [rW, sub 8 (by decide), nat _ (by omega), nat _ (by omega)]; omega

end OCaml.Vm.Sim
