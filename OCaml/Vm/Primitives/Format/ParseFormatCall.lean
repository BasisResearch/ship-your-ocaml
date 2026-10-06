import OCaml.Vm.Primitives.Format.ParseFormat
import OCaml.Vm.Primitives.Format.StringLengthCall
import OCaml.Vm.Primitives.LibraryStrlenCall
import OCaml.Vm.Primitives.Memmove
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Boot.Startup.LibraryText

/-!
# `parse_format` as a call summary

`parse_format(fmt, suffix, buf)` (ints.c) copies the OCaml format string
`fmt` (length `n`) into the 32-byte buffer `buf`, then the C suffix (here
`ARCH_INTNAT_PRINTF_FORMAT` = `"l"`) before the conversion character, then
the conversion and a terminator, and returns the conversion character. The
path is the generated block family of `--ocaml-format` with three calls
spliced in: `caml_string_length` (`string_length_call`), `strlen` on the
suffix (`strlen_call`) and two `memmove`s (`memmove_call`).

The composition is split by phase to stay within the elaboration budget:
`measure` runs the prologue and both length calls.
-/

namespace OCaml.Vm.Primitives.Format.ParseFormat
set_option autoImplicit false
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast OCaml.Vm.Primitives
open OCaml.Vm.Boot.Startup

/-- A present register reads as its own value. -/
theorem gpr_getD {c : Config} {k : Nat} (h : (gprGet c.σ k).isSome) :
    gprGet c.σ k = some ((gprGet c.σ k).getD 0) := by
  cases e : gprGet c.σ k with
  | none => rw [e] at h; cases h
  | some v => rfl

/-- The registers at the entry, as the blocks' symbolic inputs. -/
def entryRegs (c : Config) : Nat → BitVec 64 := fun k => (gprGet c.σ k).getD 0

/-- parse_format's frame slot `off` (below `sp - 48`), normalized once. -/
theorem frame_slot {sp : BitVec 64} (frame : NativeFrame sp 48) (off : Nat) (bound : off ≤ 48) :
    sp - 48#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (nativeFrameBase sp 48 + off) := by
  rw [BitVec.sub_eq_add_neg]
  exact frame.address off bound

theorem frame_base {sp : BitVec 64} (frame : NativeFrame sp 48) :
    sp - 48#64 = BitVec.ofNat 64 (nativeFrameBase sp 48) := by
  have := frame_slot frame 0 (by decide)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, Nat.add_zero] at this

theorem frame_word {sp : BitVec 64} (frame : NativeFrame sp 48) (off : Nat) (bound : off + 8 ≤ 48)
    (aligned : off % 8 = 0) : WriteWindow (sp - 48#64 + BitVec.ofNat 64 off) 8 := by
  rw [frame_slot frame off (by omega)]
  exact frame.word bound aligned

/-- The prologue's six saves lie in the frame. -/
theorem proLog_inside {R : Nat → BitVec 64} {loads : List (List (BitVec 8))} {sp : BitVec 64}
    (stack : R 2 = sp) (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (proLog R loads) := by
  have slot (off : Nat) (bound : off + 8 ≤ 48) :
      (sp - 48#64 + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 48 + off := by
    rw [frame_slot frame off (by omega)]; exact frame.slot_nat (by omega)
  have base : (sp - 48#64).toNat = nativeFrameBase sp 48 := by
    rw [frame_base frame]; simpa using frame.slot_nat (off := 0) (by decide)
  have top : nativeFrameBase sp 48 + 48 = sp.toNat := by
    have := frame.lower; unfold nativeFrameBase; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  simp only [proLog, stack, LogInW, InsideW]
  rw [slot 40 (by decide), slot 32 (by decide), slot 16 (by decide), slot 8 (by decide), base,
    slot 24 (by decide)]
  refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩,
    Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

/-- Every listed GPR holds its own value, at a library-ready state. -/
theorem holds_entry {live : Nat → Prop} {c : Config} (good : VsaOk live c) :
    ∀ keys : List Nat, (∀ k ∈ keys, 1 ≤ k ∧ k ≤ 31) →
      GHolds c.σ (keys.map fun k => (k, entryRegs c k))
  | [], _ => trivial
  | k :: keys, hk =>
    ⟨gpr_getD (good.gpr k (hk k (by simp)).1 (hk k (by simp)).2),
      holds_entry good keys fun j hj => hk j (List.mem_cons_of_mem _ hj)⟩

/-- parse_format's entry: arguments, a 48-byte native frame, a placed OCaml
format string apart from it, and library readiness (`VsaOk`, the global
pointer). -/
structure MeasureInput (live : Nat → Prop) (ra sp : BitVec 64) (f buf n : Nat) (c : Config) : Prop
    extends LeafInput ra c where
  libraryGood : VsaOk live c
  globalPointer : ROHolds (vsaModel live) c roR []
  stack : gpr c 2 = some sp
  fmt : gpr c 10 = some (BitVec.ofNat 64 f)
  suffix : gpr c 11 = some 0x80055088#64
  buffer : gpr c 12 = some (BitVec.ofNat 64 buf)
  frame : NativeFrame sp 48
  geometry : StringGeometry f n
  shape : StringShape c f n
  /-- the string object, header included, misses the frame -/
  apart : f + 8 * ((n + 8) / 8) ≤ nativeFrameBase sp 48 ∨ sp.toNat + 8 ≤ f

/-- The registers `measure_length` may change. -/
def lengthWritten : List Nat := [1, 2, 8, 10, 15, 18, 20]

/-- After the prologue and `caml_string_length`: back at `0x80010428` with
the length in `a0`, the frame saves in memory and library readiness kept. -/
structure LengthDone (live : Nat → Prop) (sp : BitVec 64) (f buf n : Nat) (before after : Config) : Prop
    extends LeafInput pro_call.link after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some pro_call.link
  memory : after.σ.mem = writeLog before.σ.mem (proLog (entryRegs before) [])
  output : after.σ.sailOutput = before.σ.sailOutput
  length : gpr after 10 = some (BitVec.ofNat 64 n)
  stack : gpr after 2 = some (sp - 48#64)
  buffer : gpr after 8 = some (BitVec.ofNat 64 buf)
  suffix : gpr after 18 = some 0x80055088#64
  fmt : gpr after 20 = some (BitVec.ofNat 64 f)
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ lengthWritten → gpr after k = gpr before k

theorem entry_value {c : Config} {k : Nat} {v : BitVec 64} (h : gpr c k = some v) : entryRegs c k = v := by
  simp only [entryRegs]; change (gpr c k).getD 0 = v; rw [h]; rfl

/-- **The prologue and `caml_string_length`.** -/
theorem measure_length {live : Nat → Prop} {ra sp : BitVec 64} {f buf n : Nat} (c : Config)
    (h : MeasureInput live ra sp f buf n c) :
    FnSummary 0x800103fc#64 (fun d => d = c) (LengthDone live sp f buf n c) := by
  let R := entryRegs c
  have hR1 : R 1 = ra := entry_value h.raReg
  have hR2 : R 2 = sp := entry_value h.stack
  have hR10 : R 10 = BitVec.ofNat 64 f := entry_value h.fmt
  have hR11 : R 11 = 0x80055088#64 := entry_value h.suffix
  have hR12 : R 12 = BitVec.ofNat 64 buf := entry_value h.buffer
  have regs : GHolds c.σ (pro_input R) :=
    holds_entry h.libraryGood [1, 2, 8, 9, 10, 11, 12, 18, 19, 20] (by decide)
  have leaf : LeafInput (R 1) c := by rw [hR1]; exact h.toLeafInput
  have w4 : WriteWindow (R 2 - 48#64) 8 := by
    rw [hR2, frame_base h.frame]; simpa using h.frame.word (off := 0) (by decide) (by decide)
  have S := pro_fast c R leaf regs (by rw [hR2]; exact frame_word h.frame 40 (by decide) (by decide))
    (by rw [hR2]; exact frame_word h.frame 32 (by decide) (by decide))
    (by rw [hR2]; exact frame_word h.frame 16 (by decide) (by decide))
    (by rw [hR2]; exact frame_word h.frame 8 (by decide) (by decide)) w4
    (by rw [hR2]; exact frame_word h.frame 24 (by decide) (by decide))
    (h.frame.image_outside (proLog_inside hR2 h.frame))
  apply summary_bind S (fun _ p => p.pc)
  intro e p
  have args : GHolds e.σ [(2, R 2 - 48#64), (8, R 12), (10, R 10), (18, R 11), (20, R 10)] :=
    holds_project p.regs (by simp [pro_regs, lookupG])
  have J := call_registers_summary pro_call_shape pro_call_decode e (pro_call_pins p.image) p.good p.image
    p.tick p.minstret _ args (by change KeysOK [2, 8, 10, 18, 20]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have memE : entered.σ.mem = writeLog c.σ.mem (proLog R []) := q.memory.trans p.memory
  have lower := h.geometry.lower
  have out (x w : Nat) (lo : f - 8 ≤ x) (hi : x + w ≤ f + 8 * ((n + 8) / 8)) :
      OutLRange (proLog R []) x w := by
    apply OCaml.Vm.Sim.outLRange_of_windows (proLog_inside hR2 h.frame)
    refine ⟨?_, trivial⟩
    rcases h.apart with below | above
    · exact Or.inl (by dsimp only; omega)
    · exact Or.inr (by dsimp only; omega)
  have header : word entered (f - 8) = word c (f - 8) :=
    Reloc.bytesT_congr (copied_of_writeLog memE (out _ 8 (Nat.le_refl _) (by omega)))
  have padding : byte entered (f + 8 * ((n + 8) / 8) - 1) = byte c (f + 8 * ((n + 8) / 8) - 1) :=
    Reloc.bytesT_congr (copied_of_writeLog memE (out _ 1 (by omega) (by omega)))
  have shapeE : StringShape entered f n :=
    ⟨by rw [header]; exact h.shape.headerSize, by rw [padding]; exact h.shape.padding⟩
  have leafE : LeafInput pro_call.link entered :=
    ⟨q.good, q.image, q.minstret, gholds_lookup (n := 1) _ q.regs rfl, by decide, q.tick⟩
  have argument : gpr entered 10 = some (BitVec.ofNat 64 f) := by
    rw [← hR10]; exact gholds_lookup (n := 10) _ q.regs rfl
  have L := StringLength.string_length_call entered pro_call.link leafE argument h.geometry shapeE
  apply L.weaken (fun _ eq => eq)
  intro after r
  have goodE : VsaOk live e := p.vsaOk h.libraryGood (by decide) (by simp [pro_regs, keysG])
  have goodQ : VsaOk live entered := q.vsaOk_of_present goodE (by decide) (by simp [keysG])
    (fun a ha => by rw [q.memory]; exact goodE.live a ha)
  have goodR : VsaOk live after := r.vsaOk goodQ (by decide) (by simp [StringLength.lengthWrites, keysG])
  have gpE := p.toEffectPost.readOnly_log (live := live) (text := []) (by decide) (by decide)
    h.globalPointer (fun _ hp => nomatch hp)
  have gpQ := (show WritePost [1] [] e pro_call.target (R 10) entered from q.toEffectPost).readOnly_log
    (live := live) (text := []) (by decide) (by decide) gpE (fun _ hp => nomatch hp)
  have gpR := r.toEffectPost.readOnly_log (live := live) (text := []) (by decide) (by decide)
    gpQ (fun _ hp => nomatch hp)
  have frameR (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ StringLength.lengthWrites) :
      gpr after k = gpr entered k := r.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameQ (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1]) : gpr entered k = gpr e k :=
    q.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameP (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [2, 8, 18, 20]) : gpr e k = gpr c k :=
    p.toEffectPost.gpr_frame (by decide) k lo hi out
  have atE (k : Nat) {v : BitVec 64} (hv : lookupG k ((1, pro_call.link) ::
      [(2, R 2 - 48#64), (8, R 12), (10, R 10), (18, R 11), (20, R 10)]) = some v) : gpr entered k = some v :=
    gholds_lookup _ q.regs hv
  refine ⟨⟨r.good, r.image, r.minstret, gholds_lookup (n := 1) _ r.regs rfl, by decide, r.tick⟩,
    goodR, gpR, r.pc, ?_, ?_, r.result, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r.memory]; exact memE
  · exact r.output.trans (q.output.trans p.output)
  · rw [frameR 2 (by decide) (by decide) (by decide), atE 2 rfl, hR2]
  · rw [frameR 8 (by decide) (by decide) (by decide), atE 8 rfl, hR12]
  · rw [frameR 18 (by decide) (by decide) (by decide), atE 18 rfl, hR11]
  · rw [frameR 20 (by decide) (by decide) (by decide), atE 20 rfl, hR10]
  · intro k lo hi out
    simp only [lengthWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [frameR k lo hi (by simp [StringLength.lengthWrites]; omega),
      frameQ k lo hi (by simp; omega), frameP k lo hi (by simp; omega)]

/-- The global pointer survives any run that keeps `gp`. -/
theorem globalPointer_of_gpr {live : Nat → Prop} {before after : Config}
    (keep : gpr after 3 = gpr before 3) (h : ROHolds (vsaModel live) before roR []) :
    ROHolds (vsaModel live) after roR [] := by
  refine ⟨fun q hq => ?_, fun _ hq => nomatch hq⟩
  have old := h.1 q hq
  obtain rfl := List.mem_singleton.1 hq
  change vsaReg after 3 = _
  change vsaReg before 3 = _ at old
  simp only [vsaReg] at old ⊢
  change (gpr after 3).getD 0 = _
  change (gpr before 3).getD 0 = _ at old
  rw [keep]; exact old

/-- The C suffix `ARCH_INTNAT_PRINTF_FORMAT` = `"l"`, in `.rodata`. -/
def suffixAddr : Nat := 0x80055088

theorem suffix_bytes {c : Config} (image : ExecutableImage c) :
    imgM c.σ.mem suffixAddr = 0x6c#8 ∧ imgM c.σ.mem (suffixAddr + 1) = 0#8 := by
  have b0 := image.rodata 7944 (by decide)
  have b1 := image.rodata 7945 (by decide)
  refine ⟨?_, ?_⟩
  · change (c.σ.mem[suffixAddr]?).getD 0 = _
    rw [show suffixAddr = Image.rodataBase + 7944 from rfl, b0]; decide
  · change (c.σ.mem[suffixAddr + 1]?).getD 0 = _
    rw [show suffixAddr + 1 = Image.rodataBase + 7945 from rfl, b1]; decide

/-- The registers `measure` may change. -/
def measureWritten : List Nat := [1, 2, 8, 10, 11, 12, 13, 14, 15, 18, 19, 20]

/-- After both length calls: at the fit check (`0x80010434`) with `s3` the
format's length and `a0` the suffix's. -/
structure Measured (live : Nat → Prop) (sp : BitVec 64) (f buf n : Nat) (before after : Config) : Prop
    extends LeafInput suffix_call.link after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some suffix_call.link
  memory : Vsa.Densify.MemEqv after.σ.mem (writeLog before.σ.mem (proLog (entryRegs before) []))
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  suffixLength : gpr after 10 = some 1#64
  length : gpr after 19 = some (BitVec.ofNat 64 n)
  stack : gpr after 2 = some (sp - 48#64)
  buffer : gpr after 8 = some (BitVec.ofNat 64 buf)
  suffix : gpr after 18 = some 0x80055088#64
  fmt : gpr after 20 = some (BitVec.ofNat 64 f)
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ measureWritten → gpr after k = gpr before k

/-- **Both length calls.** -/
theorem measure {live : Nat → Prop} {ra sp : BitVec 64} {f buf n : Nat} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : MeasureInput live ra sp f buf n c) :
    FnSummary 0x800103fc#64 (fun d => d = c) (Measured live sp f buf n c) := by
  apply summary_bind (measure_length c h) (fun _ d => d.pc)
  intro d dl
  let R := entryRegs d
  have regs : GHolds d.σ (suffix_input R) := holds_entry dl.libraryGood [1, 2, 8, 10, 18, 20] (by decide)
  have S := suffix_fast d R (by rw [show R 1 = pro_call.link from entry_value dl.raReg]; exact dl.toLeafInput) regs
  apply summary_bind S (fun _ p => p.pc)
  intro e p
  have args : GHolds e.σ [(10, R 18)] := holds_project p.regs (by simp [suffix_regs, lookupG])
  have J := call_registers_summary suffix_call_shape suffix_call_decode e (suffix_call_pins p.image) p.good
    p.image p.tick p.minstret _ args (by change KeysOK [10]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have goodE : VsaOk live e := p.vsaOk dl.libraryGood (by decide) (by simp [suffix_regs, keysG])
  have goodQ : VsaOk live entered := q.vsaOk_of_present goodE (by decide) (by simp [keysG])
    (fun a ha => by rw [q.memory]; exact goodE.live a ha)
  have frameQ (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1]) : gpr entered k = gpr e k :=
    q.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameP (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10, 19]) : gpr e k = gpr d k :=
    p.toEffectPost.gpr_frame (by decide) k lo hi out
  have hR18 : R 18 = 0x80055088#64 := entry_value dl.suffix
  have bytes := suffix_bytes q.image
  have string : StrRead entered.σ.mem (List.range' suffixAddr 2) (fun _ => False) entered.σ.mem suffixAddr 1
      (imgM entered.σ.mem) :=
    { win := fun x low high => Or.inl ⟨List.mem_range'_1.2 ⟨low, by omega⟩, rfl⟩
      nz := fun i hi => by rw [show i = 0 by omega, Nat.add_zero, bytes.1]; decide
      nul := bytes.2
      lo := by decide
      hi := by decide
      htif := by decide }
  have readOnly : ROHolds (vsaModel live) entered roR
      (snpText ++ dataOf entered.σ.mem (List.range' suffixAddr 2)) := by
    have gp := globalPointer_of_gpr (live := live) ((frameQ 3 (by decide) (by decide) (by decide)).trans
      ((frameP 3 (by decide) (by decide) (by decide)).trans
        (dl.kept 3 (by decide) (by decide) (by decide)))) h.globalPointer
    refine ⟨gp.1, ?_⟩
    intro r hr
    rcases List.mem_append.1 hr with snp | data
    · change (entered.σ.mem[r.1]?).getD 0 = r.2
      rw [snp_text_loaded q.image r snp]; rfl
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 data
      rfl
  have arg : gpr entered 10 = some (BitVec.ofNat 64 suffixAddr) := by
    rw [show BitVec.ofNat 64 suffixAddr = R 18 from hR18.symm]
    exact gholds_lookup (n := 10) _ q.regs rfl
  have L := strlen_call entered codeLive string goodQ q.image liveImage readOnly arg
    (gholds_lookup (n := 1) _ q.regs rfl) (by decide)
  apply L.weaken (fun _ eq => eq)
  intro after r
  have frameR (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10, 11, 12, 13, 14, 15]) :
      gpr after k = gpr entered k := r.registers k lo hi out
  have back (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1, 10, 11, 12, 13, 14, 15, 19]) :
      gpr after k = gpr d k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [frameR k lo hi (by simp; omega), frameQ k lo hi (by simp; omega), frameP k lo hi (by simp; omega)]
  refine ⟨r.toLeafInput, r.libraryGood, ?_, r.pc, ?_, ?_, r.result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalPointer_of_gpr ((back 3 (by decide) (by decide) (by decide)).trans
      (dl.kept 3 (by decide) (by decide) (by decide))) h.globalPointer
  · intro x
    have m := r.memory x
    have pm : e.σ.mem = d.σ.mem := p.memory
    rw [q.memory, pm, dl.memory] at m
    exact m
  · exact r.output.trans (by simp only [Vsa.Machine.output, q.output, p.output, dl.output])
  · rw [frameR 19 (by decide) (by decide) (by decide), frameQ 19 (by decide) (by decide) (by decide)]
    rw [show gpr e 19 = some (R 10) from gholds_lookup (n := 19) _ p.regs rfl]
    exact congrArg some (entry_value dl.length)
  · rw [back 2 (by decide) (by decide) (by decide), dl.stack]
  · rw [back 8 (by decide) (by decide) (by decide), dl.buffer]
  · rw [back 18 (by decide) (by decide) (by decide), dl.suffix]
  · rw [back 20 (by decide) (by decide) (by decide), dl.fmt]
  · intro k lo hi out
    simp only [measureWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [back k lo hi (by simp; omega), dl.kept k lo hi (by simp [lengthWritten]; omega)]

/-- Every stdio-footprint byte lies below the end of `.bss`. -/
theorem stdioFoot_high {a : Nat} (h : VsaIris.Stdio.stdioFoot a) : a < 0x8007d138 := by
  simp only [VsaIris.Stdio.stdioFoot, VsaIris.Stdio.InRange] at h
  omega

theorem bltu_false_of_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    LeanRV64DExecutable.Functions.zopz0zI_u a b = false := by
  unfold LeanRV64DExecutable.Functions.zopz0zI_u; simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (Int.not_lt.mpr (Int.ofNat_le.mpr h))

/-- The buffer and the format string, as `memmove` needs them. -/
structure BufferInput (f buf n : Nat) : Prop where
  bufLow : 0x80063b90 ≤ buf
  bufHigh : buf + 32 ≤ 0x100000000
  /-- the string, its suffix and conversion, and the terminator fit -/
  fits : n + 2 ≤ 31
  /-- the string is a heap object, above `.bss` -/
  fmtLow : 0x8007d138 ≤ f
  fmtHigh : f + n ≤ 0x100000000
  apart : f + n ≤ buf ∨ buf + 32 ≤ f

/-- The registers `copy` may change. -/
def copyWritten : List Nat := [1, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 28]

/-- After the first `memmove`: the format string is in the buffer. -/
structure Copied (live : Nat → Prop) (sp : BitVec 64) (f buf n : Nat) (before after : Config) : Prop
    extends LeafInput copy_call.link after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some copy_call.link
  copied : ∀ i, i < n → byte after (buf + i) = byte before (f + i)
  rest : ∀ a, a < buf ∨ buf + n ≤ a → byte after a = byte before a
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  buffer : gpr after 8 = some (BitVec.ofNat 64 buf)
  suffixLength : gpr after 9 = some 1#64
  length : gpr after 19 = some (BitVec.ofNat 64 n)
  stack : gpr after 2 = some (sp - 48#64)
  suffix : gpr after 18 = some 0x80055088#64
  fmt : gpr after 20 = some (BitVec.ofNat 64 f)
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ copyWritten → gpr after k = gpr before k

/-- **The fit check and the copy of the format string.** -/
theorem copy {live : Nat → Prop} {sp : BitVec 64} {f buf n : Nat} (c d : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (dm : Measured live sp f buf n c d) (hb : BufferInput f buf n) :
    FnSummary suffix_call.link (fun e => e = d) (Copied live sp f buf n d) := by
  let R := entryRegs d
  have hR10 : R 10 = 1#64 := entry_value dm.suffixLength
  have hR19 : R 19 = BitVec.ofNat 64 n := entry_value dm.length
  have hR8 : R 8 = BitVec.ofNat 64 buf := entry_value dm.buffer
  have hR20 : R 20 = BitVec.ofNat 64 f := entry_value dm.fmt
  have regs : GHolds d.σ (fits_input R) := holds_entry dm.libraryGood [1, 2, 8, 10, 18, 19, 20] (by decide)
  have leaf : LeafInput (R 1) d := by rw [show R 1 = suffix_call.link from entry_value dm.raReg]; exact dm.toLeafInput
  have ok : guardB .BLTU (31#64) (R 19 + R 10 + 1#64) = false := by
    rw [hR19, hR10]
    apply bltu_false_of_le
    have := hb.fits
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have S := fits_fast d R leaf regs ok
  apply summary_bind S (fun _ p => p.pc)
  intro e p
  have goodE : VsaOk live e := p.vsaOk dm.libraryGood (by decide) (by simp [fits_regs, keysG])
  have regsE : GHolds e.σ (copy_input (entryRegs e)) := holds_entry goodE [1, 2, 8, 10, 18, 19, 20] (by decide)
  have frameP (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [14, 15]) : gpr e k = gpr d k :=
    p.toEffectPost.gpr_frame (by decide) k lo hi out
  have leafE : LeafInput (entryRegs e 1) e := by
    rw [show entryRegs e 1 = suffix_call.link from entry_value ((frameP 1 (by decide) (by decide) (by decide)).trans dm.raReg)]
    exact ⟨p.good, p.image, p.minstret, (frameP 1 (by decide) (by decide) (by decide)).trans dm.raReg, by decide, p.tick⟩
  let R' := entryRegs e
  have back (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [14, 15]) {v : BitVec 64} (hv : gpr d k = some v) :
      R' k = v := entry_value ((frameP k lo hi out).trans hv)
  have S2 := copy_fast e R' leafE regsE
  apply summary_bind S2 (fun _ p2 => p2.pc)
  intro e2 p2
  have args : GHolds e2.σ [(10, R' 8), (11, R' 20), (12, R' 19)] :=
    holds_project p2.regs (by simp [copy_regs, lookupG])
  have J := call_registers_summary copy_call_shape copy_call_decode e2 (copy_call_pins p2.image) p2.good
    p2.image p2.tick p2.minstret _ args (by change KeysOK [10, 11, 12]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have goodE2 : VsaOk live e2 := p2.vsaOk goodE (by decide) (by simp [copy_regs, keysG])
  have goodQ : VsaOk live entered := q.vsaOk_of_present goodE2 (by decide) (by simp [keysG])
    (fun a ha => by rw [q.memory]; exact goodE2.live a ha)
  have frameP2 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [9, 10, 11, 12]) : gpr e2 k = gpr e k :=
    p2.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameQ (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1]) : gpr entered k = gpr e2 k :=
    q.toEffectPost.gpr_frame (by decide) k lo hi out
  have memE : entered.σ.mem = d.σ.mem := by
    have pm : e.σ.mem = d.σ.mem := p.memory
    have pm2 : e2.σ.mem = e.σ.mem := p2.memory
    rw [q.memory, pm2, pm]
  have geometry : VsaIris.Sym.MoveGeom 0 buf n buf f n :=
    ⟨hb.bufLow, ⟨Nat.le_refl _, Nat.le_refl _⟩, by have := hb.bufHigh; have := hb.fits; omega,
      by have := hb.fmtLow; omega, hb.fmtHigh, Or.inr (by have := hb.fmtLow; omega),
      by have := hb.fits; rcases hb.apart with h | h <;> omega⟩
  have sourceOut : ∀ a, f ≤ a → a < f + n → ¬ VsaIris.Stdio.stdioFoot a := fun a lo _ foot => by
    have := stdioFoot_high foot; have := hb.fmtLow; omega
  have gpQ := globalPointer_of_gpr (live := live)
    ((frameQ 3 (by decide) (by decide) (by decide)).trans ((frameP2 3 (by decide) (by decide) (by decide)).trans
      (frameP 3 (by decide) (by decide) (by decide)))) dm.globalPointer
  have readOnly : ROHolds (vsaModel live) entered roR (snpText ++ dataOf entered.σ.mem (List.range' f n)) := by
    refine ⟨gpQ.1, ?_⟩
    intro r hr
    rcases List.mem_append.1 hr with snp | data
    · change (entered.σ.mem[r.1]?).getD 0 = r.2
      rw [snp_text_loaded q.image r snp]; rfl
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 data
      rfl
  have h8 : R' 8 = BitVec.ofNat 64 buf := back 8 (by decide) (by decide) (by decide) dm.buffer
  have h20 : R' 20 = BitVec.ofNat 64 f := back 20 (by decide) (by decide) (by decide) dm.fmt
  have h19 : R' 19 = BitVec.ofNat 64 n := back 19 (by decide) (by decide) (by decide) dm.length
  have h10 : R' 10 = 1#64 := back 10 (by decide) (by decide) (by decide) dm.suffixLength
  have M := memmove_call (live := live) entered codeLive geometry sourceOut goodQ q.image liveImage readOnly
    (by rw [← h8]; exact gholds_lookup (n := 10) _ q.regs rfl)
    (by rw [← h20]; exact gholds_lookup (n := 11) _ q.regs rfl)
    (by rw [← h19]; exact gholds_lookup (n := 12) _ q.regs rfl)
    (gholds_lookup (n := 1) _ q.regs rfl) (by decide)
  apply M.weaken (fun _ eq => eq)
  intro after r
  have toD (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ copyWritten) : gpr after k = gpr d k := by
    simp only [copyWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [r.registers k lo hi (by simp [memmoveScratch]; omega) (by simp; omega),
      frameQ k lo hi (by simp; omega), frameP2 k lo hi (by simp; omega), frameP k lo hi (by simp; omega)]
  have byteE (x : Nat) : byte entered x = byte d x := by simp only [byte, memE]
  refine ⟨r.toLeafInput, r.libraryGood, globalPointer_of_gpr (toD 3 (by decide) (by decide) (by decide))
    dm.globalPointer, r.pc, fun i hi => (r.copied i hi).trans (byteE _),
    fun a ha => (r.kept a ha).trans (byteE _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, toD⟩
  · exact r.output.trans (by simp only [Vsa.Machine.output, q.output, p2.output, p.output])
  · rw [toD 8 (by decide) (by decide) (by decide), dm.buffer]
  · rw [r.registers 9 (by decide) (by decide) (by decide) (by decide), frameQ 9 (by decide) (by decide) (by decide),
      show gpr e2 9 = some (R' 10) from gholds_lookup (n := 9) _ p2.regs rfl, h10]
  · rw [toD 19 (by decide) (by decide) (by decide), dm.length]
  · rw [toD 2 (by decide) (by decide) (by decide), dm.stack]
  · rw [toD 18 (by decide) (by decide) (by decide), dm.suffix]
  · rw [toD 20 (by decide) (by decide) (by decide), dm.fmt]

/-- The conversion-byte test of `parse_format` (no `l`/`L`/`n` length
modifier before the conversion), for every byte (one kernel check). -/
theorem plain_guard_all : ∀ k : Fin 256, 34 < (k.val + 180) % 256 →
    guardB .BLTU 34#64 (BitVec.signExtend 64 (Sail.BitVec.extractLsb
      (bytesVal .lbu [BitVec.ofNat 8 k.val] + 18446744073709551540#64) 31 0) &&& 255#64) = true := by
  decide +kernel

theorem plain_guard (b : BitVec 8) (h : 34 < (b.toNat + 180) % 256) :
    guardB .BLTU 34#64 (BitVec.signExtend 64 (Sail.BitVec.extractLsb
      (bytesVal .lbu [b] + 18446744073709551540#64) 31 0) &&& 255#64) = true := by
  have := plain_guard_all ⟨b.toNat, b.isLt⟩ h
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

/-- Buffer addresses from the plain block's register arithmetic. -/
theorem buffer_last {f buf n : Nat} (hb : BufferInput f buf n) (long : 1 ≤ n) :
    BitVec.ofNat 64 buf + (BitVec.ofNat 64 n + 18446744073709551615#64) = BitVec.ofNat 64 (buf + (n - 1)) := by
  have := hb.bufHigh; have := hb.fits
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2:Nat)^64 = 18446744073709551616 from rfl]
  try simp only [BitVec.toNat_ofNat, show (2:Nat)^64 = 18446744073709551616 from rfl]
  rw [Nat.mod_eq_of_lt (a := buf) (by omega), Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

theorem buffer_prev {f buf n : Nat} (hb : BufferInput f buf n) (long : 2 ≤ n) :
    BitVec.ofNat 64 buf + (BitVec.ofNat 64 n + 18446744073709551615#64) + 18446744073709551615#64 =
      BitVec.ofNat 64 (buf + (n - 2)) := by
  have := hb.bufHigh; have := hb.fits
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2:Nat)^64 = 18446744073709551616 from rfl]
  try simp only [BitVec.toNat_ofNat, show (2:Nat)^64 = 18446744073709551616 from rfl]
  rw [Nat.mod_eq_of_lt (a := buf) (by omega), Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

theorem buffer_window {f buf n : Nat} (hb : BufferInput f buf n) (k : Nat) (hk : k < 32) :
    ReadWindow (BitVec.ofNat 64 (buf + k)) 1 := by
  have := hb.bufHigh; have := hb.bufLow
  have e : (BitVec.ofNat 64 (buf + k)).toNat = buf + k := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> rw [e] <;> (try simp only [Layout.sym_tohost]) <;> omega

/-- The registers `append` may change. -/
def appendWritten : List Nat := [1, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 28]

/-- After the second `memmove`: the suffix replaces the conversion byte. -/
structure Appended (live : Nat → Prop) (sp : BitVec 64) (f buf n : Nat) (base before after : Config) : Prop
    extends LeafInput append_call.link after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some append_call.link
  prefixBytes : ∀ i, i + 1 < n → byte after (buf + i) = byte base (f + i)
  suffixByte : byte after (buf + (n - 1)) = 0x6c#8
  rest : ∀ a, a < buf ∨ buf + n ≤ a → byte after a = byte base a
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  conversion : gpr after 8 = some ((byte base (f + (n - 1))).setWidth 64)
  suffixLength : gpr after 9 = some 1#64
  cursor : gpr after 10 = some (BitVec.ofNat 64 (buf + (n - 1)))
  stack : gpr after 2 = some (sp - 48#64)
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ appendWritten → gpr after k = gpr before k

theorem ofNat_toNat_buffer {f buf n : Nat} (hb : BufferInput f buf n) (k : Nat) (hk : k < 32) :
    (BitVec.ofNat 64 (buf + k)).toNat = buf + k := by
  have := hb.bufHigh; exact Nat.mod_eq_of_lt (by omega)

/-- **The conversion check and the copy of the suffix.** -/
theorem append {live : Nat → Prop} {sp : BitVec 64} {f buf n : Nat} (d e : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (dc : Copied live sp f buf n d e) (hb : BufferInput f buf n) (long : 2 ≤ n)
    (prev : 34 < ((byte d (f + (n - 2))).toNat + 180) % 256) :
    FnSummary copy_call.link (fun x => x = e) (Appended live sp f buf n d e) := by
  let R := entryRegs e
  have h8 : R 8 = BitVec.ofNat 64 buf := entry_value dc.buffer
  have h19 : R 19 = BitVec.ofNat 64 n := entry_value dc.length
  have regs : GHolds e.σ (plain_input R) := holds_entry dc.libraryGood [1, 2, 8, 9, 10, 18, 19] (by decide)
  have leaf : LeafInput (R 1) e := by rw [show R 1 = copy_call.link from entry_value dc.raReg]; exact dc.toLeafInput
  have fits := hb.fits
  have prevAddr : R 8 + (R 19 + 18446744073709551615#64) + 18446744073709551615#64 =
      BitVec.ofNat 64 (buf + (n - 2)) := by rw [h8, h19]; exact buffer_prev hb long
  have lastAddr : R 8 + (R 19 + 18446744073709551615#64) = BitVec.ofNat 64 (buf + (n - 1)) := by
    rw [h8, h19]; exact buffer_last hb (by omega)
  have w0 : ReadWindow (R 8 + (R 19 + 18446744073709551615#64) + 18446744073709551615#64) 1 := by
    rw [prevAddr]; exact buffer_window hb _ (by omega)
  have w1 : ReadWindow (R 8 + (R 19 + 18446744073709551615#64)) 1 := by
    rw [lastAddr]; exact buffer_window hb _ (by omega)
  have prevByte : (e.σ.mem[(R 8 + (R 19 + 18446744073709551615#64) + 18446744073709551615#64).toNat]?).getD 0 =
      byte d (f + (n - 2)) := by
    rw [prevAddr, ofNat_toNat_buffer hb _ (by omega), ← StringLength.byte_getD]
    exact dc.copied (n - 2) (by omega)
  have ok : guardB .BLTU (34#64) (BitVec.signExtend 64 (Sail.BitVec.extractLsb (bytesVal .lbu
      ((plain_loads e.σ.mem R).getD 0 []) + 18446744073709551540#64) 31 0) &&& 255#64) = true := by
    simp only [plain_loads, List.getD_cons_zero]
    rw [prevByte]
    exact plain_guard _ prev
  have S := plain_fast e R leaf regs w0 w1 ok
  apply summary_bind S (fun _ p => p.pc)
  intro e1 p
  have good1 : VsaOk live e1 := p.vsaOk dc.libraryGood (by decide) (by simp [plain_regs, keysG])
  have frameP (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [8, 13, 14, 15, 19]) : gpr e1 k = gpr e k :=
    p.toEffectPost.gpr_frame (by decide) k lo hi out
  let R2 := entryRegs e1
  have h15 : R2 15 = BitVec.ofNat 64 (buf + (n - 1)) := by
    have v := gholds_lookup (n := 15) _ p.regs rfl
    rw [show R2 15 = R 8 + (R 19 - 1#64) from entry_value v, ← lastAddr, BitVec.sub_eq_add_neg]; rfl
  have h9 : R2 9 = 1#64 := entry_value ((frameP 9 (by decide) (by decide) (by decide)).trans dc.suffixLength)
  have h18 : R2 18 = 0x80055088#64 := entry_value ((frameP 18 (by decide) (by decide) (by decide)).trans dc.suffix)
  have regs2 : GHolds e1.σ (append_input R2) := holds_entry good1 [1, 2, 8, 9, 10, 15, 18] (by decide)
  have link1 : gpr e1 1 = some copy_call.link := (frameP 1 (by decide) (by decide) (by decide)).trans dc.raReg
  have leaf2 : LeafInput (R2 1) e1 := by
    rw [show R2 1 = copy_call.link from entry_value link1]
    exact ⟨p.good, p.image, p.minstret, link1, by decide, p.tick⟩
  have S2 := append_fast e1 R2 leaf2 regs2
  apply summary_bind S2 (fun _ p2 => p2.pc)
  intro e2 p2
  have args : GHolds e2.σ [(10, R2 15), (11, R2 18), (12, R2 9)] :=
    holds_project p2.regs (by simp [append_regs, lookupG])
  have J := call_registers_summary append_call_shape append_call_decode e2 (append_call_pins p2.image) p2.good
    p2.image p2.tick p2.minstret _ args (by change KeysOK [10, 11, 12]; decide) (by simp [KeysAvoidRa, keysG]) rfl
  apply summary_bind J (fun _ q => q.pc)
  intro entered q
  have good2 : VsaOk live e2 := p2.vsaOk good1 (by decide) (by simp [append_regs, keysG])
  have goodQ : VsaOk live entered := q.vsaOk_of_present good2 (by decide) (by simp [keysG])
    (fun a ha => by rw [q.memory]; exact good2.live a ha)
  have frameP2 (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [10, 11, 12]) : gpr e2 k = gpr e1 k :=
    p2.toEffectPost.gpr_frame (by decide) k lo hi out
  have frameQ (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ [1]) : gpr entered k = gpr e2 k :=
    q.toEffectPost.gpr_frame (by decide) k lo hi out
  have memE : entered.σ.mem = e.σ.mem := by
    have pm : e1.σ.mem = e.σ.mem := p.memory
    have pm2 : e2.σ.mem = e1.σ.mem := p2.memory
    rw [q.memory, pm2, pm]
  have byteE (x : Nat) : byte entered x = byte e x := by simp only [byte, memE]
  have geometry : VsaIris.Sym.MoveGeom 0 (buf + (n - 1)) 1 (buf + (n - 1)) suffixAddr 1 :=
    ⟨by have := hb.bufLow; omega, ⟨Nat.le_refl _, Nat.le_refl _⟩, by have := hb.bufHigh; omega,
      by decide, by decide, Or.inl (by decide), Or.inl (by simp only [suffixAddr]; have := hb.bufLow; omega)⟩
  have sourceOut : ∀ a, suffixAddr ≤ a → a < suffixAddr + 1 → ¬ VsaIris.Stdio.stdioFoot a := fun a _ hi foot => by
    have := stdioFoot_low foot; simp only [suffixAddr] at hi; omega
  have gpQ := globalPointer_of_gpr (live := live)
    ((frameQ 3 (by decide) (by decide) (by decide)).trans ((frameP2 3 (by decide) (by decide) (by decide)).trans
      (frameP 3 (by decide) (by decide) (by decide)))) dc.globalPointer
  have readOnly : ROHolds (vsaModel live) entered roR
      (snpText ++ dataOf entered.σ.mem (List.range' suffixAddr 1)) := by
    refine ⟨gpQ.1, ?_⟩
    intro r hr
    rcases List.mem_append.1 hr with snp | data
    · change (entered.σ.mem[r.1]?).getD 0 = r.2
      rw [snp_text_loaded q.image r snp]; rfl
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 data
      rfl
  have M := memmove_call (live := live) entered codeLive geometry sourceOut goodQ q.image liveImage readOnly
    (by rw [← h15]; exact gholds_lookup (n := 10) _ q.regs rfl)
    (by rw [show BitVec.ofNat 64 suffixAddr = R2 18 from h18.symm]; exact gholds_lookup (n := 11) _ q.regs rfl)
    (by rw [show BitVec.ofNat 64 1 = R2 9 from h9.symm]; exact gholds_lookup (n := 12) _ q.regs rfl)
    (gholds_lookup (n := 1) _ q.regs rfl) (by decide)
  apply M.weaken (fun _ eq => eq)
  intro after r
  have toE (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ appendWritten) : gpr after k = gpr e k := by
    simp only [appendWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [r.registers k lo hi (by simp [memmoveScratch]; omega) (by simp; omega),
      frameQ k lo hi (by simp; omega), frameP2 k lo hi (by simp; omega), frameP k lo hi (by simp; omega)]
  have suffixByte := (suffix_bytes q.image).1
  refine ⟨r.toLeafInput, r.libraryGood, globalPointer_of_gpr (toE 3 (by decide) (by decide) (by decide))
    dc.globalPointer, r.pc, ?_, ?_, ?_, ?_, ?_, ?_, r.result, ?_, ?_⟩
  · intro i hi
    rw [r.kept _ (Or.inl (by omega)), byteE]
    exact dc.copied i (by omega)
  · have c0 := r.copied 0 (by decide)
    rw [Nat.add_zero, Nat.add_zero] at c0
    rw [c0, StringLength.byte_getD]; exact suffixByte
  · intro a ha
    rw [r.kept a (by omega), byteE]
    exact dc.rest a ha
  · exact r.output.trans (by simp only [Vsa.Machine.output, q.output, p2.output, p.output])
  · rw [r.registers 8 (by decide) (by decide) (by decide) (by decide), frameQ 8 (by decide) (by decide) (by decide),
      frameP2 8 (by decide) (by decide) (by decide),
      show gpr e1 8 = _ from gholds_lookup (n := 8) _ p.regs rfl]
    simp only [plain_loads, List.getD_cons_succ, List.getD_cons_zero]
    rw [lastAddr, ofNat_toNat_buffer hb _ (by omega), ← StringLength.byte_getD, dc.copied (n - 1) (by omega)]
    simp only [bytesVal, LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, List.getD_cons_zero, BitVec.zeroExtend_eq_setWidth]
  · rw [toE 9 (by decide) (by decide) (by decide), dc.suffixLength]
  · rw [toE 2 (by decide) (by decide) (by decide), dc.stack]
  · exact toE

/-- The six words parse_format's prologue saved, still in its frame. -/
structure SavedSlots (sp : BitVec 64) (ra s0 s1 s2 s3 s4 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) :
    Prop where
  ra : bytesT m (nativeFrameBase sp 48 + 40) 8 = ra
  s0 : bytesT m (nativeFrameBase sp 48 + 32) 8 = s0
  s1 : bytesT m (nativeFrameBase sp 48 + 24) 8 = s1
  s2 : bytesT m (nativeFrameBase sp 48 + 16) 8 = s2
  s3 : bytesT m (nativeFrameBase sp 48 + 8) 8 = s3
  s4 : bytesT m (nativeFrameBase sp 48) 8 = s4

/-- The registers `finish` may change. -/
def finishWritten : List Nat := [1, 2, 8, 9, 10, 15, 18, 19, 20]

/-- parse_format returned: the conversion byte, the saved registers, and the
terminator after the conversion. -/
structure Finished (live : Nat → Prop) (sp ra s0 s1 s2 s3 s4 : BitVec 64) (buf n : Nat) (conv : BitVec 8)
    (before after : Config) : Prop extends LeafInput ra after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some (conv.setWidth 64)
  conversion : byte after (buf + n) = conv
  nul : byte after (buf + n + 1) = 0#8
  rest : ∀ a, a < buf + n ∨ buf + n + 2 ≤ a → byte after a = byte before a
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  stack : gpr after 2 = some sp
  savedS0 : gpr after 8 = some s0
  savedS1 : gpr after 9 = some s1
  savedS2 : gpr after 18 = some s2
  savedS3 : gpr after 19 = some s3
  savedS4 : gpr after 20 = some s4
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ finishWritten → gpr after k = gpr before k

theorem buffer_succ {f buf n : Nat} (hb : BufferInput f buf n) (k : Nat) (hk : k + 1 < 32) :
    BitVec.ofNat 64 (buf + k) + 1#64 = BitVec.ofNat 64 (buf + (k + 1)) := by
  have := hb.bufHigh
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2:Nat)^64 = 18446744073709551616 from rfl]
  rw [Nat.mod_eq_of_lt (a := buf + k) (by omega), Nat.mod_eq_of_lt (a := 1) (by omega)]
  omega

theorem buffer_byte_window {f buf n : Nat} (hb : BufferInput f buf n) (k : Nat) (hk : k < 32) :
    WriteWindow (BitVec.ofNat 64 (buf + k)) 1 := by
  have := hb.bufHigh; have := hb.bufLow
  have e := ofNat_toNat_buffer hb k hk
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> (try simp only [Layout.sym_tohost]) <;> omega

theorem setWidth_zext (b : BitVec 8) : b.setWidth 64 = LeanRV64DExecutable.zero_extend (m := 64) b := rfl

/-- **The conversion byte, the terminator and the return.** -/
theorem finish {live : Nat → Prop} {sp ra s0 s1 s2 s3 s4 : BitVec 64} {f buf n : Nat} (d e a : Config)
    (da : Appended live sp f buf n d e a) (hb : BufferInput f buf n) (long : 2 ≤ n)
    (frame : NativeFrame sp 48) (above : sp.toNat ≤ buf)
    (slots : SavedSlots sp ra s0 s1 s2 s3 s4 a.σ.mem) (aligned : ra.toNat % 4 = 0) :
    FnSummary append_call.link (fun x => x = a)
      (Finished live sp ra s0 s1 s2 s3 s4 buf n (byte d (f + (n - 1))) a) := by
  let R := entryRegs a
  have fits := hb.fits
  have h2 : R 2 = sp - 48#64 := entry_value da.stack
  have h8 : R 8 = (byte d (f + (n - 1))).setWidth 64 := entry_value da.conversion
  have h9 : R 9 = 1#64 := entry_value da.suffixLength
  have h10 : R 10 = BitVec.ofNat 64 (buf + (n - 1)) := entry_value da.cursor
  have at0 : R 10 + R 9 = BitVec.ofNat 64 (buf + n) := by
    rw [h10, h9, buffer_succ hb _ (by omega)]; congr 2; omega
  have succ : BitVec.ofNat 64 (buf + n) + 1#64 = BitVec.ofNat 64 (buf + (n + 1)) := buffer_succ hb _ (by omega)
  have at1 : R 10 + R 9 + 1#64 = BitVec.ofNat 64 (buf + (n + 1)) := by rw [at0, succ]
  have regs : GHolds a.σ (finish_input R) := holds_entry da.libraryGood [2, 8, 9, 10] (by decide)
  have leaf : LeafInput (R 1) a := by rw [show R 1 = append_call.link from entry_value da.raReg]; exact da.toLeafInput
  have top : nativeFrameBase sp 48 + 48 = sp.toNat := by
    have := frame.lower; unfold nativeFrameBase; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  have slotNat (off : Nat) (h : off + 8 ≤ 48) : (R 2 + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 48 + off := by
    rw [h2, frame_slot frame off (by omega)]; exact frame.slot_nat (by omega)
  have slot0 : (R 2).toNat = nativeFrameBase sp 48 := by
    rw [h2, frame_base frame]; simpa using frame.slot_nat (off := 0) (by decide)
  have win (off : Nat) (h : off + 8 ≤ 48) (al : off % 8 = 0) : ReadWindow (R 2 + BitVec.ofNat 64 off) 8 := by
    rw [h2]; exact (frame_word frame off h al).read
  have win0 : ReadWindow (R 2) 8 := by
    rw [h2, frame_base frame]; simpa using (frame.word (off := 0) (by decide) (by decide)).read
  have bufNat0 : (BitVec.ofNat 64 (buf + n)).toNat = buf + n := ofNat_toNat_buffer hb _ (by omega)
  have bufNat1 : (BitVec.ofNat 64 (buf + (n + 1))).toNat = buf + (n + 1) := ofNat_toNat_buffer hb _ (by omega)
  have apart (x : Nat) (hx : x + 8 ≤ sp.toNat) (loads : List (List (BitVec 8))) :
      OutLRange ((finishLog R loads).take 2) x 8 := by
    simp only [finishLog, List.take, OutLRange]
    rw [at0, succ, bufNat0, bufNat1]
    exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩
  have outside (loads : List (List (BitVec 8))) : ImageOutside (finishLog R loads) := by
    have := hb.bufLow
    constructor <;> simp only [finishLog, OutLRange, Image.textBase, Image.textSize, Image.rodataBase,
      Image.rodataSize] <;> rw [at0, succ, bufNat0, bufNat1] <;> exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩
  have savedRa : bytesVal .ld (read8 a.σ.mem (R 2 + 40#64).toNat) = ra := by
    rw [read8_value, slotNat 40 (by decide)]; exact slots.ra
  have S := finish_fast a ra R leaf regs (by rw [at0]; exact buffer_byte_window hb _ (by omega))
    (by rw [at1]; exact buffer_byte_window hb _ (by omega))
    (win 40 (by decide) (by decide)) (apart _ (by rw [slotNat 40 (by decide)]; omega) _)
    (win 32 (by decide) (by decide)) (apart _ (by rw [slotNat 32 (by decide)]; omega) _)
    (win 24 (by decide) (by decide)) (apart _ (by rw [slotNat 24 (by decide)]; omega) _)
    (win 16 (by decide) (by decide)) (apart _ (by rw [slotNat 16 (by decide)]; omega) _)
    (win 8 (by decide) (by decide)) (apart _ (by rw [slotNat 8 (by decide)]; omega) _)
    win0 (apart _ (by rw [slot0]; omega) _) (outside _) savedRa aligned
  apply S.weaken (fun _ eq => eq)
  intro after p
  have logEq : finishLog R (finish_loads a.σ.mem R) =
      [] ++ (buf + n, 1, R 8) :: [(buf + (n + 1), 1, 0#64)] := by
    simp only [finishLog, List.nil_append]; rw [at0, succ, bufNat0, bufNat1]
  have mem : after.σ.mem = writeLog a.σ.mem ([] ++ (buf + n, 1, R 8) :: [(buf + (n + 1), 1, 0#64)]) := by
    rw [p.memory, logEq]
  have load (k : Nat) (off : Nat) (h : off + 8 ≤ 48) {v : BitVec 64}
      (slot : bytesT a.σ.mem (nativeFrameBase sp 48 + off) 8 = v) :
      bytesVal .ld (read8 a.σ.mem (R 2 + BitVec.ofNat 64 off).toNat) = v := by
    rw [read8_value, slotNat off h]; exact slot
  have pin (k : Nat) {v : BitVec 64} (hv : lookupG k (finish_regs R (finish_loads a.σ.mem R)) = some v) :
      gpr after k = some v := gholds_lookup _ p.regs hv
  refine ⟨⟨p.good, p.image, p.minstret, ?_, aligned, p.tick⟩,
    p.vsaOk da.libraryGood (by decide) (by simp [finish_regs, keysG]),
    p.toEffectPost.readOnly_log (text := []) (by decide) (by decide) da.globalPointer (fun _ hq => nomatch hq),
    p.pc, by rw [p.result, h8], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pin 1 rfl).trans (by simp only [finish_loads, List.getD_cons_zero]; exact congrArg some savedRa)
  · rw [StringLength.byte_getD, mem, pin1_of_writeLog _ _ _ _ _
      (by unfold OutL OutL; exact ⟨Or.inl (by dsimp only; omega), trivial⟩), h8]
    simp only [Option.getD_some, setWidth_zext, Vsa.Sim.sbData_zext]
  · rw [StringLength.byte_getD, mem, show buf + n + 1 = buf + (n + 1) by omega,
      show [] ++ (buf + n, 1, R 8) :: [(buf + (n + 1), 1, 0#64)] =
        [(buf + n, 1, R 8)] ++ (buf + (n + 1), 1, 0#64) :: [] from rfl,
      pin1_of_writeLog _ _ _ _ _ (by simp only [OutL])]
    rfl
  · intro x hx
    simp only [byte]
    rw [mem, bytesT_writeLog_out _ (by
      simp only [OutLRange, List.nil_append]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
  · simp only [Vsa.Machine.output, p.output]
  · rw [pin 2 rfl, h2, BitVec.sub_add_cancel]
  · rw [pin 8 rfl]; simp only [finish_loads, List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg some (load 8 32 (by decide) slots.s0)
  · rw [pin 9 rfl]; simp only [finish_loads, List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg some (load 9 24 (by decide) slots.s1)
  · rw [pin 18 rfl]; simp only [finish_loads, List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg some (load 18 16 (by decide) slots.s2)
  · rw [pin 19 rfl]; simp only [finish_loads, List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg some (load 19 8 (by decide) slots.s3)
  · rw [pin 20 rfl]; simp only [finish_loads, List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg some (by rw [read8_value, slot0]; exact slots.s4)
  · intro k lo hi out
    exact p.toEffectPost.gpr_frame (by decide) k lo hi out

/-- The prologue's saves at their frame addresses. -/
theorem proLog_nat {R : Nat → BitVec 64} {sp : BitVec 64} (stack : R 2 = sp) (frame : NativeFrame sp 48) :
    proLog R [] = [(nativeFrameBase sp 48 + 40, 8, R 1), (nativeFrameBase sp 48 + 32, 8, R 8),
      (nativeFrameBase sp 48 + 16, 8, R 18), (nativeFrameBase sp 48 + 8, 8, R 19),
      (nativeFrameBase sp 48, 8, R 20), (nativeFrameBase sp 48 + 24, 8, R 9)] := by
  have slot (off : Nat) (bound : off + 8 ≤ 48) :
      (sp - 48#64 + BitVec.ofNat 64 off).toNat = nativeFrameBase sp 48 + off := by
    rw [frame_slot frame off (by omega)]; exact frame.slot_nat (by omega)
  have base : (sp - 48#64).toNat = nativeFrameBase sp 48 := by
    rw [frame_base frame]; simpa using frame.slot_nat (off := 0) (by decide)
  simp only [proLog, stack]
  rw [slot 40 (by decide), slot 32 (by decide), slot 16 (by decide), slot 8 (by decide), base, slot 24 (by decide)]

/-- A word written by a log and missed by its later entries reads back. -/
theorem word_log_last (m : Std.ExtHashMap Nat (BitVec 8)) (log1 log2 : List WEntry) (A : Nat) (v : BitVec 64)
    (out : OutLRange log2 A 8) : bytesT (writeLog m (log1 ++ (A, 8, v) :: log2)) A 8 = v := by
  rw [writeLog_append]
  show bytesT (writeLog (writeLog (writeLog m log1) [(A, 8, v)]) log2) A 8 = v
  rw [bytesT_writeLog_out _ out, word_writeLog]

/-- The prologue's saves read back from the frame. -/
theorem proLog_slots {R : Nat → BitVec 64} {sp : BitVec 64} (stack : R 2 = sp) (frame : NativeFrame sp 48)
    (m : Std.ExtHashMap Nat (BitVec 8)) :
    SavedSlots sp (R 1) (R 8) (R 9) (R 18) (R 19) (R 20) (writeLog m (proLog R [])) := by
  have top : nativeFrameBase sp 48 + 48 = sp.toNat := by
    have := frame.lower; unfold nativeFrameBase; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  rw [proLog_nat stack frame]
  have e40 := word_log_last m [] [((nativeFrameBase sp 48) + 32, 8, R 8), ((nativeFrameBase sp 48) + 16, 8, R 18), ((nativeFrameBase sp 48) + 8, 8, R 19),
    ((nativeFrameBase sp 48), 8, R 20), ((nativeFrameBase sp 48) + 24, 8, R 9)] ((nativeFrameBase sp 48) + 40) (R 1) (by simp [OutLRange] <;> omega)
  have e32 := word_log_last m [((nativeFrameBase sp 48) + 40, 8, R 1)] [((nativeFrameBase sp 48) + 16, 8, R 18), ((nativeFrameBase sp 48) + 8, 8, R 19),
    ((nativeFrameBase sp 48), 8, R 20), ((nativeFrameBase sp 48) + 24, 8, R 9)] ((nativeFrameBase sp 48) + 32) (R 8) (by simp [OutLRange] <;> omega)
  have e16 := word_log_last m [((nativeFrameBase sp 48) + 40, 8, R 1), ((nativeFrameBase sp 48) + 32, 8, R 8)] [((nativeFrameBase sp 48) + 8, 8, R 19),
    ((nativeFrameBase sp 48), 8, R 20), ((nativeFrameBase sp 48) + 24, 8, R 9)] ((nativeFrameBase sp 48) + 16) (R 18) (by simp [OutLRange] <;> omega)
  have e8 := word_log_last m [((nativeFrameBase sp 48) + 40, 8, R 1), ((nativeFrameBase sp 48) + 32, 8, R 8), ((nativeFrameBase sp 48) + 16, 8, R 18)]
    [((nativeFrameBase sp 48), 8, R 20), ((nativeFrameBase sp 48) + 24, 8, R 9)] ((nativeFrameBase sp 48) + 8) (R 19) (by simp [OutLRange] <;> omega)
  have e0 := word_log_last m [((nativeFrameBase sp 48) + 40, 8, R 1), ((nativeFrameBase sp 48) + 32, 8, R 8), ((nativeFrameBase sp 48) + 16, 8, R 18), ((nativeFrameBase sp 48) + 8, 8, R 19)]
    [((nativeFrameBase sp 48) + 24, 8, R 9)] (nativeFrameBase sp 48) (R 20) (by simp [OutLRange] <;> omega)
  have e24 := word_log_last m [((nativeFrameBase sp 48) + 40, 8, R 1), ((nativeFrameBase sp 48) + 32, 8, R 8), ((nativeFrameBase sp 48) + 16, 8, R 18), ((nativeFrameBase sp 48) + 8, 8, R 19),
    ((nativeFrameBase sp 48), 8, R 20)] [] ((nativeFrameBase sp 48) + 24) (R 9) trivial
  simp only [List.cons_append, List.nil_append] at e40 e32 e16 e8 e0 e24
  exact ⟨e40, e32, e24, e16, e8, e0⟩

theorem bytesT_one (m : Std.ExtHashMap Nat (BitVec 8)) (x : Nat) : bytesT m x 1 = (m[x]?).getD 0 := by
  simp only [bytesT]
  change (0#0).append ((m[x]?).getD 0) = _
  rw [BitVec.append]
  simp

/-- Every register parse_format may change. -/
def parseWritten : List Nat := [1, 2, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 28]

/-- **parse_format returned** to `ra`: the buffer holds the format string
with the suffix `l` before its conversion character, then a NUL; the
conversion character is in `a0`; callee-saved registers and `sp` are
restored; memory outside the frame and the buffer is unchanged. -/
structure ParseFormatPost (live : Nat → Prop) (ra sp : BitVec 64) (f buf n : Nat) (before after : Config) : Prop
    extends LeafInput ra after where
  libraryGood : VsaOk live after
  globalPointer : ROHolds (vsaModel live) after roR []
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some ((byte before (f + (n - 1))).setWidth 64)
  prefixBytes : ∀ i, i + 1 < n → byte after (buf + i) = byte before (f + i)
  suffixByte : byte after (buf + (n - 1)) = 0x6c#8
  conversion : byte after (buf + n) = byte before (f + (n - 1))
  nul : byte after (buf + n + 1) = 0#8
  rest : ∀ a, (a + 1 ≤ nativeFrameBase sp 48 ∨ sp.toNat ≤ a) → (a < buf ∨ buf + n + 2 ≤ a) →
    byte after a = byte before a
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  stack : gpr after 2 = some sp
  restored : ∀ k ∈ [8, 9, 18, 19, 20], gpr after k = gpr before k
  kept : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ parseWritten → gpr after k = gpr before k

/-- **`parse_format` as a call summary** (`"%d"`-like formats: no `l`/`L`/`n`
modifier before the conversion). The buffer is the caller's, directly above
parse_format's frame. -/
theorem parse_format_call {live : Nat → Prop} {ra sp : BitVec 64} {f buf n : Nat} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (liveImage : ImageLive live)
    (h : MeasureInput live ra sp f buf n c) (hb : BufferInput f buf n) (long : 2 ≤ n)
    (above : sp.toNat ≤ buf) (prev : 34 < ((byte c (f + (n - 2))).toNat + 180) % 256) :
    FnSummary 0x800103fc#64 (fun d => d = c) (ParseFormatPost live ra sp f buf n c) := by
  have lower := h.geometry.lower
  have top : nativeFrameBase sp 48 + 48 = sp.toNat := by
    have := h.frame.lower; unfold nativeFrameBase; simp only [Vsa.Sim.DlHeap.heapEnd] at this; omega
  have hR2 : entryRegs c 2 = sp := entry_value h.stack
  apply summary_bind (measure c codeLive liveImage h) (fun _ d => d.pc)
  intro d dm
  -- outside the frame, the measured memory is the entry memory
  have toC (x : Nat) (hx : x + 1 ≤ nativeFrameBase sp 48 ∨ sp.toNat ≤ x) : byte d x = byte c x := by
    rw [StringLength.byte_getD, StringLength.byte_getD]
    rw [show (d.σ.mem[x]?).getD 0 = ((writeLog c.σ.mem (proLog (entryRegs c) []))[x]?).getD 0 from dm.memory x]
    rw [writeLog_out _ _ _ (by
      rw [proLog_nat hR2 h.frame]; simp [OutL] <;> omega)]
  have strC (i : Nat) (hi : i < n) : byte d (f + i) = byte c (f + i) := toC _ (by
    rcases h.apart with b | b
    · left; have := h.geometry.upper; omega
    · right; omega)
  apply summary_bind (copy c d codeLive liveImage dm hb) (fun _ e => e.pc)
  intro e dc
  apply summary_bind (append d e codeLive liveImage dc hb long (by rw [strC _ (by omega)]; exact prev))
    (fun _ a => a.pc)
  intro a da
  have slotsC := proLog_slots hR2 h.frame c.σ.mem
  have slotA (off : Nat) (bound : off + 8 ≤ 48) :
      bytesT a.σ.mem (nativeFrameBase sp 48 + off) 8 =
        bytesT (writeLog c.σ.mem (proLog (entryRegs c) [])) (nativeFrameBase sp 48 + off) 8 := by
    apply Reloc.bytesT_congr
    intro j hj
    rw [bytesT_one, bytesT_one]
    rw [← StringLength.byte_getD, da.rest _ (Or.inl (by omega)), StringLength.byte_getD]
    exact dm.memory _
  have slots : SavedSlots sp ra (entryRegs c 8) (entryRegs c 9) (entryRegs c 18) (entryRegs c 19)
      (entryRegs c 20) a.σ.mem :=
    ⟨by rw [slotA 40 (by decide), slotsC.ra]; exact entry_value h.raReg,
      by rw [slotA 32 (by decide)]; exact slotsC.s0, by rw [slotA 24 (by decide)]; exact slotsC.s1,
      by rw [slotA 16 (by decide)]; exact slotsC.s2, by rw [slotA 8 (by decide)]; exact slotsC.s3,
      by simpa using (slotA 0 (by decide)).trans slotsC.s4⟩
  apply (finish d e a da hb long h.frame above slots h.aligned).weaken (fun _ eq => eq)
  intro after fin
  have present (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) : gpr c k = some (entryRegs c k) :=
    gpr_getD (h.libraryGood.gpr k lo hi)
  have keptAll (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 31) (out : k ∉ parseWritten) : gpr after k = gpr c k := by
    simp only [parseWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    rw [fin.kept k lo hi (by simp [finishWritten]; omega), da.kept k lo hi (by simp [appendWritten]; omega),
      dc.kept k lo hi (by simp [copyWritten]; omega), dm.kept k lo hi (by simp [measureWritten]; omega)]
  refine ⟨fin.toLeafInput, fin.libraryGood, fin.globalPointer, fin.pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    keptAll⟩
  · rw [fin.result, strC _ (by omega)]
  · intro i hi
    rw [fin.rest _ (Or.inl (by omega)), da.prefixBytes i hi, strC i (by omega)]
  · rw [fin.rest _ (Or.inl (by omega)), da.suffixByte]
  · rw [fin.conversion, strC _ (by omega)]
  · exact fin.nul
  · intro x frameOut bufOut
    rw [fin.rest _ (by omega), da.rest _ (by omega), toC x frameOut]
  · exact fin.output.trans (da.output.trans (dc.output.trans dm.output))
  · exact fin.stack
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [fin.savedS0, present 8 (by decide) (by decide)]
    · rw [fin.savedS1, present 9 (by decide) (by decide)]
    · rw [fin.savedS2, present 18 (by decide) (by decide)]
    · rw [fin.savedS3, present 19 (by decide) (by decide)]
    · rw [fin.savedS4, present 20 (by decide) (by decide)]

end OCaml.Vm.Primitives.Format.ParseFormat
