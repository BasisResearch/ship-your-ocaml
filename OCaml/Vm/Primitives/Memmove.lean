import OCaml.Vm.Primitives.LibraryStrlen
import VsaIris.Vsa.SnpMove
import VsaIris.Vsa.LibraryStdioFoot
import OCaml.Vm.Boot.Startup.LibraryText
import Vsa.Densify.Transport

/-!
# newlib `memmove` as a machine summary

The retargeted library proof `memmove_nw` (`VsaIris/Vsa/SnpMove.lean`, at
ocamlrun's `memmove`, `0x80042644`) covers the non-overlapping copy of `len`
bytes from `src` to `d` (`MoveGeom.disj`). It is bridged here to the
function-summary API exactly as `LibraryStrlen` bridges `strlen_nw`: the
copied bytes equal the source image, every other owned byte keeps its value,
`a0` still holds the destination, and every register outside memmove's
scratch set is kept.
-/

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The registers `memmove` may clobber (`MMFrame`). -/
def memmoveScratch : List Nat := [6, 11, 12, 13, 14, 15, 16, 17, 28]

/-- `memmove` returns to its caller with the destination in `a0`, the copy
done, the rest of its owned bytes unchanged, and its non-scratch registers. -/
structure MemmoveResult (S : Nat → Prop) (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem)
    (d src len : Nat) (g : Nat → BitVec 8) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = R 1
  result : rv 10 = R 10
  registers : ∀ r ∈ nRegs, r ≠ VsaIris.PC → r ∉ memmoveScratch → rv r = R r
  copied : ∀ i, i < len → mv (d + i) = g (src + i)
  rest : ∀ a, S a → (a < d ∨ d + len ≤ a) → mv a = imgM Mt a

/-- Close the landed memmove continuation with its concrete return facts. -/
theorem memmove_symbolic {live Dt DA s dst n} (codeLive : ∀ p ∈ snpText, live p.1)
    (d src len : Nat) (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem)
    (geometry : MoveGeom s dst n d src len)
    (destination : R 10 = BitVec.ofNat 64 d) (source : R 11 = BitVec.ofNat 64 src)
    (length : R 12 = BitVec.ofNat 64 len) (aligned : (R 1).toNat % 4 = 0)
    (window : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g) :
    SnpW live Dt DA (snpS s dst n) (MemmoveResult (snpS s dst n) R Mt d src len g) 0x80042644#64 R Mt := by
  apply memmove_nw codeLive d src len g R Mt geometry destination source length aligned window
  intro R' Mt' frame copied
  apply swp_done
  intro rv mv observed
  have kept : ∀ r ∈ nRegs, r ≠ VsaIris.PC → r ∉ memmoveScratch → rv r = R r := by
    intro r hr ne out
    simp only [memmoveScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at out
    obtain ⟨h6, h11, h12, h13, h14, h15, h16, h17, h28⟩ := out
    exact (observed.regs r hr ne).trans (frame r h11 h12 h13 h14 h15 h16 h17 h6 h28)
  have inside : ∀ i, i < len → snpS s dst n (d + i) := fun i hi => by
    have := geometry.d_in
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  exact ⟨observed.pc, kept 10 (by decide) (by decide) (by decide),
    kept,
    fun i hi => (observed.img _ (inside i hi)).trans (copied.done i hi),
    fun a owned outside => (observed.img a owned).trans (copied.rest a outside)⟩

/-- **Whole-machine `memmove` summary**, reusing the retargeted library proof. -/
theorem memmove_summary {live Dt DA s dst n} (d src len : Nat) (g : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Vsa.MemRepr.Mem) (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1) (geometry : MoveGeom s dst n d src len)
    (destination : R 10 = BitVec.ofNat 64 d) (source : R 11 = BitVec.ofNat 64 src)
    (length : R 12 = BitVec.ofNat 64 len) (aligned : (R 1).toNat % 4 = 0)
    (window : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g)
    (separate : LocalSeparation roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n))
    (input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs (snpS s dst n) R Mt c) :
    FnSummary 0x80042644#64 (fun e => e = c)
      (LocalPost live roR (snpText ++ dataOf Dt DA) nRegs (snpS s dst n)
        (MemmoveResult (snpS s dst n) R Mt d src len g) c) :=
  symbolic_summary c separate input
    (memmove_symbolic codeLive d src len g R Mt geometry destination source length aligned window)

/-! ## The ABI wrapper -/

/-- The snprintf context with an empty stack window and the destination as
the owned window: only the stdio footprint and `[d, d + len)`. -/
abbrev moveOwned (d len : Nat) : Nat → Prop := snpS 0 d len

/-- memmove's library code lies in `.text`, below `.rodata`. -/
theorem snpText_below : ∀ p ∈ snpText, p.1 < 0x80053180 := by
  apply forall_piecesText (P := fun a _ => a < 0x80053180)
  intro q hq a ha
  simp only [snpPieces, List.mem_singleton] at hq
  subst hq
  obtain ⟨r, hr, -, high⟩ := inRangesB_iff.1 ha
  have bounds : ∀ r ∈ snpCodeRanges, r.2 ≤ 0x80053180 := by decide
  have := bounds r hr
  omega

/-- Every stdio-footprint byte lies at or above `0x800643a0`. -/
theorem stdioFoot_low {a : Nat} (h : VsaIris.Stdio.stdioFoot a) : 0x800643a0 ≤ a := by
  simp only [VsaIris.Stdio.stdioFoot, VsaIris.Stdio.InRange] at h
  omega

/-- The owned window misses the program image. -/
theorem moveOwned_image {d len : Nat} (low : 0x80063b90 ≤ d) : ImageSeparate (moveOwned d len) := by
  constructor <;> intro i hi owned <;>
    simp only [moveOwned, snpS, snpNeed, Image.textBase, Image.textSize, Image.rodataBase,
      Image.rodataSize] at hi owned <;>
    rcases owned with ⟨foot, -⟩ | ⟨lo, hi'⟩ | ⟨lo, hi'⟩ <;>
    first | (have := stdioFoot_low foot; omega) | omega

/-- **memmove at a caller's registers.** -/
structure MemmoveCallPost (live : Nat → Prop) (ra : BitVec 64) (d src len : Nat)
    (before after : Config) : Prop extends LeafInput ra after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some (BitVec.ofNat 64 d)
  copied : ∀ i, i < len → byte after (d + i) = byte before (src + i)
  kept : ∀ a, a < d ∨ d + len ≤ a → byte after a = byte before a
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ memmoveScratch → n ∉ [10] → gpr after n = gpr before n

/-- **memmove from any caller**: the source is read in the caller's memory
(`DA` = its addresses), the destination is the only owned window. -/
theorem memmove_call {live : Nat → Prop} {d src len : Nat} {ra : BitVec 64} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1)
    (geometry : MoveGeom 0 d len d src len)
    (sourceOut : ∀ a, src ≤ a → a < src + len → ¬ VsaIris.Stdio.stdioFoot a)
    (good : VsaOk live c) (image : ExecutableImage c) (liveImage : ImageLive live)
    (readOnly : ROHolds (vsaModel live) c roR (snpText ++ dataOf c.σ.mem (List.range' src len)))
    (destination : gpr c 10 = some (BitVec.ofNat 64 d)) (source : gpr c 11 = some (BitVec.ofNat 64 src))
    (length : gpr c 12 = some (BitVec.ofNat 64 len)) (returnAddress : gpr c 1 = some ra)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80042644#64 (fun e => e = c) (MemmoveCallPost live ra d src len c) := by
  let R := (vsaModel live).reg c
  have ret : R 1 = ra := by change (gpr c 1).getD 0 = ra; rw [returnAddress]; rfl
  have dst : R 10 = BitVec.ofNat 64 d := by change (gpr c 10).getD 0 = _; rw [destination]; rfl
  have srcR : R 11 = BitVec.ofNat 64 src := by change (gpr c 11).getD 0 = _; rw [source]; rfl
  have lenR : R 12 = BitVec.ofNat 64 len := by change (gpr c 12).getD 0 = _; rw [length]; rfl
  have align : (R 1).toNat % 4 = 0 := by rw [ret]; exact aligned
  have dLow := geometry.d_lo
  have disj := geometry.disj
  have window : ReadWin c.σ.mem (List.range' src len) (moveOwned d len) c.σ.mem src (src + len)
      (imgM c.σ.mem) := fun a lo hi => .inl ⟨List.mem_range'_1.2 ⟨lo, by omega⟩, rfl⟩
  have input : SymbolicInput live (snpText ++ dataOf c.σ.mem (List.range' src len)) nRegs
      (moveOwned d len) R c.σ.mem c :=
    ⟨good, readOnly, fun _ _ _ => rfl, fun _ _ => rfl⟩
  have separate : LocalSeparation roR (snpText ++ dataOf c.σ.mem (List.range' src len)) nRegs
      (moveOwned d len) := by
    refine ⟨by decide, fun p hp owned => ?_⟩
    rcases List.mem_append.1 hp with code | data
    · have := snpText_below p code
      rcases owned with ⟨foot, -⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
      · have := stdioFoot_low foot; omega
      · simp only [snpNeed] at lo hi; omega
      · omega
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 data
      have inside := List.mem_range'_1.1 ha
      rcases owned with ⟨foot, -⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
      · exact sourceOut a inside.1 (by omega) foot
      · simp only [snpNeed] at lo hi; omega
      · dsimp only at lo hi; omega
  apply (memmove_summary d src len (imgM c.σ.mem) R c.σ.mem c codeLive geometry
    dst srcR lenR align window separate input).weaken
    (fun _ h => h)
  intro after post
  have memory : ∀ a, a < d ∨ d + len ≤ a → (vsaModel live).mem after a = (vsaModel live).mem c a := by
    intro a out
    by_cases owned : moveOwned d len a
    · exact post.result.rest a owned out
    · exact post.memory a owned
  have leafImage := image_local image post.good liveImage (moveOwned_image dLow) post.memory
  refine ⟨⟨post.good.good, leafImage, post.good.good.minstret,
      library_gpr post.good (by decide) (by decide)
        ((post.result.registers 1 (by decide) (by decide) (by decide)).trans ret),
      aligned, post.good.tick⟩,
    post.good, library_pc post.good (post.result.pc.trans ret),
    library_gpr post.good (by decide) (by decide) (post.result.result.trans dst),
    fun i hi => by rw [byte_total, byte_total]; exact post.result.copied i hi,
    fun a out => by rw [byte_total, byte_total]; exact memory a out,
    post.output, ?_⟩
  intro n lower upper scratch notResult
  apply library_register_frame good post.good lower upper
  by_cases owned : n ∈ nRegs
  · exact post.result.registers n owned (by change n ≠ 32; omega) scratch
  · exact post.registers n owned

/-! ## memmove from a leaf call with the library's register facts -/

/-- RAM: the bytes the library proofs read and write. -/
def ramLive (a : Nat) : Prop :=
  Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Densify.ramBase + Vsa.Densify.ramSize

theorem ramLive_image : ImageLive ramLive := by
  constructor <;> intro i hi <;>
    simp only [ramLive, Vsa.Densify.ramBase, Vsa.Densify.ramSize,
      Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] at * <;> omega

theorem snpText_ram : ∀ p ∈ snpText, ramLive p.1 := by
  apply forall_piecesText (P := fun a _ => ramLive a)
  intro q hq a ha
  simp only [snpPieces, List.mem_singleton] at hq
  subst hq
  obtain ⟨r, hr, low, high⟩ := inRangesB_iff.1 ha
  have bounds : ∀ r ∈ snpCodeRanges, 0x80000000 ≤ r.1 ∧ r.2 ≤ 0x80053180 := by decide
  have := bounds r hr
  simp only [ramLive, Vsa.Densify.ramBase, Vsa.Densify.ramSize]
  omega

/-- **The machine facts a library call needs beyond `LeafInput`**: every
integer register present, RAM present, the global pointer, an idle HTIF
payload. -/
structure LibraryReady (c : Config) : Prop where
  gprs : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome
  ram : ∀ a, ramLive a → (c.σ.mem[a]?).isSome
  gp : gpr c 3 = some gpV
  htifIdle : c.σ.regs.get? LeanRV64DExecutable.Register.htif_payload_writes = some 0#4

/-- **memmove from a leaf call**: the destination is outside the stdio
footprint and the program image, and does not overlap the source. -/
theorem memmove_leaf {d src len : Nat} {ra : BitVec 64} (c : Config)
    (leaf : LeafInput ra c) (ready : LibraryReady c)
    (geometry : MoveGeom 0 d len d src len)
    (sourceOut : ∀ a, src ≤ a → a < src + len → ¬ VsaIris.Stdio.stdioFoot a)
    (destination : gpr c 10 = some (BitVec.ofNat 64 d)) (source : gpr c 11 = some (BitVec.ofNat 64 src))
    (length : gpr c 12 = some (BitVec.ofNat 64 len)) :
    FnSummary 0x80042644#64 (fun e => e = c) (MemmoveCallPost ramLive ra d src len c) := by
  have code := OCaml.Vm.Boot.Startup.snp_text_loaded leaf.image
  refine memmove_call c snpText_ram geometry sourceOut
    ⟨leaf.good, leaf.tick, ready.gprs, ready.ram, ready.htifIdle⟩ leaf.image ramLive_image
    ⟨fun p hp => ?_, fun p hp => ?_⟩ destination source length leaf.raReg leaf.aligned
  · rw [List.mem_singleton.1 hp]
    change vsaReg c 3 = gpV
    simp only [vsaReg, show ((3 : Nat) = VsaIris.PC) = False from by decide, ite_false]
    change (gpr c 3).getD 0 = gpV
    rw [ready.gp]; rfl
  · rcases List.mem_append.1 hp with text | data
    · change (c.σ.mem[p.1]?).getD 0 = p.2
      rw [code p text]; rfl
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 data
      rfl

end OCaml.Vm.Primitives
