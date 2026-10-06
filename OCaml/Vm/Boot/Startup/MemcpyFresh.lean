import OCaml.Vm.Boot.Startup.BlockReady
import OCaml.Vm.Boot.Startup.ReadyPerm
import OCaml.Vm.Boot.Startup.LibraryText
import OCaml.Vm.Primitives.LibraryMemcpy
import OCaml.Vm.Primitives.StringCopyFinish
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.Sym VsaIris.VsaHeap VsaIris.MallocFast
  VsaIris.Memcpy OCaml.Vm.Primitives

theorem memcpy_text_live : ∀ p ∈ mText, startupLive p.1 := by
  intro p hp
  obtain ⟨⟨b, k⟩, member, rfl⟩ := List.mem_map.1 hp
  have get := List.mem_zipIdx_iff_getElem?.1 member
  simp only at get
  have bound : k < memcpyCode.length := by
    rcases Nat.lt_or_ge k memcpyCode.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at get
      cases get
  have length : memcpyCode.length = 296 := by decide +kernel
  change Vsa.Densify.ramBase ≤ memcpyBase + k ∧ memcpyBase + k < Vsa.Densify.ramBase + Vsa.Densify.ramSize
  unfold Vsa.Densify.ramBase Vsa.Densify.ramSize memcpyBase
  omega

theorem memcpy_text_low {p : Nat × BitVec 8} (hp : p ∈ mText) : p.1 < heapStart := by
  obtain ⟨⟨b, k⟩, member, rfl⟩ := List.mem_map.1 hp
  have get := List.mem_zipIdx_iff_getElem?.1 member
  simp only at get
  have bound : k < memcpyCode.length := by
    rcases Nat.lt_or_ge k memcpyCode.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at get
      cases get
  have length : memcpyCode.length = 296 := by decide +kernel
  change memcpyBase + k < heapStart
  unfold memcpyBase heapStart
  omega


/-- A finished `memcpy(p, src, n)` into the live block `(p, n)`. -/
structure MemcpyFreshDone (H : List (Nat × Nat)) (capacity : Nat) (sp ra p src : BitVec 64) (n : Nat)
    (before after : Config) : Prop where
  ready : RuntimeReady H capacity sp ra after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some p
  bytes : ∀ k, k < n → (after.σ.mem[p.toNat + k]?).getD 0 = (before.σ.mem[src.toNat + k]?).getD 0
  kept : ∀ x, ¬ InExt (p.toNat, n) x → (after.σ.mem[x]?).getD 0 = (before.σ.mem[x]?).getD 0
  registers : ∀ k, 1 ≤ k → k ≤ 31 → k ∉ mRegs → gprGet after.σ k = gprGet before.σ k

/-- `memcpy(p, src, n)` into the first `n` bytes of a live block `(p, m)` from
a source outside them. -/
theorem memcpy_fresh (c : Config) (H : List (Nat × Nat)) (capacity : Nat) (sp ra p src : BitVec 64) (n m : Nat)
    (ready : RuntimeReady H capacity sp ra c) (member : (p.toNat, m) ∈ H) (fits : n ≤ m)
    (regs : GHolds c.σ [(10, p), (11, src), (12, BitVec.ofNat 64 n)])
    (apart : ∀ k, k < n → ¬ InExt (p.toNat, n) (src.toNat + k))
    (sourceLow : 0x80000000 ≤ src.toNat) (sourceHigh : src.toNat + n ≤ 0x100000000)
    (sourceHtif : src.toNat + n ≤ Layout.sym_tohost ∨ Layout.sym_tohost + 16 ≤ src.toNat) :
    FnSummary 0x80042848#64 (fun d => d = c) (MemcpyFreshDone H capacity sp ra p src n c) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  have bounds := ready.block_bounds member
  have geometry : Geo p src ra n :=
    { dlo := by have : 0x80000000 ≤ heapStart := by decide
                omega
      dhi := by have : heapEnd ≤ 0x100000000 := by decide
                have := bounds.2
                omega
      dhtif := by have : Layout.sym_tohost + 16 ≤ heapStart := by decide
                  omega
      slo := sourceLow
      shi := sourceHigh
      shtif := sourceHtif
      ral := ready.aligned }
  have imageSep : ImageSeparate (InExt (p.toNat, n)) := by
    have image : Image.textBase + Image.textSize ≤ heapStart ∧ Image.rodataBase + Image.rodataSize ≤ heapStart := by
      decide
    constructor <;> intro i hi inside <;> unfold InExt at inside <;> omega
  have separate : LocalSeparation [] (mText ++ srcText src.toNat n (imgM c.σ.mem)) mRegs (InExt (p.toNat, n)) := by
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with code | source
    · have := memcpy_text_low code
      intro inside
      unfold InExt at inside
      omega
    · obtain ⟨lo, hi, -⟩ := mem_srcText source
      have := apart (x.1 - src.toNat) (by omega)
      rwa [show src.toNat + (x.1 - src.toNat) = x.1 by omega] at this
  have readOnly : ROHolds (vsaModel startupLive) c [] (mText ++ srcText src.toNat n (imgM c.σ.mem)) := by
    refine ⟨(fun _ h => nomatch h), ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with code | source
    · change (c.σ.mem[x.1]?).getD 0 = x.2
      rw [memcpy_text_loaded ready.image x code]; rfl
    · obtain ⟨-, -, value⟩ := mem_srcText source
      rw [value]; rfl
  obtain ⟨d, run, D⟩ := (memcpy_summary c memcpy_text_live geometry ready.platform ready.image startup_image_live
    imageSep separate readOnly (observed_register (by decide) ready.raReg)
    (observed_register (by decide) (gholds_lookup (n := 10) _ regs (by rfl)))
    (observed_register (by decide) (gholds_lookup (n := 11) _ regs (by rfl)))
    (observed_register (by decide) (gholds_lookup (n := 12) _ regs (by rfl)))).run c ⟨pc, rfl⟩
  have regD (k : Nat) (lower : 1 ≤ k) (upper : k ≤ 31) (unwritten : k ∉ mRegs) : gprGet d.σ k = gprGet c.σ k :=
    library_register_frame ready.platform D.observations.good lower upper (D.observations.registers k unwritten)
  have stackD := (regD 2 (by decide) (by decide) (by decide)).trans ready.stack
  refine ⟨d, run, {
    ready := ready.of_block_frame (n := m) { D.observations with
      memory := fun a out => D.observations.memory a (fun inside => out (by unfold InExt at *; omega)) }
      (by decide) D.toLeafInput stackD member bounds.1
    pc := D.pc
    result := D.result
    bytes := fun k hk => by
      have copied := D.bytes k hk
      rw [byte_total] at copied
      exact copied
    kept := fun x out => D.observations.memory x out
    registers := regD }⟩
end OCaml.Vm.Boot.Startup
