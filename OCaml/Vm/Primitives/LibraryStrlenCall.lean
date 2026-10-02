import OCaml.Vm.Primitives.LibraryStrlen

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- A read-only string certificate does not depend on the mutable image. -/
theorem strlen_readOnly_memory {Dt DA Mt a len g}
    (h : StrRead Dt DA (fun _ => False) Mt a len g) (Mt' : Vsa.MemRepr.Mem) :
    StrRead Dt DA (fun _ => False) Mt' a len g := by
  refine ⟨?_, h.nz, h.nul, h.lo, h.hi, h.htif⟩
  intro x low high
  rcases h.win x low high with fixed | impossible
  · exact Or.inl fixed
  · exact impossible.1.elim

/-- ABI form of strlen, exposing total memory equality and the preserved
registers needed by generated callers. -/
structure StrlenCallPost (live : Nat → Prop) (ra : BitVec 64) (len : Nat)
    (before after : Config) : Prop extends LeafInput ra after where
  libraryGood : VsaOk live after
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some (BitVec.ofNat 64 len)
  memory : Vsa.Densify.MemEqv after.σ.mem before.σ.mem
  output : Vsa.Machine.output after.σ = Vsa.Machine.output before.σ
  registers : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [10, 11, 12, 13, 14, 15] → gpr after n = gpr before n

/-- A static read-only C-string certificate instantiates the symbolic reader
at the caller's actual register observations. No intermediate execution is
assumed: this consumes the already-proved library function summary. -/
theorem strlen_call {live Dt DA a len g ra} (c : Config)
    (codeLive : ∀ p ∈ snpText, live p.1)
    (string : StrRead Dt DA (fun _ => False) c.σ.mem a len g)
    (good : VsaOk live c) (image : ExecutableImage c) (liveImage : ImageLive live)
    (readOnly : ROHolds (vsaModel live) c roR (snpText ++ dataOf Dt DA))
    (argument : gpr c 10 = some (BitVec.ofNat 64 a)) (returnAddress : gpr c 1 = some ra)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80042970#64 (fun d => d = c) (StrlenCallPost live ra len c) := by
  let R := (vsaModel live).reg c
  have ret : R 1 = ra := by
    change (gpr c 1).getD 0 = ra
    rw [returnAddress]; rfl
  have arg : R 10 = BitVec.ofNat 64 a := by
    change (gpr c 10).getD 0 = _
    rw [argument]; rfl
  have align : (R 1).toNat % 4 = 0 := by rw [ret]; exact aligned
  have input : SymbolicInput live (snpText ++ dataOf Dt DA) nRegs (fun _ => False) R c.σ.mem c :=
    ⟨good, readOnly, fun _ _ _ => rfl, fun _ h => h.elim⟩
  have separate : LocalSeparation roR (snpText ++ dataOf Dt DA) nRegs (fun _ => False) :=
    ⟨by decide, fun _ _ h => h⟩
  apply (strlen_summary R c codeLive string arg align separate input).weaken (fun _ h => h)
  intro after post
  have leaf := strlen_leaf input image liveImage align post
  rw [ret] at leaf
  refine ⟨leaf, post.good, library_pc post.good (post.result.pc.trans ret),
    strlen_result post, strlen_memory input post, post.output, ?_⟩
  intro n lower upper untouched
  apply library_register_frame good post.good lower upper
  by_cases owned : n ∈ nRegs
  · apply post.result.registers n owned (by change n ≠ 32; omega)
    simp only [List.mem_cons, List.mem_singleton] at untouched
    omega
  · exact post.registers n owned

end OCaml.Vm.Primitives
