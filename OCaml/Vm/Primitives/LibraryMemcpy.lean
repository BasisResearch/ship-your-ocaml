import OCaml.Vm.Primitives.LibraryFrame
import VsaIris.Vsa.MemcpyLoops

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim VsaIris VsaIris.Inst VsaIris.Memcpy LeanRV64DExecutable

/-- Named view of the upstream copy result, destructured once at the bridge. -/
structure CopyResult (dst ra : BitVec 64) (n source : Nat) (img : Nat → BitVec 8)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = ra
  raReg : rv 1 = ra
  result : rv 10 = dst
  bytes : ∀ k, k < n → mv (dst.toNat + k) = img (source + k)

theorem copyResult_of_library {dst ra n source img rv mv}
    (h : mQ dst ra n source img rv mv) : CopyResult dst ra n source img rv mv :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Full memcpy ABI/result and observational frame. -/
structure MemcpyPost (live : Nat → Prop) (dst src ra : BitVec 64) (n : Nat)
    (img : Nat → BitVec 8) (before after : Config) : Prop
    extends LeafInput ra after where
  observations : LocalFrame live [] (mText ++ srcText src.toNat n img) mRegs
    (VsaIris.InExt (dst.toNat, n)) before after
  pc : OCaml.Vm.pcOf after = some ra
  result : gpr after 10 = some dst
  bytes : ∀ k, k < n → byte after (dst.toNat + k) = img (src.toNat + k)

/-- The complete upstream alignment/bulk/word/byte proof as a machine summary. -/
theorem memcpy_summary {live dst src ra n img} (c : Config)
    (codeLive : ∀ p ∈ mText, live p.1) (geometry : Geo dst src ra n)
    (good : VsaOk live c) (image : ExecutableImage c) (liveImage : ImageLive live)
    (outside : ImageSeparate (VsaIris.InExt (dst.toNat, n)))
    (separate : LocalSeparation [] (mText ++ srcText src.toNat n img) mRegs (VsaIris.InExt (dst.toNat, n)))
    (readOnly : ROHolds (vsaModel live) c [] (mText ++ srcText src.toNat n img))
    (returnAddress : (vsaModel live).reg c 1 = ra)
    (destination : (vsaModel live).reg c 10 = dst)
    (source : (vsaModel live).reg c 11 = src)
    (length : (vsaModel live).reg c 12 = BitVec.ofNat 64 n) :
    FnSummary 0x80042848#64 (fun d => d = c) (MemcpyPost live dst src ra n img c) := by
  constructor
  rintro before ⟨pc, rfl⟩
  have parked : (vsaModel live).reg before VsaIris.PC = 0x80042848#64 := by
    change (before.σ.regs.get? Register.PC).getD 0 = _
    rw [pc]
    rfl
  obtain ⟨bound, certificate⟩ := memcpyLocalRun codeLive geometry
    ((vsaModel live).reg before) before.σ.mem parked returnAddress destination source length
  obtain ⟨after, run, post⟩ := localRun_triple before separate good readOnly certificate before rfl
  have result := copyResult_of_library post.result
  have leaf : LeafInput ra after :=
    ⟨post.good.good, image_local image post.good liveImage outside post.memory,
      post.good.good.minstret, library_gpr post.good (by decide) (by decide) result.raReg,
      geometry.ral, post.good.tick⟩
  refine ⟨after, run, ?_⟩
  exact { leaf with
    observations := post.toLocalFrame
    pc := library_pc post.good result.pc
    result := library_gpr post.good (by decide) (by decide) result.result
    bytes := fun k hk => by rw [byte_total]; exact result.bytes k hk }

end OCaml.Vm.Primitives
