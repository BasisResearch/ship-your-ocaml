import OCaml.Vm.Boot.Startup.AttemptSearch
import OCaml.Vm.Boot.Startup.AttemptOpenCalls
import OCaml.Vm.Boot.Startup.GcMessageQuiet
import OCaml.Vm.Boot.Startup.StatFree
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast
  OCaml.Vm.Primitives

theorem SearchName.cbytes {m : Vsa.MemRepr.Mem} {p : BitVec 64} {len : Nat} (h : SearchName m p len) :
    CBytes m p.toNat len := by
  rcases h with plain | rooted
  · exact plain.bytes
  · exact rooted.bytes

/-- caml_attempt_open at `open(truename, O_RDONLY)`: the duplicated name, the
quiet opening message and its free are behind it. -/
structure AttemptAtOpen (H : List (Nat × Nat)) (capacity : Nat) (ra s0 s1 s2 s3 s4 flag name : BitVec 64)
    (len : Nat) (before after : Config) where
  copy : BitVec 64
  pc : PCAt 0x80042590#64 after
  link : gprGet after.σ 1 = some jal_80004920_call.link
  path : gprGet after.σ 10 = some copy
  flags : gprGet after.σ 11 = some 0#64
  stack : gprGet after.σ 2 = some attemptStack
  truename : gprGet after.σ 18 = some copy
  trail : gprGet after.σ 8 = some trailSlot
  slot : gprGet after.σ 19 = some exeNameSlot
  flagReg : gprGet after.σ 20 = some flag
  upper : ∀ k, 21 ≤ k → k ≤ 27 → gprGet after.σ k = gprGet before.σ k
  ready : RuntimeReady ((copy.toNat, len + 1) :: H) capacity attemptStack jal_80004920_call.link after
  fresh : heapStart ≤ copy.toNat ∧ copy.toNat + (len + 1) ≤ heapEnd
  aligned : copy.toNat % 16 = 0
  bytes : ∀ k, k ≤ len → (after.σ.mem[copy.toNat + k]?).getD 0 = (WhileMinImage.initialMem[name.toNat + k]?).getD 0
  slots : ∀ off value, (off, value) ∈ attemptOpenSlots ra s0 s1 s2 s3 s4 →
    bytesT after.σ.mem (nativeFrameBase parameterStack 64 + off) 8 = value
  caller : CallerFrame parameterStack before after
  late : LateImage after
  run : Steps before after

theorem attempt_open_to_open {c s : Config} {H : List (Nat × Nat)} {capacity charge : Nat}
    {ra s0 s1 s2 s3 s4 flag name : BitVec 64} {len : Nat}
    (S : AttemptSearched H (capacity + charge) ra s0 s1 s2 s3 s4 flag name len c s)
    (embedded : ∀ k, k ≤ len → EmbedByte (name.toNat + k))
    (kind : ∀ d : Config, EmbedImage d → SearchName d.σ.mem name len)
    (small : len ≤ 64) (charged : vsaChg (len + 1) charge) :
    ∃ after, Steps s after ∧ Nonempty (AttemptAtOpen H capacity ra s0 s1 s2 s3 s4 flag name len c after) := by
  have frameS : NativeFrame attemptStack (48 + allocHeadroom) := by constructor <;> decide
  have copyName (k : Nat) (hk : k ≤ len) :
      (s.σ.mem[S.copy.toNat + k]?).getD 0 = (s.σ.mem[name.toNat + k]?).getD 0 := by
    rw [S.bytes k hk, S.late.embed.byte _ (embedded k hk)]
  have copyBytes : CBytes s.σ.mem S.copy.toNat len := by
    have nameB := (kind s S.late.embed).cbytes
    exact {
      nz := fun i hi => by
        change (s.σ.mem[_]?).getD 0 ≠ 0
        rw [copyName i (by omega)]
        exact nameB.nz i hi
      nul := by
        change (s.σ.mem[_]?).getD 0 = 0
        rw [copyName len (Nat.le_refl _)]
        exact nameB.nul
      lo := by have := S.fresh.1; unfold heapStart at this; omega
      hi := by have := S.fresh.2; unfold heapEnd at this; omega
      htif := Or.inr (by have := S.fresh.1; unfold heapStart at this; omega) }
  -- caml_stat_strdup(truename)
  obtain ⟨atDup, run1, dcall⟩ := (attempt_open_strdup s _ attemptStack S.copy S.ready.toLeafInput
    ⟨S.result, S.stack, trivial⟩).run s ⟨S.pc, rfl⟩
  have readyDup := S.ready.stack_log dcall (by decide) (by simp only [keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ dcall.regs (by rfl)) (gholds_lookup (n := 1) _ dcall.regs (by rfl))
    (by decide) frameS (by simp only [LogInW])
  have sameDup : atDup.σ.mem = s.σ.mem := dcall.memory
  have toDup (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [18] ++ [1])
      (hv : gprGet s.σ n = some v) : gprGet atDup.σ n = some v :=
    (dcall.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  obtain ⟨atMsg, run2, ⟨D⟩⟩ := (strdup_full atDup _ capacity charge attemptStack
    jal_800048f4_call.link trailSlot (gprGet atDup.σ 9 |>.getD 0) S.copy len readyDup frameS
    ⟨by rw [gpr_of_ready readyDup 9 (by decide) (by decide)]; rfl,
      toDup 8 _ (by decide) (by decide) (by decide) S.trail,
      gholds_lookup (n := 10) _ dcall.regs (by rfl), trivial⟩
    (by rw [sameDup]; exact copyBytes)
    (fun k hk => Or.inr (Or.inr (Or.inr ⟨S.copy.toNat, len + 1, List.mem_cons_self .., S.fresh.1, S.fresh.2,
      by omega, by omega⟩)))
    (Or.inr (by have := S.fresh.1; unfold heapStart at this; unfold Layout.sym_tohost; omega)) (by omega)
    charged).run atDup ⟨dcall.pc, rfl⟩
  sorry
end OCaml.Vm.Boot.WhileMinElfParse
