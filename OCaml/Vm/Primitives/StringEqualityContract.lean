import OCaml.Vm.Primitives.StringEncoding
import OCaml.Vm.Primitives.StringScanEntry

namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- Arguments are represented heap strings with the canonical padding written
by caml_alloc_string. The allocating-string summaries supply that invariant. -/
structure StringPairInput (runtimeOk : Config → Prop) (P : Prog) (s : St)
    (pl : Place) (cp : ChanPlace) (sp high : Nat) (ra : BitVec 64)
    (l l' a a' : Nat) (bs bs' : List UInt8) (c : Config) : Prop
    extends ImmediateInput runtimeOk P s pl cp sp high ra [.ptr l 0, .ptr l' 0] c where
  placed : pl.φ l = some a
  placed' : pl.φ l' = some a'
  object : s.heap.get? l = some (.bytes bs)
  object' : s.heap.get? l' = some (.bytes bs')
  canonical : PaddedString c a bs
  canonical' : PaddedString c a' bs'
  geometry : StringGeometry a bs.length
  geometry' : StringGeometry a' bs'.length

def stringEqualityResult (bs bs' : List UInt8) : BitVec 63 :=
  if bs == bs' then 1#63 else 0#63

/-- The machine's pointer/header/word branches compute the abstract result. -/
theorem string_comparison_value {c a a' bs bs'}
    (h : PaddedString c a bs) (h' : PaddedString c a' bs') :
    StringScan.comparisonValue c a a' ((bs.length + 8) / 8) ((bs'.length + 8) / 8) =
      tag64 (stringEqualityResult bs bs') := by
  classical
  by_cases alias : a = a'
  · subst a'
    have size := h.headerSize.symm.trans h'.headerSize
    have same := h.eq_of_words h' size (fun _ _ => rfl)
    simp [StringScan.comparisonValue, stringEqualityResult, same, tag64]
  · by_cases sizes : (bs.length + 8) / 8 = (bs'.length + 8) / 8
    · by_cases same : bs = bs'
      · have equal := ((h.eq_iff_words h').mp same).2
        have all : ∀ j, j < (bs.length + 8) / 8 → StringScan.equalWord c a a' j :=
          fun j hj => (equal j hj).symm
        rw [StringScan.comparisonValue, if_neg alias, if_pos sizes, StringScan.scanValue, if_pos all]
        simp [stringEqualityResult, same, tag64]
      · have notAll : ¬ ∀ j, j < (bs.length + 8) / 8 → StringScan.equalWord c a a' j := by
          intro all
          exact same (h.eq_of_words h' sizes (fun j hj => (all j hj).symm))
        rw [StringScan.comparisonValue, if_neg alias, if_pos sizes, StringScan.scanValue, if_neg notAll]
        simp [stringEqualityResult, same, tag64]
    · have different : bs ≠ bs' := by
        intro same
        exact sizes (by rw [same])
      rw [StringScan.comparisonValue, if_neg alias, if_neg sizes]
      simp [stringEqualityResult, different, tag64]

/-- A complete represented call summary for the generated string-equality CFG. -/
theorem string_equal_contract {runtimeOk : Config → Prop} (stable : MemoryStable runtimeOk)
    {P s pl cp sp high ra l l' a a' bs bs' c}
    (h : StringPairInput runtimeOk P s pl cp sp high ra l l' a a' bs bs' c) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_string_equal) (fun d => d = c)
      (ImmediatePost runtimeOk P s pl cp sp high "caml_string_equal" [.ptr l 0, .ptr l' 0]
        (stringEqualityResult bs bs') StringScan.scanWrites c ra) := by
  have S := StringScan.string_equal_machine c ra a a' bs.length bs'.length h.toLeafInput
    (h.arguments.get (i := 0) rfl (by simp [valWord, h.placed]))
    (h.arguments.get (i := 1) rfl (by simp [valWord, h.placed']))
    h.geometry h.geometry' h.canonical.headerSize h.canonical'.headerSize
  rw [string_comparison_value h.canonical h.canonical'] at S
  apply immediate_contract stable h.toImmediateInput S
  · simp [PreservesLoopRegisters, StringScan.scanWrites, Layout.reg_dispatchTable,
      Layout.reg_opcodeBound, Layout.reg_pending, Layout.reg_domain, gprReg]
  · by_cases same : bs = bs' <;>
      simp [primF1Impl, strOf?, h.object, h.object', stringEqualityResult, Val.ofBool, same]

end OCaml.Vm.Primitives
