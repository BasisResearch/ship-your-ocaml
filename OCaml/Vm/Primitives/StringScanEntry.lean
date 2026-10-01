import OCaml.Vm.Primitives.StringScanLoop
import OCaml.Vm.Primitives.StringContract

namespace OCaml.Vm.Primitives.StringScan
open Vsa.Machine Vsa.Sim LeanRV64DExecutable Vsa.Logic

noncomputable def comparisonValue (before : Config) (a b n m : Nat) : BitVec 64 :=
  if a = b then 3#64 else if n = m then scanValue before a b n else 1#64

theorem return_equal {before ra c regs}
    (h : BoundaryPost scanWrites before ra equalExit regs c) :
    FnSummary equalExit (fun d => d = c) (RegisterPost scanWrites before ra 3#64) := by
  have S := b54_summary c ra h.toLeafInput ⟨h.raReg, True.intro⟩
  exact S.weaken (fun _ he => he) (fun _ post => (h.then post).finish rfl)

theorem return_unequal {before ra c regs}
    (h : BoundaryPost scanWrites before ra (BitVec.ofNat 64 (Layout.sym_caml_string_equal + 76)) regs c)
    (result : lookupG 13 regs = some 1#64) :
    FnSummary (BitVec.ofNat 64 (Layout.sym_caml_string_equal + 76)) (fun d => d = c)
      (RegisterPost scanWrites before ra 1#64) := by
  have S := b4c_summary c ra 1#64 h.toLeafInput ⟨h.raReg, gholds_lookup _ h.regs result, True.intro⟩
  exact S.weaken (fun _ he => he) (fun _ post => (h.then post).finish rfl)

/-- The nonempty equal-size path initializes the generated word loop. -/
theorem setup_scan {before ra a b n c}
    (wa : WordRange a n) (wb : WordRange b n) (positive : 0 < n)
    (h : BoundaryPost scanWrites before ra (BitVec.ofNat 64 (Layout.sym_caml_string_equal + 28))
      [(1, ra), (10, BitVec.ofNat 64 a), (11, BitVec.ofNat 64 b), (15, BitVec.ofNat 64 n)] c) :
    FnSummary (BitVec.ofNat 64 (Layout.sym_caml_string_equal + 28)) (fun d => d = c)
      (RegisterPost scanWrites before ra (scanValue before a b n)) := by
  have nonzero : BitVec.ofNat 64 n ≠ 0#64 := by
    intro he
    have hn := congrArg BitVec.toNat he
    rw [wa.count_nat] at hn
    change n = 0 at hn
    omega
  have S := b1c_summary c ra (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 n)
    false h.toLeafInput h.regs (by simp [guardB, nonzero])
  apply boundary_bind S
  intro d post
  have T := b20_summary d ra (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 n)
    post.toLeafInput post.regs
  apply boundary_bind T
  intro e ep
  have start : BoundaryPost scanWrites before ra scanHead (loopRegs ra a b n 0) e :=
    ((h.then post).then ep).project (by
      simp [loopRegs, b20_regs, List.all, lookupG, wa.limit, scanPtr])
  exact scan_words wa wb positive start (by intro j hj; omega)

/-- Whole primitive machine summary, including alias and unequal-size paths. -/
theorem string_equal_machine (c : Config) (ra : BitVec 64) (a b la lb : Nat)
    (h : LeafInput ra c) (hx : gpr c 10 = some (BitVec.ofNat 64 a))
    (hy : gpr c 11 = some (BitVec.ofNat 64 b))
    (ga : StringGeometry a la) (gb : StringGeometry b lb)
    (ha : (word c (a - 8)).toNat / 1024 = (la + 8) / 8)
    (hb : (word c (b - 8)).toNat / 1024 = (lb + 8) / 8) :
    FnSummary (BitVec.ofNat 64 Layout.sym_caml_string_equal) (fun d => d = c)
      (RegisterPost scanWrites c ra (comparisonValue c a b ((la + 8) / 8) ((lb + 8) / 8))) := by
  let n := (la + 8) / 8
  let m := (lb + 8) / 8
  have wa := ga.wordRange
  have wb := gb.wordRange
  have sizesA : (word c (a - 8)).toNat / 1024 = n := ha
  have sizesB : (word c (b - 8)).toNat / 1024 = m := hb
  by_cases alias : a = b
  · subst b
    have S := b00_summary c ra (BitVec.ofNat 64 a) (BitVec.ofNat 64 a) true h
      ⟨h.raReg, hx, hy, True.intro⟩ (by simp [guardB])
    apply boundary_bind S
    intro d post
    simpa only [comparisonValue, if_pos rfl, ite_true, equalExit, Layout.sym_caml_string_equal] using return_equal post
  · have pointers : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
      intro he
      have hn := congrArg BitVec.toNat he
      have boundA := ga.upper
      have boundB := gb.upper
      simp only [BitVec.toNat_ofNat] at hn
      apply alias
      omega
    have S := b00_summary c ra (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) false h
      ⟨h.raReg, hx, hy, True.intro⟩ (by simp [guardB, pointers])
    apply boundary_bind S
    intro d post
    let bs0 := read8 d.σ.mem (a - 8)
    let bs1 := read8 d.σ.mem (b - 8)
    have size0 : bytesVal .ld bs0 >>> (10 : Nat) = BitVec.ofNat 64 n := by
      rw [read8_value]
      have he : word d (a - 8) = word c (a - 8) := by simp only [word, post.memory]
      change word d (a - 8) >>> (10 : Nat) = _
      rw [he]
      exact header_words _ n sizesA
    have size1 : bytesVal .ld bs1 >>> (10 : Nat) = BitVec.ofNat 64 m := by
      rw [read8_value]
      have he : word d (b - 8) = word c (b - 8) := by simp only [word, post.memory]
      change word d (b - 8) >>> (10 : Nat) = _
      rw [he]
      exact header_words _ m sizesB
    have window0 : ReadWindow (BitVec.ofNat 64 a - 8#64) 8 := by
      exact ga.header_window
    have window1 : ReadWindow (BitVec.ofNat 64 b - 8#64) 8 := by
      exact gb.header_window
    have pins0 : LPins8 d.σ.mem (BitVec.ofNat 64 a - 8#64).toNat bs0 := by
      have address : (BitVec.ofNat 64 a - 8#64).toNat = a - 8 := by
        exact string_header_address ga
      rw [address]
      exact read8_pins _ _
    have pins1 : LPins8 d.σ.mem (BitVec.ofNat 64 b - 8#64).toNat bs1 := by
      have address : (BitVec.ofNat 64 b - 8#64).toNat = b - 8 := by
        exact string_header_address gb
      rw [address]
      exact read8_pins _ _
    by_cases sizes : (la + 8) / 8 = (lb + 8) / 8
    · have branch : guardB bop.BNE (bytesVal .ld bs0 >>> (10 : Nat)) (bytesVal .ld bs1 >>> (10 : Nat)) = false := by
        simp only [guardB, size0, size1]
        simp only [n, m, sizes, bne_self_eq_false]
      have T := b04_summary d ra (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) bs0 bs1 false
        post.toLeafInput post.regs window0 pins0 window1 pins1 branch
      apply boundary_bind T
      intro e ep
      have entry : BoundaryPost scanWrites c ra (BitVec.ofNat 64 (Layout.sym_caml_string_equal + 28))
          [(1, ra), (10, BitVec.ofNat 64 a), (11, BitVec.ofNat 64 b), (15, BitVec.ofNat 64 n)] e :=
        (post.then ep).project (by simp [b04_regs, List.all, lookupG, size0])
      have U := setup_scan wa (by rw [sizes]; exact wb) (by omega) entry
      simpa only [comparisonValue, if_neg alias, if_pos sizes, Bool.false_eq_true, ite_false, ite_true, Layout.sym_caml_string_equal] using U
    · have counts : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 m := by
        intro he
        have hn := congrArg BitVec.toNat he
        rw [wa.count_nat, wb.count_nat] at hn
        exact sizes hn
      have branch : guardB bop.BNE (bytesVal .ld bs0 >>> (10 : Nat)) (bytesVal .ld bs1 >>> (10 : Nat)) = true := by
        simp [guardB, size0, size1, counts]
      have T := b04_summary d ra (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) bs0 bs1 true
        post.toLeafInput post.regs window0 pins0 window1 pins1 branch
      apply boundary_bind T
      intro e ep
      have U := return_unequal (post.then ep) rfl
      simpa only [comparisonValue, if_neg alias, if_neg sizes, ite_true, Layout.sym_caml_string_equal] using U

end OCaml.Vm.Primitives.StringScan
