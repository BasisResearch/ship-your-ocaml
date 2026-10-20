import OCaml.Vm.Primitives.Uncaught.FatalLink

/-!
# BcSem's message for a constant exception is the machine's name

A constant exception is a block with a nonzero tag whose field 0 is its name
string. BcSem's `formatUncaught` returns that string up to its first NUL,
cut at 255 bytes. The machine reads the same bytes (`NameAt`). The string's
representation (`ObjAt` of its `.bytes` object, with `caml_alloc_string`'s
padding) makes the two agree: every name byte lies inside the string, and the
string has a NUL right after the name (`string_prefix`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Bytecode OCaml.Vm.Primitives
open OCaml.Vm.Primitives.Named.NamedValue (NameAt)

theorem toUInt8_toNat (n : Nat) : n.toUInt8.toNat = n % 2 ^ 8 := rfl

theorem byte_getD (c : Config) (a : Nat) : OCaml.Vm.byte c a = (c.σ.mem[a]?).getD 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [OCaml.Vm.byte]
  rw [getLsbD_bytesT _ 1 a k (by omega)]
  have : k / 8 = 0 := by omega
  have : k % 8 = k := by omega
  simp [*]

/-- **The string at `np` is the name, then a NUL** (or ends with the name):
its `takeWhile (· != 0)` is the name's bytes. -/
theorem string_prefix {c : Config} {pl : Place} {cp : ChanPlace} {np : BitVec 64} {b : List UInt8}
    {name : List (BitVec 8)} (strAt : ObjAt c pl cp np.toNat (.bytes b)) (named : NameAt c.σ.mem np name)
    (high : np.toNat + name.length < 2 ^ 64) :
    b.takeWhile (· != 0) = nameBytes name := by
  obtain ⟨-, inB, pad, zero⟩ := strAt
  simp only [Obj.wosize] at pad zero
  have addr (i : Nat) (hi : i ≤ name.length) : (np + BitVec.ofNat 64 i).toNat = np.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have nameByte (i : Nat) (hi : i < name.length) : OCaml.Vm.byte c (np.toNat + i) = name[i] := by
    rw [byte_getD, ← addr i (Nat.le_of_lt hi)]; exact named.bytes i hi
  have nul : OCaml.Vm.byte c (np.toNat + name.length) = 0#8 := by
    rw [byte_getD, ← addr _ (Nat.le_refl _)]; exact named.nul
  -- every name byte lies inside the string
  have long : name.length ≤ b.length := by
    apply Nat.le_of_not_lt
    intro j
    have nz := named.nonzero b.length j
    have eq := nameByte b.length j
    by_cases last : b.length < 8 * (b.length / 8 + 1) - 1
    · rw [zero b.length (Nat.le_refl _) last] at eq
      exact nz eq.symm
    · have ea : np.toNat + 8 * (b.length / 8 + 1) - 1 = np.toNat + b.length := by omega
      have p := pad
      rw [ea, eq] at p
      exact nz (BitVec.eq_of_toNat_eq (by rw [p]; simp; omega))
  -- the string's bytes up to the name's length are the name's
  have same (i : Nat) (hi : i < name.length) : b[i]'(by omega) = name[i].toNat.toUInt8 := by
    have := inB i (b[i]'(by omega)) (List.getElem?_eq_getElem _)
    rw [nameByte i hi] at this
    rw [this]
    apply UInt8.toNat.inj
    rw [toUInt8_toNat, BitVec.toNat_ofNat]
    have := (b[i]'(by omega)).toNat_lt
    omega
  have split : b = nameBytes name ++ b.drop name.length := by
    refine (List.take_append_drop name.length b).symm.trans ?_
    congr 1
    apply List.ext_getElem
    · simp [nameBytes]; omega
    · intro i h1 h2
      simp only [List.getElem_take, nameBytes, List.getElem_map]
      exact same i (by simpa [nameBytes] using h2)
  have nonzero : ∀ x ∈ nameBytes name, (x != 0) = true := by
    intro x hx
    simp only [nameBytes, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have nz := named.nonzero i hi
    simp only [bne_iff_ne, ne_eq]
    intro h0
    apply nz
    apply BitVec.eq_of_toNat_eq
    have := congrArg UInt8.toNat h0
    rw [toUInt8_toNat] at this
    have := name[i].isLt
    have z : (0 : UInt8).toNat = 0 := rfl
    simp only [BitVec.toNat_ofNat] at this ⊢
    omega
  rw [split, List.takeWhile_append_of_pos nonzero]
  cases hd : b.drop name.length with
  | nil => simp
  | cons x rest =>
    have hx : b[name.length]? = some x := by
      have := congrArg (·[0]?) hd
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      exact this
    have := inB name.length x hx
    rw [nul] at this
    have x0 : x = 0 := by
      apply UInt8.toNat.inj
      have := congrArg BitVec.toNat this
      simp only [BitVec.toNat_ofNat] at this
      have := x.toNat_lt
      have z : (0 : UInt8).toNat = 0 := rfl
      omega
    simp [x0]

/-- **`formatUncaught` on a constant exception** (a block with a nonzero tag,
field 0 its name string) is the machine's name bytes. -/
theorem formatUncaught_constant {P : Prog} {h : Heap} {l ln t : Nat} {rest : List Val} {b : List UInt8}
    {c : Config} {pl : Place} {cp : ChanPlace} {np : BitVec 64} {name : List (BitVec 8)}
    (block : h.get? l = some (.block t (.ptr ln 0 :: rest))) (tagNz : t ≠ 0)
    (str : h.get? ln = some (.bytes b)) (strAt : ObjAt c pl cp np.toNat (.bytes b))
    (named : NameAt c.σ.mem np name) (fits : name.length ≤ 255) (high : np.toNat + name.length < 2 ^ 64) :
    formatUncaught P h (.ptr l 0) = some (nameBytes name) := by
  have pre := string_prefix strAt named high
  have short : (nameBytes name).length ≤ 255 := by simpa [nameBytes] using fits
  simp [formatUncaught, tag?, block, Obj.tag, tagNz, field?, strOf?, str, pre, List.take_of_length_le short]

/-- **`fatal_bcsem` for a represented constant exception**: BcSem's message
comes from the exception block (nonzero tag, field 0 the name string) whose
string object is represented at the machine's name pointer `np`. -/
theorem fatal_bcsem_constant {ra sp exn s0 s1 s2 s3 np : BitVec 64} {name : List (BitVec 8)} {pl : Place}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {H : List (Nat × Nat)}
    {capacity charge : Nat} {p dom start trig active pos imp err : BitVec 64} {c0 : Config}
    {P : Prog} {s : St} {l ln t : Nat} {rest : List Val} {b : List UInt8} {cp : ChanPlace} {e : Nat} {w' : World}
    (pre : FatalPre ra sp exn s0 s1 s2 s3 np name pl s.world.named chains H capacity charge p dom start trig
      active pos c0)
    (std : FatalLowAt p dom start trig imp err c0)
    (printf : ∀ live capacity res, FprintfReport live capacity sp res dom err name)
    (inactive : active = 0#64)
    (noAtExit : s.world.named.lookup "Pervasives.do_at_exit" = none)
    (world : Vsa.Machine.output c0.σ = bytesToString s.world.console)
    (live : s.world.os.proc.exited = none)
    (stderrFd : TCB.Os.lookupFd s.world.os 2 = some (.stream .stderr))
    (block : s.heap.get? l = some (.block t (.ptr ln 0 :: rest))) (tagNz : t ≠ 0)
    (str : s.heap.get? ln = some (.bytes b)) (strAt : ObjAt c0 pl cp np.toNat (.bytes b))
    (sem : startUncaught P s (.ptr l 0) = .halt e w') :
    e = 2 ∧ Halts c0 (bytesToString w'.console) e := by
  have th := pre.thrown
  have hi := th.nameHigh
  have he : Vsa.Sim.DlHeap.heapEnd < 2 ^ 64 := by decide
  exact fatal_bcsem pre std printf inactive noAtExit world live stderrFd
    (formatUncaught_constant block tagNz str strAt th.named th.fits (by omega)) sem

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
