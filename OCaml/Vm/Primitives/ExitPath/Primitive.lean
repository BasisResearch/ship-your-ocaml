import OCaml.Vm.Primitives.ExitPath.Machine
import OCaml.Vm.Primitives.ImmediateContract

/-! `caml_sys_exit`: the represented primitive call halts the machine with
`primF1Impl`'s exit status and console. -/
namespace OCaml.Vm.Primitives.ExitPath
open OCaml.Bytecode Vsa.Machine Vsa.Sim VsaIris.Inst LeanRV64DExecutable

/-- The low 32 status bits of `caml_sys_exit`'s untagged argument. -/
theorem exitCode_low (n : BitVec 63) :
    BitVec.extractLsb 31 0 (Functions.shift_bits_right_arith (tag64 n) 1#6) = n.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Functions.shift_bits_right_arith, tag64, BitVec.getLsbD_extractLsb, BitVec.getLsbD_setWidth]
  simp [BitVec.getLsbD_sshiftRight, Sail.BitVec.toNatInt, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_signExtend]
  have h1 : 1 + i < 64 := by omega
  have h2 : i < 63 := by omega
  have h3 : i < 64 := by omega
  have h4 : ¬ 64 ≤ i := by omega
  simp [hi, h1, h2, h3, h4]

theorem exitStatus_tag (n : BitVec 63) :
    (exitStatus (exitCode (tag64 n))).toNat = (BitVec.ofInt 32 n.toInt).toNat := by
  unfold exitStatus exitCode
  rw [exitCode_low, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofInt,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_cond]
  have hn := n.isLt
  simp only [BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  split <;> split <;> omega

/-- The OS `exit` transition records the status and leaves the streams. -/
theorem osCall_exit_streams {os os' : TCB.Os.OsState} {e : Nat} {r : TCB.Os.Ret}
    (h : osCall os (.exit e) = some (r, os')) : os'.streams = os.streams := by
  simp [osCall, osReturn, TCB.Os.outs, TCB.Os.allowed, TCB.Os.next] at h
  split at h
  · simp at h
  · simp [TCB.Os.Ret.matches] at h
    obtain ⟨-, rfl⟩ := h
    rfl

/-- Native-runtime facts of the exit path beyond the represented call site:
machine health with the registers the exit path reads (`ExitOk`), the native stack window and the four runtime globals at their
defaults. The running-platform invariant supplies them at every `C_CALL`. -/
structure ExitRuntime (nativeSp : BitVec 64) (c : Config) : Prop where
  ok : ExitOk c
  stack : gpr c 2 = some nativeSp
  layout : ExitLayout exitDepth nativeSp
  globals : ExitGlobals c

theorem caml_sys_exit_halts {runtimeOk : Config → Prop} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {ra : BitVec 64} {c : Config} {nativeSp : BitVec 64}
    {n : BitVec 63} {code : Nat} {w' : World}
    (h : ImmediateInput runtimeOk P s pl cp sp high ra [.int n] c)
    (runtime : ExitRuntime nativeSp c)
    (entry : pcOf c = some (BitVec.ofNat 64 Layout.sym_caml_sys_exit))
    (sem : primF1Impl "caml_sys_exit" [.int n] s.heap s.world = .exit code w') :
    Halts c (bytesToString w'.console) code := by
  obtain ⟨word, hw, arg⟩ := h.arguments 0 (.int n) rfl
  simp only [valWord, Option.some.injEq] at hw
  subst hw
  have H := exit_halts ⟨h.toLeafInput, runtime.ok, runtime.stack, arg, runtime.layout, runtime.globals⟩
    (by simpa [Layout.sym_caml_sys_exit] using entry)
  rw [exitStatus_tag, h.data.world.1] at H
  simp only [primF1Impl, intArg?] at sem
  split at sem
  · rename_i r os' call
    cases sem
    simpa only [World.console, osCall_exit_streams call] using H
  · cases sem

end OCaml.Vm.Primitives.ExitPath
