import OCaml.Vm.Primitives.Uncaught.FatalCompose
import OCaml.Vm.Primitives.Console.World
import OCaml.Vm.Primitives.ExitPath.Primitive

/-!
# The uncaught path against BcSem's `startUncaught`

With neither `Printexc.handle_uncaught_exception` nor `Pervasives.do_at_exit`
registered, BcSem's `startUncaught` is `fatalExit` with the formatted message
(`startUncaught_quiet`): one write of `"Fatal error: exception " ++ msg ++
"\n"` on stderr, which the OS model completes (`osCall_write_stream`), then
`exit 2` (`fatalExit_halt`). The machine prints the same text and halts with
status 2 (`fatal_halts`), so it halts with BcSem's console and status
(`fatal_bcsem`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim VsaIris VsaIris.VsaHeap
open OCaml.Vm.Primitives.Named.NamedValue (strOf)

/-- The name's bytes in BcSem's encoding. -/
def nameBytes (name : List (BitVec 8)) : List UInt8 := name.map fun b => b.toNat.toUInt8

/-- The bytes BcSem's `fatalExit` writes for a message. -/
def reportBytes (msg : List UInt8) : List UInt8 :=
  ("Fatal error: exception ".toList.map fun c => c.toNat.toUInt8) ++ msg ++ [10]

theorem bytesToString_report (name : List (BitVec 8)) :
    bytesToString (reportBytes (nameBytes name)) = fatalText name := by
  have lit : bytesToString ("Fatal error: exception ".toList.map fun c => c.toNat.toUInt8) =
      "Fatal error: exception " := by decide
  have nl : bytesToString [10] = "\n" := by decide
  have nm : bytesToString (nameBytes name) = strOf name := by
    unfold bytesToString nameBytes strOf
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro b _
    simp only [Function.comp, Nat.toUInt8]
    congr 1
    rw [show (UInt8.ofNat b.toNat).toNat = b.toNat % 2 ^ 8 from rfl]
    exact Nat.mod_eq_of_lt b.isLt
  unfold fatalText reportBytes
  simp only [bytesToString, List.map_append, String.ofList_append] at lit nl nm ⊢
  rw [lit, nl, nm]

/-- `List.find?` on the key is `List.lookup`. -/
theorem find?_key {named : List (String × Val)} {k : String} :
    (named.find? (fun p => p.1 == k)).map (·.2) = named.lookup k := by
  induction named with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases h : a = k
    · subst h; simp [List.find?, List.lookup]
    · have h' : (k == a) = false := by simp; exact Ne.symm h
      have ha : (a == k) = false := by simp; exact h
      simp only [List.find?, ha, List.lookup, h', ih]

/-- **No handler, no `do_at_exit`**: `startUncaught` is `fatalExit` with the message. -/
theorem startUncaught_quiet {P : Prog} {s : St} {exn : Val} {msg : List UInt8}
    (noHandler : s.world.named.lookup "Printexc.handle_uncaught_exception" = none)
    (noAtExit : s.world.named.lookup "Pervasives.do_at_exit" = none)
    (fmt : formatUncaught P s.heap exn = some msg) :
    startUncaught P s exn = fatalExit s.world (some msg) := by
  unfold startUncaught
  simp only [find?_key, noHandler, noAtExit, fmt]

/-- **`fatalExit` with a message**: status 2, the report appended to the console. -/
theorem fatalExit_halt {w w' : World} {msg : List UInt8} {e : Nat} (live : w.os.proc.exited = none)
    (stderr : TCB.Os.lookupFd w.os 2 = some (.stream .stderr)) (h : fatalExit w (some msg) = .halt e w') :
    e = 2 ∧ w'.console = w.console ++ reportBytes msg := by
  simp only [fatalExit, ConsoleWrite.osCall_write_stream live stderr (by decide)] at h
  split at h
  · rename_i r os' call
    simp only [bind, Option.bind] at call
    split at call
    · cases call
    · rename_i p hx
      cases call
      cases h
      refine ⟨rfl, ?_⟩
      simp only [World.console, ExitPath.osCall_exit_streams hx]
      rfl
  · cases h

/-- **The machine halts like BcSem on an uncaught constant exception** with
no handler and no `do_at_exit` registered, the backtrace inactive: when
BcSem's `startUncaught` halts with `e` and world `w'`, the machine from the
fatal path's entry halts with status `e` and console `w'.console`. The
message is BcSem's `formatUncaught` of the exception (`message`, supplied by
the exception's representation: its constructor block and name string).
Named obligation: `FprintfReport` (with the stdio state at exit, `StdioAtExit`). -/
theorem fatal_bcsem {ra sp exn s0 s1 s2 s3 np : BitVec 64} {name : List (BitVec 8)} {pl : Place}
    {chains : Nat → List (BitVec 64 × List (BitVec 8) × Val)} {H : List (Nat × Nat)}
    {capacity charge : Nat} {p dom start trig active pos imp err : BitVec 64} {c0 : Config}
    {P : Prog} {s : St} {exnv : Val} {e : Nat} {w' : World}
    (pre : FatalPre ra sp exn s0 s1 s2 s3 np name pl s.world.named chains H capacity charge p dom start trig
      active pos c0)
    (std : FatalLowAt p dom start trig imp err c0)
    (printf : ∀ live capacity res, FprintfReport live capacity sp res dom err name)
    (inactive : active = 0#64)
    (noAtExit : s.world.named.lookup "Pervasives.do_at_exit" = none)
    (world : Vsa.Machine.output c0.σ = bytesToString s.world.console)
    (live : s.world.os.proc.exited = none)
    (stderrFd : TCB.Os.lookupFd s.world.os 2 = some (.stream .stderr))
    (message : formatUncaught P s.heap exnv = some (nameBytes name))
    (sem : startUncaught P s exnv = .halt e w') :
    e = 2 ∧ Halts c0 (bytesToString w'.console) e := by
  rw [startUncaught_quiet pre.input.noHandler noAtExit message] at sem
  obtain ⟨rfl, console⟩ := fatalExit_halt live stderrFd sem
  refine ⟨rfl, ?_⟩
  have h := fatal_halts (printed := "") pre std
    (fun _ v _ hv => absurd hv (by rw [noAtExit]; simp)) printf inactive
  have quiet : atExitOutput s.world.named "" = "" := by simp only [atExitOutput, noAtExit]
  rw [quiet, String.append_empty, world] at h
  rw [console]
  unfold bytesToString at h ⊢
  rw [List.map_append, String.ofList_append]
  have r := bytesToString_report name
  unfold bytesToString at r
  rw [r]
  exact h

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
