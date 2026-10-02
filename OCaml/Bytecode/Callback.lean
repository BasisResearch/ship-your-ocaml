import OCaml.Bytecode.Semantics

/-! Typed interface for callbackN_exn. The nested interpreter shares heap
and world effects and restores its suspended caller's registers. The C ABI's
exception-result tag is represented by `Except`, not exposed as an OCaml value. -/
namespace OCaml.Bytecode

inductive CallbackOutcome where
  | returned (value : Except Val Val) (caller : St)
  | exit (code : Nat) (world : World)
  | unsupported
  | wrong
  | timeout

private def completedCallback (P : Prog) (s : St) : Option CallbackOutcome :=
  if s.pc = P.code.size then
    match s.world.callbacks with
    | frame :: rest =>
      if frame.kind = .boundary then
        let result := match s.world.pendingException with
          | none => Except.ok s.accu
          | some exn => Except.error exn
        some (.returned result (restoreCallback s frame rest))
      else none
    | [] => none
  else none

private def runCallback (P : Prog) : Nat → St → CallbackOutcome
  | 0, _ => .timeout
  | fuel + 1, s =>
    match completedCallback P s with
    | some result => result
    | none => match step P s with
      | .next s' => runCallback P fuel s'
      | .halt code w => .exit code w
      | .wrong => .wrong
      | .unsupported => .unsupported

/-- C's exception-returning callback interface, with bounded execution for
validation. `startCallback` enforces 1..252 arguments. -/
def callbackN_exn (P : Prog) (fuel : Nat) (caller : St) (closure : Val) (args : List Val) :
    CallbackOutcome :=
  match startCallback P caller closure args .boundary with
  | .next nested => runCallback P fuel nested
  | _ => .wrong

def callback_exn (P : Prog) (fuel : Nat) (caller : St) (closure arg : Val) : CallbackOutcome :=
  callbackN_exn P fuel caller closure [arg]

def callback2_exn (P : Prog) (fuel : Nat) (caller : St) (closure a b : Val) : CallbackOutcome :=
  callbackN_exn P fuel caller closure [a, b]

def callback3_exn (P : Prog) (fuel : Nat) (caller : St) (closure a b c : Val) : CallbackOutcome :=
  callbackN_exn P fuel caller closure [a, b, c]

end OCaml.Bytecode
