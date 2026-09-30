import OCaml.Bytecode.Load
/-! L4 check (ROUND-1.md §2): a ZINC step is local. Along real runs, perturb
stack slot `d` (deeper than any instruction reads: d ≥ 8 + its operands) and
check the step's result differs from the unperturbed one in exactly that
slot (shifted by the step's stack delta), with every other field equal. -/
open OCaml.Bytecode

def perturbed (s : St) (d : Nat) : St := { s with stack := s.stack.set d (.int 0x5eed) }

def reads (i : Instr) : Nat := 8 + (i.args.map Int.natAbs).foldl max 0

def check (P : Prog) (fuel : Nat) : Nat × Nat × Nat := Id.run do
  let mut s := P.init
  let mut tested := 0
  let mut bad := 0
  let mut n := 0
  for _ in [0:fuel] do
    match decodeAt P.code s.pc with
    | none => break
    | some i =>
      let d := reads i
      if d + 1 < s.stack.length then
        tested := tested + 1
        match step P s, step P (perturbed s d) with
        | .next a, .next b =>
          -- same everything, stacks equal except one slot holding 0x5eed
          let diff := (List.zip a.stack b.stack).filter (fun (x, y) => x != y)
          let ok := a.pc == b.pc && a.accu == b.accu && a.env == b.env && a.extra == b.extra &&
            a.trap == b.trap && a.heap == b.heap && a.world == b.world &&
            a.stack.length == b.stack.length && diff.length == 1 &&
            (diff.head?.map (·.2) == some (.int 0x5eed))
          if !ok then bad := bad + 1
        | .halt e w, .halt e' w' => if !(e == e' && w == w') then bad := bad + 1
        | _, _ => bad := bad + 1
      match step P s with
      | .next s' => s := s'; n := n + 1
      | _ => break
  return (n, tested, bad)

def main (args : List String) : IO Unit := do
  for f in args do
    match loadExe (← IO.FS.readBinFile f) with
    | none => IO.println s!"{f}: load failed"
    | some P =>
      let (n, t, b) := check P 150000
      IO.println s!"{f}: {n} steps, {t} perturbed steps, {b} non-local"
