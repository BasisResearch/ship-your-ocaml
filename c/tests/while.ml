(* OCaml port of ship-your-interpreter c/tests/while.wl:
   while loops, break (an exception), continue, nesting. *)
let () =
  let i = ref 0 and sum = ref 0 in
  while !i < 10 do
    i := !i + 1;
    sum := !sum + !i
  done;
  print_int !sum; print_newline ();
  let n = ref 0 and total = ref 0 in
  (try
     while true do
       n := !n + 1;
       if !n > 100 then raise Exit;
       if !n mod 2 <> 0 then total := !total + !n
     done
   with Exit -> ());
  print_int !total; print_newline ();
  let acc = ref 0 and a = ref 1 in
  while !a <= 3 do
    let b = ref 1 in
    while !b <= 3 do
      acc := !acc + !a * !b;
      b := !b + 1
    done;
    a := !a + 1
  done;
  print_int !acc; print_newline ()
