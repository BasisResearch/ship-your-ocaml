(* F1: integer arithmetic, comparisons, branches, loops *)
let () =
  let x = 17 and y = 5 in
  List.iter (fun v -> print_int v; print_char ' ')
    [x + y; x - y; x * y; x / y; x mod y; -x / y; -x mod y;
     x land y; x lor y; x lxor y; x lsl 3; x asr 1; (-x) lsr 60;
     compare x y; min x y; max x y; abs (-x)];
  print_newline ();
  let r = ref 0 in
  for i = 1 to 100 do if i mod 3 = 0 || i mod 5 = 0 then r := !r + i done;
  print_int !r; print_newline ();
  print_int max_int; print_newline (); print_int min_int; print_newline ()
