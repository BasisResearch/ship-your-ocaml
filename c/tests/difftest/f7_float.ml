(* F7: floats (soft-float on rv64i) and their printing *)
let () =
  let x = 1.5 and y = 0.25 in
  Printf.printf "%g %g %g %g\n" (x +. y) (x -. y) (x *. y) (x /. y);
  print_float (sqrt 2.0); print_newline ();
  print_string (string_of_float 3.0); print_newline ();
  Printf.printf "%.3f %e\n" (4.0 *. atan 1.0) 12345.678;
  print_int (truncate 7.9 + int_of_float (-2.5)); print_newline ()
