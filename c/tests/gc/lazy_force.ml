let () =
  let force = CamlinternalLazy.force in
  let x = lazy (Sys.opaque_identity 42) in
  print_int (force x); print_newline ();
  print_int (force x); print_newline ();
  print_int (force (Lazy.from_val 42)); print_newline ();
  let s = lazy (Sys.opaque_identity "forced") in
  print_endline (force s);
  print_endline (force s);
  let p = lazy (Sys.opaque_identity (7, 9)) in
  ignore (force p);
  let a, b = force p in print_int (a + b); print_newline ()
