let () =
  let x = lazy (Sys.opaque_identity 42) in
  let y = Lazy.from_val 42 in
  ignore (Lazy.force x);
  Printf.printf "%b " (x == y);
  Gc.minor ();
  Printf.printf "%b\n" (x == y)
