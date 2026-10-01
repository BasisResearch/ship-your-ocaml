(* Direct bytecode data arms and primitive boundaries. *)
type floats = { mutable a : float; b : float }
let () =
  let r = { a = 1.25; b = 2.5 } in
  r.a <- r.b;
  let v = [| r.a; r.b |] in
  print_int (Array.length v); print_newline ();
  let xs = [| 1; 2; 3 |] in
  Array.unsafe_set xs 1 7;
  print_int (Array.unsafe_get xs 1); print_newline ();
  let b = Bytes.of_string "abcde" in
  Bytes.blit b 0 b 1 4;
  Bytes.fill b 2 2 'z';
  Bytes.unsafe_set b 0 'X';
  print_int (Char.code (Bytes.unsafe_get b 0)); print_newline ();
  print_int (Char.code (String.unsafe_get "abc" 1)); print_newline ();
  print_endline (Bytes.to_string b);
  (try ignore (xs.(-1)) with Invalid_argument s -> print_endline s);
  (try Bytes.set b 9 'q' with Invalid_argument s -> print_endline s);
  print_int (compare (1, "a") (1, "b")); print_newline ()
