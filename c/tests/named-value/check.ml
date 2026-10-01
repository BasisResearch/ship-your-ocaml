external lookup : string -> int = "test_named_value_lookup"

let () =
  Callback.register "a1-replaced" 11;
  Callback.register "a1-replaced" 22;
  Callback.register "a1-prefix\000left" 33;
  Callback.register "a1-prefix\000right" 44;
  assert (lookup "a1-replaced" = 22);
  assert (lookup "a1-prefix" = 44);
  assert (lookup "a1-prefix\000ignored" = 44);
  Printf.printf "%d %d\n" (lookup "a1-replaced") (lookup "a1-prefix")
