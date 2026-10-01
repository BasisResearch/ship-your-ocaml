let () =
  Callback.register "a1-replaced" 11;
  Callback.register "a1-replaced" 22;
  Callback.register "a1-prefix\000left" 33;
  Callback.register "a1-prefix\000right" 44;
  print_endline "named registrations completed"
