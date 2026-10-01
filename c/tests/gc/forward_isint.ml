let () =
  let x = Obj.new_block Obj.forward_tag 1 in
  Obj.set_field x 0 (Obj.repr 42);
  let before = Obj.is_int x in
  Gc.minor ();
  Printf.printf "%b %b\n" before (Obj.is_int x)
