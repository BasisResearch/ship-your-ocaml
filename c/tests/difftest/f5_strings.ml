(* F5: strings, bytes, Buffer, Printf, Char *)
let () =
  let s = "hello" ^ ", " ^ "world" in
  print_string (String.uppercase_ascii s); print_newline ();
  print_int (String.length s); print_newline ();
  let b = Bytes.of_string s in Bytes.set b 0 'J';
  print_string (Bytes.to_string b); print_newline ();
  let buf = Buffer.create 4 in
  for i = 0 to 9 do Buffer.add_string buf (string_of_int i) done;
  print_string (Buffer.contents buf); print_newline ();
  Printf.printf "%d %5d %-3d| %x %s %c\n" 42 7 3 255 "str" 'z';
  print_string (String.concat "," (String.split_on_char ' ' "a b c"));
  print_newline ();
  print_int (int_of_string "12345" + Char.code 'A'); print_newline ()
