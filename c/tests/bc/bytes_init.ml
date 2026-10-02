let () =
  let b = Bytes.create 20 in
  Printf.printf "length %d\n" (Bytes.length b);
  Bytes.set b 5 'x';
  Printf.printf "read %c\n" (Bytes.get b 5);
  output stdout b 5 1; print_newline ();
  let copy = Bytes.create 20 in
  Bytes.blit b 0 copy 0 20;
  Printf.printf "copied %c\n" (Bytes.get copy 5);
  Bytes.fill copy 0 5 'a';
  Bytes.fill copy 6 14 'z';
  print_endline (Bytes.to_string copy);
  Bytes.blit copy 0 copy 2 10;
  print_endline (Bytes.to_string copy);
  let ch = open_out_bin "init.bin" in
  output_string ch "input"; close_out ch;
  let ch = open_in_bin "init.bin" in
  let b = Bytes.create 40 in
  let n = input ch b 3 5 in
  output stdout b 3 n; print_newline ();
  close_in ch; Sys.remove "init.bin"
