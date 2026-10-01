let () =
  let p = "a2-file-test" in
  let o = open_out_bin p in
  output_string o "abcdef";
  Printf.printf "%d " (pos_out o);
  flush o;
  seek_out o 2; output_string o "XY"; close_out o;
  let i = open_in_bin p in
  let b = Bytes.make 8 '.' in
  let n = input i b 1 6 in
  Printf.printf "%d:%s:%d " n (Bytes.to_string b) (pos_in i);
  seek_in i 1; Printf.printf "%c " (input_char i);
  seek_in i 6;
  (try ignore (input_char i); print_string "bad " with End_of_file -> print_string "eof ");
  close_in i;
  Sys.rename p (p ^ "2");
  Printf.printf "%b %b " (Sys.file_exists p) (Sys.file_exists (p ^ "2"));
  Sys.remove (p ^ "2");
  (try ignore (open_in p); print_string "bad" with Sys_error _ -> print_string "missing");
  print_newline ()
