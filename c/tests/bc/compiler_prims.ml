external array_get : 'a array -> int -> 'a = "caml_array_get"
external ensure : int -> unit = "caml_ensure_stack_capacity"
external seed : unit -> int array = "caml_sys_random_seed"
let rec cycle = 7 :: cycle
let () =
  ensure 1024;
  Printf.printf "dummy %d seed %b\n" (List.hd cycle) (Array.length (seed ()) > 0);
  List.iter (fun s -> print_endline (Digest.to_hex (Digest.string s)))
    [""; "a"; "abc"; String.make 55 'a'; String.make 56 'b'; String.make 64 'c'; String.make 1000 'd'];
  let shared = [42; -50000; 1073741824] in
  let value = (shared, shared, [|1.; -2.5|], Int64.min_int, Int32.max_int, Nativeint.min_int, "hello") in
  let ch = open_out_bin "fixture.marshal" in
  output_value ch value; close_out ch;
  print_endline (Digest.to_hex (Digest.file "fixture.marshal"));
  let ch = open_in_bin "fixture.marshal" in
  let (a, b, floats, i64, i32, ni, text) : int list * int list * float array * int64 * int32 * nativeint * string = input_value ch in
  close_in ch;
  Printf.printf "marshal %b %b %b %b %b %b %s\n" (a = shared) (a == b) (int_of_float (array_get floats 1) = -2)
    (Int64.to_int i64 = 0) (Int32.to_int i32 = 2147483647) (Nativeint.to_int ni = 0) text;
  Printf.printf "directory %b\n" (Array.exists ((=) "fixture.marshal") (Sys.readdir "."));
  let ch = open_out_bin "fixture.cycle" in output_value ch cycle; close_out ch;
  let ch = open_in_bin "fixture.cycle" in
  let c : int list = input_value ch in close_in ch;
  Printf.printf "cycle %d %b\n" (List.hd c) (List.tl c == c);
  Sys.remove "fixture.marshal"; Sys.remove "fixture.cycle"
