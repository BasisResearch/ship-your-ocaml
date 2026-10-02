external hash : int -> int -> int -> 'a -> int = "caml_hash"
let rec cycle = 1 :: cycle
let () =
  List.iter (fun (count, limit, seed) ->
    let show x = Printf.printf "%d " (hash count limit seed x) in
    show ""; show "a"; show "abc"; show "abcd"; show "abcdefg";
    show (1, "two", [3; 4; 5]); show cycle;
    show 0.; show (-0.); show nan; show infinity;
    show [| 1.; 2.; 3. |]; show Int64.min_int; show Int64.max_int;
    show Int32.min_int; show Nativeint.min_int; print_newline ())
    [10,100,0; 0,0,0; 1,0,42; 3,2,-1; 50,256,12345; 10,-1,0]
