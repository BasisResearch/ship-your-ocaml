let () =
  List.iter (fun n -> Printf.printf "%d|%+08d|%#x|%#o|%u|%.0d|%-8.4d\n" n n n n n n n)
    [0; 1; -1; 255; max_int; min_int];
  List.iter (fun s -> try Printf.printf "%s:%d\n" s (int_of_string s)
                     with Failure e -> print_endline e)
    ["123"; "-123"; "0xff"; "0b1001"; "0o77"; "0u4611686018427387904";
     "1_234"; "+17"; "_1"; "4611686018427387904"; "0xffffffffffffffff"];
  List.iter (fun f -> Printf.printf "%.12g|%e|%.3f\n" f f f)
    [0.; -0.; 1.5; 0.00001; 1e20; 2.5; 9.999999999999; infinity; neg_infinity; nan];
  List.iter (fun f -> Printf.printf "%.15g\n" (atan f))
    [-100.; -2.; -1.; -0.5; 0.; 0.25; 0.5; 1.; 2.; 100.]
