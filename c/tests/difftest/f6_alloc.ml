(* F6: allocation pressure: minor collections, promotion, a major slice *)
let () =
  let l = List.init 100_000 (fun i -> i) in
  print_int (List.fold_left (+) 0 l); print_newline ();
  let t = Hashtbl.create 16 in
  for i = 0 to 20_000 do Hashtbl.replace t (i mod 1000) (string_of_int i) done;
  print_int (Hashtbl.length t); print_string " "; print_string (Hashtbl.find t 999);
  print_newline ();
  let m = List.fold_left (fun acc i -> (i, i * i) :: acc) [] (List.init 20_000 Fun.id) in
  print_int (List.length m); print_newline ()
