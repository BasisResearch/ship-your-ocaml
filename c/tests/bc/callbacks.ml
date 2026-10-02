external callback : ('a -> 'b) -> 'a -> 'b = "caml_callback"
external callback2 : ('a -> 'b -> 'c) -> 'a -> 'b -> 'c = "caml_callback2"
external callback3 : ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd = "caml_callback3"
let rec nested n = if n = 0 then 1 else 1 + callback nested (n - 1)
let () =
  Printf.printf "one %d two %d three %d nested %d\n"
    (callback (fun n -> n + 1) 41)
    (callback2 (fun a b -> a * 10 + b) 4 2)
    (callback3 (fun a b c -> a + b + c) 10 12 20)
    (nested 20);
  let add = callback (fun a b -> a + b) 10 in
  Printf.printf "partial %d\n" (add 32);
  (try ignore (callback (fun () -> failwith "callback failure") ())
   with Failure s -> Printf.printf "caught %s\n" s);
  Printf.printf "inner %d\n" (callback (fun () ->
    try callback (fun () -> raise Not_found) () with Not_found -> 42) ());
  at_exit (fun () -> print_endline "at exit")
