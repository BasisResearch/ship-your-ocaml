(* F4: exceptions (trap frames), nested handlers, re-raise, finally *)
exception Found of int
let find p l = try List.iter (fun v -> if p v then raise (Found v)) l; None
               with Found v -> Some v
let () =
  (match find (fun v -> v > 3) [1; 5; 7] with
   | Some v -> print_int v | None -> print_string "none");
  print_newline ();
  let r = try (try raise Not_found with Not_found -> failwith "inner")
          with Failure m -> m in
  print_string r; print_newline ();
  let c = ref 0 in
  (try Fun.protect ~finally:(fun () -> incr c) (fun () -> raise Exit)
   with Exit -> incr c);
  print_int !c; print_newline ();
  (try ignore ([| 1 |].(5)) with Invalid_argument m -> print_string m);
  print_newline ();
  (try ignore (1 / (!c - 2)) with Division_by_zero -> print_string "div0");
  print_newline ()
