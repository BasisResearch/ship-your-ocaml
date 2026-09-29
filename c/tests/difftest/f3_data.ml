(* F3: variants, records, pattern matching, arrays, lists *)
type shape = Circle of int | Rect of int * int | Empty
type pt = { x : int; mutable y : int }
let area = function Circle r -> 3 * r * r | Rect (w, h) -> w * h | Empty -> 0
let () =
  let shapes = [Circle 2; Rect (3, 4); Empty; Rect (1, 1)] in
  print_int (List.fold_left (fun a s -> a + area s) 0 shapes); print_newline ();
  let p = { x = 1; y = 2 } in p.y <- p.y + p.x;
  print_int (p.x * 10 + p.y); print_newline ();
  let a = Array.init 10 (fun i -> i * i) in
  a.(3) <- 100;
  print_int (Array.fold_left (+) 0 a); print_newline ();
  let l = List.rev (List.filter (fun v -> v mod 2 = 0) (Array.to_list a)) in
  List.iter (fun v -> print_int v; print_char ' ') l; print_newline ();
  match List.sort compare [5; 3; 9; 1] with
  | a :: b :: _ -> print_int (a * 10 + b); print_newline ()
  | _ -> ()
