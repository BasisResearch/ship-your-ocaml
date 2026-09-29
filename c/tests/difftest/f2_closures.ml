(* F2: closures, partial application, recursion, tail calls *)
let rec fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)
let make_adder k = fun x -> x + k
let compose f g x = f (g x)
let rec loop acc n = if n = 0 then acc else loop (acc + n) (n - 1)
let () =
  print_int (fib 15); print_newline ();
  let add5 = make_adder 5 in
  print_int (compose add5 (( * ) 2) 10); print_newline ();
  print_int (loop 0 10000); print_newline ();
  let fs = List.map (fun i -> fun x -> x * i) [1; 2; 3] in
  print_int (List.fold_left (fun a f -> a + f 7) 0 fs); print_newline ();
  let rec even n = n = 0 || odd (n - 1) and odd n = n <> 0 && even (n - 1) in
  print_string (if even 100 then "even" else "odd"); print_newline ()
