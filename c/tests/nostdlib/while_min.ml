(* c/tests/while.ml without the Stdlib (ocamlc -nopervasives -nostdlib):
   the same loops, printing through the channel primitives directly. Small
   enough for BcSem to be evaluated in the kernel (OCaml/Programs). *)
type chan
type 'a ref = { mutable contents : 'a }
exception Exit
external ( + ) : int -> int -> int = "%addint"
external ( * ) : int -> int -> int = "%mulint"
external ( mod ) : int -> int -> int = "%modint"
external ( < ) : int -> int -> bool = "%lessthan"
external ( <= ) : int -> int -> bool = "%lessequal"
external ( > ) : int -> int -> bool = "%greaterthan"
external ( <> ) : int -> int -> bool = "%notequal"
external raise : exn -> 'a = "%raise"
external open_out : int -> chan = "caml_ml_open_descriptor_out"
external format_int : string -> int -> string = "caml_format_int"
external length : string -> int = "%string_length"
external output : chan -> string -> int -> int -> unit = "caml_ml_output"
external output_char : chan -> char -> unit = "caml_ml_output_char"
external flush : chan -> unit = "caml_ml_flush"
let stdout = open_out 1
let print_int n = let s = format_int "%d" n in output stdout s 0 (length s)
let newline () = output_char stdout '\n'
let () =
  let i = { contents = 0 } and sum = { contents = 0 } in
  while i.contents < 10 do
    i.contents <- i.contents + 1;
    sum.contents <- sum.contents + i.contents
  done;
  print_int sum.contents; newline ();
  let n = { contents = 0 } and total = { contents = 0 } in
  (try
     while true do
       n.contents <- n.contents + 1;
       if n.contents > 100 then raise Exit;
       if n.contents mod 2 <> 0 then total.contents <- total.contents + n.contents
     done
   with Exit -> ());
  print_int total.contents; newline ();
  let acc = { contents = 0 } and a = { contents = 1 } in
  while a.contents <= 3 do
    let b = { contents = 1 } in
    while b.contents <= 3 do
      acc.contents <- acc.contents + a.contents * b.contents;
      b.contents <- b.contents + 1
    done;
    a.contents <- a.contents + 1
  done;
  print_int acc.contents; newline ();
  flush stdout
