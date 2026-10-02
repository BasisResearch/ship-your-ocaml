external register : string -> 'a -> unit = "caml_register_named_value"
external ( + ) : int -> int -> int = "%addint"
external raise : exn -> 'a = "%raise"
exception Boom of int
let () =
  register "one" (fun x -> x + 1);
  register "two" (fun x y -> x + y);
  register "three" (fun x y z -> x + y + z);
  register "five" (fun a b c d e -> a + b + c + d + e);
  register "raise1" (fun x -> raise (Boom x));
  register "raise2" (fun x y -> raise (Boom (x + y)));
  register "raise3" (fun x y z -> raise (Boom (x + y + z)))
