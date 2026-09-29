(* F8: objects / methods (GETMETHOD, GETPUBMET), lazy, polymorphic compare *)
class counter = object (self)
  val mutable n = 0
  method incr = n <- n + 1; self#get
  method get = n
end
let () =
  let c = new counter in
  ignore (c#incr); ignore (c#incr);
  print_int c#get; print_newline ();
  let lz = lazy (print_string "forced "; 42) in
  print_int (Lazy.force lz + Lazy.force lz); print_newline ();
  print_int (compare (1, "b") (1, "a")); print_newline ();
  print_string (if [1; 2] = [1; 2] then "eq" else "ne"); print_newline ()
