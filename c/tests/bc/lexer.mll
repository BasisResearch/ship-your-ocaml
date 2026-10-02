{
let count = ref 0
}
rule tokens = parse
| '@' (['a'-'z']+ as word) ':' (['0'-'9']+ as n) { Printf.printf "pair:%s:%s\n" word n; tokens lexbuf }
| (['a'-'z']+ as word) { incr count; Printf.printf "word:%s\n" word; tokens lexbuf }
| (['0'-'9']+ as n) { Printf.printf "int:%d\n" (int_of_string n); tokens lexbuf }
| [' ' '\n' '\t'] { tokens lexbuf }
| eof { Printf.printf "done:%d\n" !count }
| _ { failwith "bad character" }
{
let () =
  tokens (Lexing.from_string "@alpha:12 alpha 12 beta 345 gamma");
  let oc = open_out_bin "lexer-input.txt" in
  output_string oc (String.concat " " (List.init 300 (fun _ -> "longword")));
  close_out oc;
  let ic = open_in_bin "lexer-input.txt" in
  tokens (Lexing.from_channel ic); close_in ic; Sys.remove "lexer-input.txt"
}
