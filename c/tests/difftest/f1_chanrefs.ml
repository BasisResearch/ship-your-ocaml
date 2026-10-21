(* caml_ml_out_channels_list wraps every open output channel in a fresh
   custom block (one more refcount per listed channel: Chan.refs). Five custom
   blocks in all (stdin, stdout, stderr, then the two listed output channels):
   the G1 quiet budget (Budget.customs). *)
external out_channels_list : unit -> out_channel list = "caml_ml_out_channels_list"

let () =
  let l = out_channels_list () in
  print_int (List.length l);
  print_newline ();
  List.iter flush l;
  print_endline "listed channels flushed"
