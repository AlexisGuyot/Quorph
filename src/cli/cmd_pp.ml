let run file =
  let ic = open_in file in
  let len = in_channel_length ic in
  let text = really_input_string ic len in
  close_in ic;
  try
    let q = Simple_parser.parse text in
    let pretty = Ast_surface.pp q in
    print_endline "— Quorph pipeline (pretty-print) —";
    print_endline pretty;
    Ok ()
  with
  | Simple_parser.Parse_error msg -> Error (`Msg ("parse error: " ^ msg))
