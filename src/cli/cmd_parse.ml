module S = Stdlib.String
module L = Stdlib.List

let run file =
  let ic = open_in file in
  let len = in_channel_length ic in
  let text = really_input_string ic len in
  close_in ic;
  try
    let (_q : Ast_surface.query) = Simple_parser.parse text in
    print_endline ("[parse] ok: " ^ file);
    Ok ()
  with
  | Parser_utils.Parse_error msg -> Error (`Msg ("parse error: " ^ msg))