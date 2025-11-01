module S = Stdlib.String
module L = Stdlib.List

let run file =
  let ic = open_in file in
  let len = in_channel_length ic in
  let text = really_input_string ic len in
  close_in ic;
  match Quorph_frontend.type_of_text text with
  | Ok ty_str ->
      print_endline ("[type] " ^ ty_str);
      Ok ()
  | Error e -> Error (`Msg e)