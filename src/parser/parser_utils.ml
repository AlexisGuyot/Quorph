(* src/parser/parser_utils.ml - Utilitaires de parsing *)

open String_utils

module S = Stdlib.String
module L = Stdlib.List

exception Parse_error of string

let fail msg = raise (Parse_error msg)

(* ====================================================================== *)
(* Comma splitting with nesting awareness                                 *)
(* ====================================================================== *)

let split_by_top_level_comma str =
  let rec scan i depth_paren depth_brace depth_bracket acc start_pos =
    if i = S.length str then
      let last_segment = S.sub str start_pos (i - start_pos) |> trim in
      let acc = if last_segment = "" then acc else last_segment :: acc in
      L.rev acc
    else
      let c = (S.get str i) in
      let new_depth_paren, new_depth_brace, new_depth_bracket =
        match c with
        | '(' -> depth_paren + 1, depth_brace, depth_bracket
        | ')' -> depth_paren - 1, depth_brace, depth_bracket
        | '{' -> depth_paren, depth_brace + 1, depth_bracket
        | '}' -> depth_paren, depth_brace - 1, depth_bracket
        | '[' -> depth_paren, depth_brace, depth_bracket + 1
        | ']' -> depth_paren, depth_brace, depth_bracket - 1
        | _ -> depth_paren, depth_brace, depth_bracket
      in
      if c = ',' && depth_paren = 0 && new_depth_brace = 0 && new_depth_bracket = 0 then
        let segment = S.sub str start_pos (i - start_pos) |> trim in
        let acc = if segment = "" then acc else segment :: acc in
        scan (i + 1) new_depth_paren new_depth_brace new_depth_bracket acc (i + 1)
      else
        scan (i + 1) new_depth_paren new_depth_brace new_depth_bracket acc start_pos
  in
  let str = trim str in
  if str = "" then [] else scan 0 0 0 0 [] 0

(* ====================================================================== *)
(* Binary operator splitting (from right, respecting nesting)            *)
(* ====================================================================== *)

let split_rightmost_binary_op ~operator str =
  let str_len = S.length str in
  let op_len = S.length operator in
  
  let rec scan pos depth_paren depth_brace depth_bracket =
    if pos < 0 then None
    else
      let c = (S.get str pos) in
      let new_depth_paren, new_depth_brace, new_depth_bracket =
        match c with
        | ')' -> depth_paren + 1, depth_brace, depth_bracket
        | '(' -> depth_paren - 1, depth_brace, depth_bracket
        | '}' -> depth_paren, depth_brace + 1, depth_bracket
        | '{' -> depth_paren, depth_brace - 1, depth_bracket
        | ']' -> depth_paren, depth_brace, depth_bracket + 1
        | '[' -> depth_paren, depth_brace, depth_bracket - 1
        | _ -> depth_paren, depth_brace, depth_bracket
      in
      
      if depth_paren = 0 && new_depth_brace = 0 && new_depth_bracket = 0 then
        if pos - op_len + 1 >= 0 then
          let segment = S.sub str (pos - op_len + 1) op_len in
          if lowercase segment = lowercase operator then
            let left = S.sub str 0 (pos - op_len + 1) |> trim in
            let right = S.sub str (pos + 1) (str_len - pos - 1) |> trim in
            Some (left, right)
          else
            scan (pos - 1) new_depth_paren new_depth_brace new_depth_bracket
        else
          scan (pos - 1) new_depth_paren new_depth_brace new_depth_bracket
      else
        scan (pos - 1) new_depth_paren new_depth_brace new_depth_bracket
  in
  scan (str_len - 1) 0 0 0

(* ====================================================================== *)
(* Field chain splitting                                                  *)
(* ====================================================================== *)

let split_field_access_chain str =
  let rec split_at_dot acc current =
    match S.index_opt current '.' with
    | None -> L.rev (current :: acc)
    | Some pos ->
        let before = S.sub current 0 pos |> trim in
        let after = S.sub current (pos + 1) (S.length current - pos - 1) |> trim in
        split_at_dot (before :: acc) after
  in
  split_at_dot [] (trim str)

let split_on_first ~needle (s : string) : (string * string) option =
  let lower = S.lowercase_ascii s in
  let n = S.length needle
  and m = S.length s in
  let rec loop i =
    if i + n > m then None
    else if S.sub lower i n = needle then
      Some ( S.sub s 0 i
           , S.sub s (i + n) (m - i - n) )
    else loop (i + 1)
  in
  loop 0
