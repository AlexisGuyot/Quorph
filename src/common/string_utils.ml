(* src/common/string_utils.ml - Utilitaires de manipulation de chaînes *)

module S = Stdlib.String
module L = Stdlib.List

(* ====================================================================== *)
(* String manipulation                                                    *)
(* ====================================================================== *)

let trim = S.trim

let starts_with ~prefix str =
  S.length str >= S.length prefix
  && S.sub str 0 (S.length prefix) = prefix

let lowercase = S.lowercase_ascii

(* ====================================================================== *)
(* String escaping                                                        *)
(* ====================================================================== *)

let escape_string s =
  let buf = Buffer.create (S.length s + 4) in
  S.iter (fun c ->
    match c with
    | '\"' -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c    -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

(* ====================================================================== *)
(* String splitting                                                       *)
(* ====================================================================== *)

let split_lines text =
  text
  |> S.split_on_char '\n'
  |> L.map trim
  |> L.filter (fun s -> s <> "")

(* Trouve la position du pattern et retourne (position, reste_après_pattern) *)
let try_split_at ~pattern str =
  let pattern_len = S.length pattern in
  let str_len = S.length str in
  let rec find_pattern i =
    if i + pattern_len > str_len then None
    else if S.sub str i pattern_len = pattern then
      Some (i, S.sub str (i + pattern_len) (str_len - i - pattern_len))
    else
      find_pattern (i + 1)
  in
  find_pattern 0

(* ====================================================================== *)
(* Identifier checking                                                    *)
(* ====================================================================== *)

let is_identifier_start = function
  | 'a'..'z' | 'A'..'Z' | '_' -> true
  | _ -> false

let is_identifier_char = function
  | 'a'..'z' | 'A'..'Z' | '_' | '0'..'9' -> true
  | _ -> false

let is_valid_identifier str =
  str <> "" 
  && is_identifier_start (S.get str 0)
  && S.for_all is_identifier_char str

(* ====================================================================== *)
(* Cutting prefix/suffix                                                  *)
(* ====================================================================== *)

let cut_prefix ~prefix str =
  if starts_with ~prefix str then
    Some (S.sub str (S.length prefix) (S.length str - S.length prefix) |> trim)
  else
    None

let expect_prefix ~prefix str =
  match cut_prefix ~prefix str with
  | Some result -> result
  | None -> failwith ("expected prefix: " ^ prefix)

(* ====================================================================== *)
(* Extract source name (before first delimiter)                          *)
(* ====================================================================== *)

let extract_source_name raw =
  let len = S.length raw in
  let rec find_delimiter i =
    if i >= len then i
    else match S.get raw i with
      | '|' | ' ' | '\t' | '\n' -> i
      | _ -> find_delimiter (i + 1)
  in
  let delimiter_pos = find_delimiter 0 in
  S.sub raw 0 delimiter_pos