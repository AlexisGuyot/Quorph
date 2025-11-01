(* src/parser/simple_parser.ml - Version refactorisée *)
open Ast_surface
open String_utils
open Parser_utils

module S = Stdlib.String
module L = Stdlib.List

(* ====================================================================== *)
(* Expression parsing                                                     *)
(* ====================================================================== *)

let rec parse_expr str = parse_or_expr str

and parse_or_expr str =
  match split_rightmost_binary_op ~operator:" or " str with
  | Some (left, right) -> EBinop ("or", parse_or_expr left, parse_and_expr right)
  | None -> parse_and_expr str

and parse_and_expr str =
  match split_rightmost_binary_op ~operator:" and " str with
  | Some (left, right) -> EBinop ("and", parse_and_expr left, parse_comparison_expr right)
  | None -> parse_comparison_expr str

and parse_comparison_expr str =
  let operators = [" = "; " <> "; " <= "; " >= "; " < "; " > "] in
  let rec try_operators = function
    | [] -> parse_additive_expr str
    | op :: rest ->
        match split_rightmost_binary_op ~operator:op str with
        | Some (left, right) -> 
            EBinop (trim op, parse_additive_expr left, parse_additive_expr right)
        | None -> try_operators rest
  in
  try_operators operators

and parse_additive_expr str =
  match split_rightmost_binary_op ~operator:" + " str with
  | Some (left, right) -> EBinop ("+", parse_additive_expr left, parse_multiplicative_expr right)
  | None ->
      match split_rightmost_binary_op ~operator:" - " str with
      | Some (left, right) -> EBinop ("-", parse_additive_expr left, parse_multiplicative_expr right)
      | None -> parse_multiplicative_expr str

and parse_multiplicative_expr str =
  match split_rightmost_binary_op ~operator:" * " str with
  | Some (left, right) -> EBinop ("*", parse_multiplicative_expr left, parse_postfix_expr right)
  | None ->
      match split_rightmost_binary_op ~operator:" / " str with
      | Some (left, right) -> EBinop ("/", parse_multiplicative_expr left, parse_postfix_expr right)
      | None -> parse_postfix_expr str

and parse_postfix_expr str =
  let str = trim str in
  let len = S.length str in
  
  (* Parenthesized expression *)
  if len >= 2 && (S.get str 0) = '(' && (S.get str (len - 1)) = ')' then
    parse_expr (S.sub str 1 (len - 2) |> trim)
  
  (* Record literal *)
  else if len >= 2 && (S.get str 0) = '{' && (S.get str (len - 1)) = '}' then
    parse_record_literal str
  
  (* Function call *)
  else
    match S.index_opt str '(' with
    | Some paren_pos when (S.get str (len - 1)) = ')' ->
        let fn_name = S.sub str 0 paren_pos |> trim in
        let args_str = S.sub str (paren_pos + 1) (len - paren_pos - 2) |> trim in
        parse_function_call fn_name args_str
    | _ ->
        (* Field access chain or atom *)
        let parts = split_field_access_chain str in
        match parts with
        | [] -> fail "Empty expression"
        | [single] -> parse_atom single
        | first :: rest ->
            let base = parse_atom first in
            L.fold_left (fun acc field -> EField (acc, field)) base rest

and parse_atom str =
  let str = trim str in
  let len = S.length str in
  
  (* String literal *)
  if len >= 2 && (S.get str 0) = '"' && (S.get str (len - 1)) = '"' then
    let content = S.sub str 1 (len - 2) in
    EString content
  
  (* Boolean literal *)
  else if lowercase str = "true" then EBool true
  else if lowercase str = "false" then EBool false
  
  (* Integer literal *)
  else if str <> "" && S.for_all (function '0'..'9' -> true | _ -> false) str then
    EInt (int_of_string str)
  
  (* Identifier *)
  else if is_valid_identifier str then
    EIdent str
  
  else
    fail ("Cannot parse atom: " ^ str)

and parse_record_literal str =
  let inside = S.sub str 1 (S.length str - 2) |> trim in
  if inside = "" then ERecord []
  else
    let items = split_by_top_level_comma inside in
    let parse_field item =
      match S.split_on_char ':' item with
      | [key; value] -> (trim key, parse_expr (trim value))
      | _ -> fail ("Malformed record field: " ^ item)
    in
    ERecord (L.map parse_field items)

and parse_function_call fn_name args_str =
  (* Special handling for filter DSL *)
  if lowercase fn_name = "filter" then
    match try_parse_filter_dsl args_str with
    | Some expr -> expr
    | None -> ECall (fn_name, [EIdent args_str])
  else
    if args_str = "" then ECall (fn_name, [])
    else if S.contains args_str ',' then
      let arg_parts = split_by_top_level_comma args_str in
      let parsed_args = L.map parse_expr arg_parts in
      ECall (fn_name, parsed_args)
    else
      ECall (fn_name, [parse_expr args_str])

and try_parse_filter_dsl payload =
  let lower_payload = lowercase payload in
  match try_split_at ~pattern:" where " lower_payload with
  | None -> None
  | Some (before_where_pos, _) ->
      (* before_where_pos est maintenant un int *)
      let before_where = S.sub payload 0 before_where_pos |> trim in
      let where_keyword_len = S.length " where " in
      let after_where = 
        S.sub payload (before_where_pos + where_keyword_len)
          (S.length payload - before_where_pos - where_keyword_len)
        |> trim
      in
      
      (* Parse "param in collection" pattern *)
      let pattern = Str.regexp {|\([A-Za-z_][A-Za-z0-9_]*\)[ \t]+in[ \t]+\([A-Za-z_][A-Za-z0-9_]*\)|} in
      if Str.string_match pattern before_where 0 then
        let param = Str.matched_group 1 before_where in
        let collection = Str.matched_group 2 before_where in
        let predicate = parse_expr after_where in
        Some (ECall ("filter", [EIdent param; EIdent collection; predicate]))
      else
        None

(* ====================================================================== *)
(* Stage parsing                                                          *)
(* ====================================================================== *)

let parse_where_stage line =
  let after_prefix = expect_prefix ~prefix:"where " line in
  Where (parse_expr after_prefix)

let parse_join_stage line =
  let after_prefix = expect_prefix ~prefix:"join " line in
  match S.split_on_char ' ' after_prefix |> L.filter ((<>) "") with
  | alias :: "in" :: rest ->
      let remainder = S.concat " " rest |> trim in
      let lower_remainder = lowercase remainder in
      (match try_split_at ~pattern:" on " lower_remainder with
       | None -> fail "join: missing 'on' clause"
       | Some (source_end_pos, _) ->
           let source = S.sub remainder 0 source_end_pos |> trim in
           let on_keyword_len = S.length " on " in
           let on_expr_str = 
             S.sub remainder (source_end_pos + on_keyword_len)
               (S.length remainder - source_end_pos - on_keyword_len)
             |> trim
           in
           Join (alias, source, parse_expr on_expr_str))
  | _ -> fail "join: expected 'join <id> in <source> on <expr>'"

let parse_group_by_stage line =
  let after_prefix = expect_prefix ~prefix:"group by " line in
  let lower_line = lowercase after_prefix in
  match try_split_at ~pattern:" aggregate " lower_line with
  | None -> fail "group by: missing 'aggregate' clause"
  | Some (key_end_pos, _) ->
      let key_str = S.sub after_prefix 0 key_end_pos |> trim in
      let agg_keyword_len = S.length " aggregate " in
      let agg_str = 
        S.sub after_prefix (key_end_pos + agg_keyword_len)
          (S.length after_prefix - key_end_pos - agg_keyword_len)
        |> trim
      in
      
      let len = S.length agg_str in
      if len >= 2 && (S.get agg_str 0) = '{' && (S.get agg_str (len - 1)) = '}' then
        let inside = S.sub agg_str 1 (len - 2) |> trim in
        let items = if inside = "" then [] else split_by_top_level_comma inside in
        
        let parse_aggregate item =
          match S.split_on_char ':' item with
          | [output; fn_call] ->
              let output = trim output in
              let fn_call = trim fn_call in
              (match S.index_opt fn_call '(' with
               | None -> fail "aggregate: expected function(args)"
               | Some paren_pos ->
                   let fn = S.sub fn_call 0 paren_pos |> trim in
                   let args_str = 
                     S.sub fn_call (paren_pos + 1) 
                       (S.length fn_call - paren_pos - 2) 
                     |> trim
                   in
                   let args =
                     if args_str = "" then []
                     else if S.contains args_str ',' then
                       split_by_top_level_comma args_str |> L.map parse_expr
                     else
                       [parse_expr args_str]
                   in
                   { out = output; fn; args })
          | _ -> fail ("aggregate: malformed item: " ^ item)
        in
        
        Group_by (parse_expr key_str, L.map parse_aggregate items)
      else
        fail "aggregate: expected braces { ... }"

let parse_select_stage line =
  let after_prefix = expect_prefix ~prefix:"select " line in
  match parse_expr after_prefix with
  | ERecord fields -> Select fields
  | _ -> fail "select: expected record literal"

let parse_order_by_stage line =
  let after_prefix = expect_prefix ~prefix:"order by " line in
  let keys = split_by_top_level_comma after_prefix in
  Order_by keys

let parse_limit_stage line =
  let after_prefix = expect_prefix ~prefix:"limit " line in
  (* Robust parsing: extract leading integer *)
  let len = S.length after_prefix in
  let start = ref 0 in
  while !start < len && (S.get after_prefix !start) = ' ' do incr start done;
  let end_pos = ref !start in
  while !end_pos < len && (S.get after_prefix !end_pos) >= '0' && (S.get after_prefix !end_pos) <= '9' do
    incr end_pos
  done;
  if !end_pos = !start then fail "limit: not an integer"
  else
    let num_str = S.sub after_prefix !start (!end_pos - !start) in
    Limit (int_of_string num_str)

let parse_stage line =
  let line = trim line in
  let line = if starts_with ~prefix:"| " line then
    S.sub line 2 (S.length line - 2) |> trim
  else
    line
  in
  
  if lowercase line = "distinct" then Distinct
  else if starts_with ~prefix:"where " line then parse_where_stage line
  else if starts_with ~prefix:"join " line then parse_join_stage line
  else if starts_with ~prefix:"group by " line then parse_group_by_stage line
  else if starts_with ~prefix:"select " line then parse_select_stage line
  else if starts_with ~prefix:"order by " line then parse_order_by_stage line
  else if starts_with ~prefix:"limit " line then parse_limit_stage line
  else fail ("Unsupported stage: " ^ line)

(* ====================================================================== *)
(* Query parsing                                                          *)
(* ====================================================================== *)

let parse_header line =
  let after_prefix = expect_prefix ~prefix:"from " line in
  match S.split_on_char ' ' after_prefix |> L.filter ((<>) "") with
  | alias :: "in" :: rest ->
      let source = S.concat " " rest |> trim in
      if alias = "" || source = "" then fail "Malformed from clause";
      (alias, source)
  | _ -> fail "Expected: from <id> in <source>"

let parse text =
  let lines = split_lines text in
  match lines with
  | [] -> fail "Empty program"
  | header :: stage_lines ->
      let alias, source_full = parse_header header in
      
      (* Handle inline stages after source *)
      let source, inline_stages =
        let pieces = S.split_on_char '|' source_full |> L.map trim in
        match pieces with
        | [] -> (trim source_full, [])
        | source_piece :: stage_pieces ->
            let clean_source = if source_piece = "" then trim source_full else source_piece in
            let stage_lines =
              stage_pieces
              |> L.filter ((<>) "")
              |> L.map (fun s -> "| " ^ s)
            in
            (clean_source, stage_lines)
      in
      
      let all_stage_lines = inline_stages @ stage_lines in
      let stages = L.map parse_stage all_stage_lines in
      
      { from_id = alias; from_source = source; stages }