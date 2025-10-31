open Ast_surface

exception Parse_error of string
let fail msg = raise (Parse_error msg)

(* ------------ Utils ------------ *)

let try_split (pat : string) (s : string) : (string * string) option =
  let lp = String.length pat in
  let ls = String.length s in
  let rec loop i =
    if i + lp > ls then None
    else if String.sub s i lp = pat then
      let left  = String.sub s 0 i in
      let right = String.sub s (i + lp) (ls - i - lp) in
      (* optionnel : normaliser les espaces *)
      let trim x =
        let is_space = function ' ' | '\n' | '\t' | '\r' -> true | _ -> false in
        let a = ref 0 and b = ref (String.length x - 1) in
        while !a <= !b && is_space x.[!a] do incr a done;
        while !b >= !a && is_space x.[!b] do decr b done;
        if !a > !b then "" else String.sub x !a (!b - !a + 1)
      in
      Some (trim left, trim right)
    else
      loop (i + 1)
  in
  loop 0

let trim (s:string) = String.trim s
let starts_with ~pref s =
  String.length s >= String.length pref
  && String.sub s 0 (String.length pref) = pref

let split_lines (text:string) : string list =
  text
  |> String.split_on_char '\n'
  |> List.map trim
  |> List.filter (fun s -> s <> "")

let expect_prefix (pref:string) (s:string) : string =
  if starts_with ~pref s
  then String.sub s (String.length pref) (String.length s - String.length pref) |> trim
  else fail ("expected prefix: "^pref)

(* ------------ Lexer helpers (very light) ------------ *)

let is_ident_start c =
  match c with
  | 'a'..'z' | 'A'..'Z' | '_' -> true
  | _ -> false

let is_ident_char c =
  match c with
  | 'a'..'z' | 'A'..'Z' | '_' | '0'..'9' -> true
  | _ -> false

(* Split a comma list while respecting (), {}, [] nesting *)
let split_top_level_commas (s:string) : string list =
  let rec loop i depth_par depth_br depth_sq acc last =
    if i = String.length s then
      let last_piece = String.sub s last (i - last) |> trim in
      let acc = if last_piece = "" then acc else last_piece :: acc in
      List.rev acc
    else
      let c = s.[i] in
      let dp, db, ds =
        match c with
        | '(' -> depth_par+1, depth_br, depth_sq
        | ')' -> depth_par-1, depth_br, depth_sq
        | '{' -> depth_par, depth_br+1, depth_sq
        | '}' -> depth_par, depth_br-1, depth_sq
        | '[' -> depth_par, depth_br, depth_sq+1
        | ']' -> depth_par, depth_br, depth_sq-1
        | _ -> depth_par, depth_br, depth_sq
      in
      if c = ',' && dp = 0 && db = 0 && ds = 0 then
        let part = String.sub s last (i - last) |> trim in
        let acc = if part = "" then acc else part :: acc in
        loop (i+1) dp db ds acc (i+1)
      else
        loop (i+1) dp db ds acc last
  in
  let s = trim s in
  if s = "" then [] else loop 0 0 0 0 [] 0

(* Find the rightmost top-level occurrence of [op] in [s] *)
let split_binop_from_right (op:string) (s:string) : (string * string) option =
  let n = String.length s in
  let m = String.length op in
  let rec scan i depth_par depth_br depth_sq =
    if i < 0 then None
    else
      let c = s.[i] in
      let dp, db, ds =
        match c with
        | ')' -> depth_par+1, depth_br, depth_sq
        | '(' -> depth_par-1, depth_br, depth_sq
        | '}' -> depth_br+1 |> fun db -> depth_par, db, depth_sq
        | '{' -> depth_br-1 |> fun db -> depth_par, db, depth_sq
        | ']' -> depth_sq+1 |> fun ds -> depth_par, depth_br, ds
        | '[' -> depth_sq-1 |> fun ds -> depth_par, depth_br, ds
        | _ -> depth_par, depth_br, depth_sq
      in
      if dp = 0 && db = 0 && ds = 0 then (
        if i - m + 1 >= 0 then
          let seg = String.sub s (i - m + 1) m in
          if String.lowercase_ascii seg = String.lowercase_ascii op then
            let left = String.sub s 0 (i - m + 1) |> trim in
            let right = String.sub s (i + 1) (n - i - 1) |> trim in
            Some (left, right)
          else scan (i-1) dp db ds
        else scan (i-1) dp db ds
      ) else scan (i-1) dp db ds
  in
  scan (n-1) 0 0 0

(* ------------ Expression parsing ------------ *)

(* Forward decls by mutual recursion *)
let rec parse_expr (s:string) : expr =
  parse_expr_or s

and parse_expr_or s =
  match split_binop_from_right " or " s with
  | Some (a,b) -> EBinop ("or", parse_expr_or a, parse_expr_and b)
  | None -> parse_expr_and s

and parse_expr_and s =
  match split_binop_from_right " and " s with
  | Some (a,b) -> EBinop ("and", parse_expr_and a, parse_expr_cmp b)
  | None -> parse_expr_cmp s

and parse_expr_cmp s =
  let try_ops = [ " = "; " <> "; " <= "; " >= "; " < "; " > " ] in
  let rec go = function
    | [] -> parse_expr_add s
    | op::ops ->
        (match split_binop_from_right op s with
         | Some (a,b) -> EBinop (String.trim op, parse_expr_add a, parse_expr_add b)
         | None -> go ops)
  in
  go try_ops

and parse_expr_add s =
  match split_binop_from_right " + " s with
  | Some (a,b) -> EBinop ("+", parse_expr_add a, parse_expr_mul b)
  | None ->
      (match split_binop_from_right " - " s with
       | Some (a,b) -> EBinop ("-", parse_expr_add a, parse_expr_mul b)
       | None -> parse_expr_mul s)

and parse_expr_mul s =
  match split_binop_from_right " * " s with
  | Some (a,b) -> EBinop ("*", parse_expr_mul a, parse_expr_postfix b)
  | None ->
      (match split_binop_from_right " / " s with
       | Some (a,b) -> EBinop ("/", parse_expr_mul a, parse_expr_postfix b)
       | None -> parse_expr_postfix s)

and parse_expr_postfix s =
  (* field access chains: a.b.c *)
  let rec split_fields acc cur =
    match String.index_opt cur '.' with
    | None -> List.rev (cur::acc)
    | Some i ->
        let left = String.sub cur 0 i |> trim in
        let right = String.sub cur (i+1) (String.length cur - i - 1) |> trim in
        split_fields (left::acc) right
  in
  let s = trim s in
  (* Parenthesized *)
  if String.length s >= 2 && s.[0] = '(' && s.[String.length s - 1] = ')' then
    parse_expr (String.sub s 1 (String.length s - 2) |> trim)
  (* Record *)
  else if String.length s >= 2 && s.[0] = '{' && s.[String.length s - 1] = '}' then
    parse_record s
  (* Call: FN(...)  (must check '(' at top-level) *)
  else (
    match String.index_opt s '(' with
    | Some i when s.[String.length s - 1] = ')' ->
        let fn = String.sub s 0 i |> trim in
        let args_str = String.sub s (i+1) (String.length s - i - 2) |> trim in
        parse_call fn args_str
    | _ ->
        (* Field chain or atom *)
        let parts = split_fields [] s in
        match parts with
        | [] -> fail "empty"
        | [one] -> parse_atom one
        | first :: rest ->
            let base = parse_atom first in
            List.fold_left (fun acc f -> EField (acc, f)) base rest
  )

and parse_atom s =
  let s = trim s in
  (* string *)
  if String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"' then
    parse_string s
  (* bool *)
  else if String.lowercase_ascii s = "true" then EBool true
  else if String.lowercase_ascii s = "false" then EBool false
  (* int *)
  else if s <> "" && String.for_all (function '0'..'9' -> true | _ -> false) s then
    EInt (int_of_string s)
  (* ident *)
  else if s <> "" && is_ident_start s.[0] && String.for_all is_ident_char s then
    EIdent s
  else
    fail ("cannot parse atom: "^s)

and parse_string s =
  (* naive unescape: assumes well-formed "..." *)
  let inside = String.sub s 1 (String.length s - 2) in
  (* keep it simple; relying on input correctness for now *)
  EString inside

and parse_record s =
  let inside = String.sub s 1 (String.length s - 2) |> trim in
  if inside = "" then ERecord []
  else
    let items = split_top_level_commas inside in
    let fields =
      List.map
        (fun item ->
           match String.split_on_char ':' item with
           | [k; v] -> (trim k, parse_expr (trim v))
           | _ -> fail ("malformed record field: "^item)
        ) items
    in
    ERecord fields

and parse_call fn args_str =
  if String.lowercase_ascii fn = "filter" then (
    match try_parse_filter_payload args_str with
    | Some e -> e
    | None -> ECall (fn, [EIdent args_str])
  ) else
    if args_str = "" then ECall (fn, [])
    else if String.contains args_str ',' then
      let parts = split_top_level_commas args_str in
      let args = List.map parse_expr parts in
      ECall (fn, args)
    else
      ECall (fn, [parse_expr args_str])

(* Special parse for: filter(y in S where pred) *)
and try_parse_filter_payload (payload:string) : expr option =
  let lower = String.lowercase_ascii payload in
  let where_pos =
    try Some (Str.search_forward (Str.regexp_string " where ") lower 0)
    with Not_found -> None
  in
  match where_pos with
  | None -> None
  | Some pos ->
      let before = String.sub payload 0 pos |> trim in
      let after =
        String.sub payload (pos + String.length " where ")
          (String.length payload - pos - String.length " where ")
        |> trim
      in
      let re = Str.regexp "\\([A-Za-z_][A-Za-z0-9_]*\\)[ \t]+in[ \t]+\\([A-Za-z_][A-Za-z0-9_]*\\)" in
      if Str.string_match re before 0 then
        let v = Str.matched_group 1 before in
        let src = Str.matched_group 2 before in
        let pred = parse_expr after in
        Some (ECall ("filter", [EIdent v; EIdent src; pred]))
      else None

(* ------------ Stages & queries ------------ *)

let parse_header (line:string) : (ident * string) =
  (* from x in source *)
  let after = expect_prefix "from " line in
  match String.split_on_char ' ' after |> List.filter (fun s -> s<> "") with
  | id :: "in" :: rest ->
      let src = String.concat " " rest |> trim in
      if id = "" || src = "" then fail "malformed from";
      (id, src)
  | _ -> fail "expected: from <id> in <source>"

let parse_where (line:string) : stage =
  let line = if starts_with ~pref:"| " line then String.sub line 2 (String.length line - 2) |> trim else line in
  let after = expect_prefix "where " line in
  Where (parse_expr after)

let parse_join (line:string) : stage =
  let line = if starts_with ~pref:"| " line then String.sub line 2 (String.length line - 2) |> trim else line in
  let after = expect_prefix "join " line in
  match String.split_on_char ' ' after |> List.filter (fun s -> s <> "") with
  | id :: "in" :: tail ->
      let s = String.concat " " tail |> trim in
      let lower = String.lowercase_ascii s in
      let on_pos =
        try Some (Str.search_forward (Str.regexp_string " on ") lower 0)
        with Not_found -> None
      in
      (match on_pos with
       | None -> fail "join: missing 'on'"
       | Some pos ->
           let src = String.sub s 0 pos |> trim in
           let on_expr = String.sub s (pos + 4) (String.length s - pos - 4) |> trim in
           Join (id, src, parse_expr on_expr))
  | _ -> fail "join: expected 'join <id> in <source> on <expr>'"

let parse_group_aggregate (line:string) : stage =
  (* group by <expr> aggregate { out: FN(args), ... } *)
  let line = if starts_with ~pref:"| " line then String.sub line 2 (String.length line - 2) |> trim else line in
  let after_group = expect_prefix "group by " line in
  let lower = String.lowercase_ascii after_group in
  let agg_pos =
    try Some (Str.search_forward (Str.regexp_string " aggregate ") lower 0)
    with Not_found -> None
  in
  match agg_pos with
  | None -> fail "group by: missing 'aggregate'"
  | Some pos ->
      let key_str = String.sub after_group 0 pos |> trim in
      let agg_str =
        String.sub after_group
          (pos + String.length " aggregate ")
          (String.length after_group - pos - String.length " aggregate ")
        |> trim
      in
      if String.length agg_str >= 2 && agg_str.[0] = '{' && agg_str.[String.length agg_str - 1] = '}' then
        let inside = String.sub agg_str 1 (String.length agg_str - 2) |> trim in
        let items = if inside = "" then [] else split_top_level_commas inside in
        let aggs =
          items
          |> List.map (fun item ->
                (* out: FN(args) *)
                let parts = String.split_on_char ':' item in
                match parts with
                | [lhs; rhs] ->
                    let out = trim lhs in
                    let rhs = trim rhs in
                    (match String.index_opt rhs '(' with
                     | None -> fail "aggregate: expected FN(args)"
                     | Some i ->
                         let fn = String.sub rhs 0 i |> trim in
                         let args_str = String.sub rhs (i+1) (String.length rhs - i - 2) |> trim in
                         let args =
                           if args_str = "" then []
                           else if String.contains args_str ',' then split_top_level_commas args_str |> List.map parse_expr
                           else [parse_expr args_str]
                         in
                         { out; fn; args })
                | _ -> fail ("aggregate item malformed: "^item))
        in
        Group_by (parse_expr key_str, aggs)
      else fail "aggregate: expected braces { ... }"

let parse_select (line:string) : stage =
  (* select { a: expr, b: expr } *)
  let line = if starts_with ~pref:"| " line then String.sub line 2 (String.length line - 2) |> trim else line in
  let after = expect_prefix "select " line in
  match after with
  | s when String.length s >= 2 && s.[0] = '{' && s.[String.length s - 1] = '}' ->
      (match parse_record s with
       | ERecord fields -> Select fields
       | _ -> fail "select: expected record")
  | _ -> fail "select: expected { ... }"

let parse_order_by (line:string) : stage =
  let line = if starts_with ~pref:"| " line then String.sub line 2 (String.length line - 2) |> trim else line in
  let after = expect_prefix "order by " line in
  let keys = split_top_level_commas after in
  Order_by keys

let parse_limit (line:string) : stage =
  let line =
    if starts_with ~pref:"| " line
    then String.sub line 2 (String.length line - 2) |> trim
    else line in
  let after = expect_prefix "limit " line |> trim in
  (* robust parse: take the leading integer, ignore trailing CR/space/text *)
  let len = String.length after in
  let i = ref 0 in
  (* skip leading spaces *)
  while !i < len && after.[!i] = ' ' do incr i done;
  let j = ref !i in
  while !j < len && after.[!j] >= '0' && after.[!j] <= '9' do incr j done;
  if !j = !i then fail "limit: not an int"
  else
    let n = int_of_string (String.sub after !i (!j - !i)) in
    Limit n

let parse_stage (line:string) : stage =
  let line = trim line in
  let is_distinct s = String.lowercase_ascii (trim s) = "distinct" in
  if starts_with ~pref:"| " line then
    let rest = String.sub line 2 (String.length line - 2) |> trim in
    if starts_with ~pref:"where " rest then parse_where line
    else if starts_with ~pref:"join " rest then parse_join line
    else if starts_with ~pref:"group by " rest then parse_group_aggregate line
    else if starts_with ~pref:"select " rest then parse_select line
    else if starts_with ~pref:"order by " rest then parse_order_by line
    else if starts_with ~pref:"limit " rest then parse_limit line
    else if is_distinct rest then Distinct
    else fail ("unsupported stage: " ^ rest)
  else
    (* autoriser aussi sans le préfixe "| " *)
    if starts_with ~pref:"where " line then parse_where line
    else if starts_with ~pref:"join " line then parse_join line
    else if starts_with ~pref:"group by " line then parse_group_aggregate line
    else if starts_with ~pref:"select " line then parse_select line
    else if starts_with ~pref:"order by " line then parse_order_by line
    else if starts_with ~pref:"limit " line then parse_limit line
    else if is_distinct line then Distinct
    else fail ("unsupported stage: " ^ line)

(* Parse a full query: header + stages (multi-ligne ou inline après la source). *)
let parse (text : string) : query =
  let lines = split_lines text in
  match lines with
  | [] -> fail "empty program"
  | header :: rest ->
      (* 1) Header: "from x in SRC [| stage ...]" *)
      let id, src_full = parse_header header in

      (* 2) Support du style "inline": on découpe ce qui suit la source
            s'il y a des '|' sur la même ligne que le header. *)
      let src, inline_stage_lines =
        let pieces =
          src_full
          |> String.split_on_char '|'   (* découpe grossière *)
          |> List.map trim              (* supprime espaces autour *)
        in
        match pieces with
        | [] ->
            (* ne devrait pas arriver, mais soyons robustes *)
            (trim src_full, [])
        | src_piece :: stage_pieces ->
            let src_clean = if src_piece = "" then trim src_full else src_piece in
            (* parse_stage attend des lignes commençant par '|', on les recrée *)
            let stage_lines =
              stage_pieces
              |> List.filter (fun s -> s <> "")
              |> List.map (fun s -> "| " ^ s)
            in
            (src_clean, stage_lines)
      in

      (* 3) Stages finaux = stages inline éventuels + lignes suivantes *)
      let stage_lines = inline_stage_lines @ rest in
      let stages = List.map parse_stage stage_lines in

      { from_id = id; from_source = src; stages }


(* Parse a single stage line *)
(* let parse_stage (s:string) : stage =
  let s = String.trim s in
  let lower = String.lowercase_ascii s in
  (* distinct *)
  if lower = "distinct" then Distinct else
  (* union / union all *)
  (let rx_union_all = Str.regexp "^union[ ]+all[ ]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)[ ]+in[ ]+\\(.+\\)$" in
   let rx_union     = Str.regexp "^union[ ]+\\([a-zA-Z_][a-zA-Z0-9_]*\\)[ ]+in[ ]+\\(.+\\)$" in
   if Str.string_match rx_union_all lower 0 then
     let id = Str.matched_group 1 s in
     let src = Str.matched_group 2 s in
     Union_all (id, String.trim src)
   else if Str.string_match rx_union lower 0 then
     let id = Str.matched_group 1 s in
     let src = Str.matched_group 2 s in
     Union (id, String.trim src)
   else
     (* Fallback to existing rules *)
     (if starts_with ~pref:"where " lower then
        let pred = String.sub s 6 (String.length s - 6) |> parse_expr in
        Where pred
      else if starts_with ~pref:"select " lower then
        let rec_src = String.sub s 7 (String.length s - 7) |> parse_expr in
        (match rec_src with
         | ERecord fields -> Select fields
         | _ -> fail "select expects a record")
      else if starts_with ~pref:"group by " lower then
        let rest = String.sub s 9 (String.length s - 9) |> trim in
        (match try_split " aggregate { " rest with
         | None -> fail "group by requires aggregate { ... }"
         | Some (k, rhs) ->
             let k = parse_expr k in
             let agg_body =
               if String.length rhs >= 1 && rhs.[String.length rhs - 1] = '}' then
                 String.sub rhs 0 (String.length rhs - 1) |> trim
               else fail "missing } in aggregate"
             in
             let parts = split_top_level_commas agg_body in
             let parse_agg item =
               match String.split_on_char ':' item with
               | [out; rest] ->
                   let out = trim out in
                   let rest = trim rest in
                   (match String.index_opt rest '(' with
                    | Some i ->
                        let fn = trim (String.sub rest 0 i) in
                        let inside = String.sub rest (i+1) (String.length rest - i - 2) in
                        let args =
                          if String.trim inside = "" then [] else
                          if String.contains inside ','
                          then split_top_level_commas inside |> List.map parse_expr
                          else [parse_expr inside]
                        in
                        { out; fn; args }
                    | None -> fail "bad aggregate fn(args)")
               | _ -> fail "bad aggregate field"
             in
             let aggs = List.map parse_agg parts in
             Group_by (k, aggs))
      else if starts_with ~pref:"order by " lower then
        let rest = String.sub s 9 (String.length s - 9) |> trim in
        let keys = String.split_on_char ',' rest |> List.map trim in
        Order_by keys
      else if starts_with ~pref:"limit " lower then
        let n = int_of_string (String.sub s 6 (String.length s - 6) |> trim) in
        Limit n
      else fail ("unknown stage: " ^ s))) *)



(* Fallback stage builder used by parse: splits on '|' and uses parse_stage *)
let parse_stages_from_lines (lines:string list) : stage list =
  lines
  |> List.map String.trim
  |> List.filter (fun s -> s <> "")
  |> List.map parse_stage

