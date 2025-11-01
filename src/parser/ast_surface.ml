module S = Stdlib.String
module L = Stdlib.List

type ident = string

type expr =
  | EIdent of ident
  | EField of expr * string
  | EInt of int
  | EBool of bool
  | EString of string
  | ERecord of (string * expr) list
  | EBinop of string * expr * expr
  | ECall of string * expr list

type agg = { out: string; fn: string; args: expr list }

type stage =
  | Where of expr
  | Join of ident * string * expr
  | Select of (string * expr) list
  | Group_by of expr * agg list
  | Order_by of string list
  | Limit of int
  | Distinct
  | Union of string * string  (* alias * source *)
  | Union_all of string * string

type query = { from_id: ident; from_source: string; stages: stage list }

let escape_string s =
  let b = Buffer.create (S.length s + 4) in
  S.iter (fun c ->
    match c with
    | '\"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | c    -> Buffer.add_char b c
  ) s;
  Buffer.contents b

let rec pp_expr = function
  | EIdent x -> x
  | EField (e, f) -> pp_expr e ^ "." ^ f
  | EInt n -> string_of_int n
  | EBool b -> if b then "true" else "false"
  | EString s -> "\"" ^ escape_string s ^ "\""
  | ERecord fs ->
      let fields = fs |> L.map (fun (k,v) -> k ^ ": " ^ pp_expr v) |> S.concat ", " in
      "{" ^ fields ^ "}"
  | EBinop (op, a, b) -> pp_expr a ^ " " ^ op ^ " " ^ pp_expr b
  | ECall (fn, args) ->
      let a = args |> L.map pp_expr |> S.concat ", " in
      fn ^ "(" ^ a ^ ")"

let pp_agg {out; fn; args} =
  let args_s = args |> L.map pp_expr |> S.concat ", " in
  out ^ ": " ^ fn ^ "(" ^ args_s ^ ")"

let pp_stage = function
  | Where e -> "where " ^ pp_expr e
  | Join (id, src, on) -> "join " ^ id ^ " in " ^ src ^ " on " ^ pp_expr on
  | Select fs -> "select " ^ (pp_expr (ERecord fs))
  | Group_by (k, aggs) ->
      let a = aggs |> L.map pp_agg |> S.concat ", " in
      "group by " ^ pp_expr k ^ " aggregate { " ^ a ^ " }"
  | Order_by keys -> "order by " ^ (S.concat ", " keys)
  | Limit n -> "limit " ^ string_of_int n
  | Distinct -> "distinct"
  | Union (id, src) -> "union " ^ id ^ " in " ^ src
  | Union_all (id, src) -> "union all " ^ id ^ " in " ^ src

let pp (q:query) =
  let header = "from " ^ q.from_id ^ " in " ^ q.from_source in
  let stages = q.stages |> L.map (fun s -> "| " ^ pp_stage s) |> S.concat "\n" in
  if stages = "" then header else header ^ "\n" ^ stages
