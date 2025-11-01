(* -------------------------------------------------------------------------- *)
(* simple_parser.ml — version corrigée (autonome, stdlib qualifiée)           *)
(* -------------------------------------------------------------------------- *)

open Ast_surface

(* Qualifie explicitement la stdlib pour éviter tout masquage par d'autres
   modules nommés "String" / "List" / etc. *)
module S = Stdlib.String
module L = Stdlib.List

(* -------------------------------------------------------------------------- *)
(* Utilitaires locaux (pour éviter dépendances fragiles à Parser_utils)       *)
(* -------------------------------------------------------------------------- *)

let trim (s : string) : string =
  let is_space = function ' ' | '\n' | '\r' | '\t' -> true | _ -> false in
  let n = S.length s in
  let i0 =
    let rec f i = if i >= n then n else if is_space (S.get s i) then f (i+1) else i in
    f 0
  in
  let i1 =
    let rec f i = if i < 0 then -1 else if is_space (S.get s i) then f (i-1) else i in
    f (n-1)
  in
  if i1 < i0 then "" else S.sub s i0 (i1 - i0 + 1)

let lowercase (s : string) = S.lowercase_ascii s

(* Découpe case-insensitive au premier match de [needle] et renvoie les deux
   tronçons de la chaîne ORIGINALE. *)
let split_on_first ~needle (s : string) : (string * string) option =
  let lower = lowercase s in
  let n = S.length needle and m = S.length s in
  let rec loop i =
    if i + n > m then None
    else if S.sub lower i n = needle then
      Some ( S.sub s 0 i, S.sub s (i + n) (m - i - n) )
    else loop (i + 1)
  in
  loop 0

(* -------------------------------------------------------------------------- *)
(*  FROM ... [ON ...] [WHERE ...]                                            *)
(* -------------------------------------------------------------------------- *)

let parse_from_like (remainder_after_from : string)
  : string * string option * string option =
  (* 1) WHERE (optionnel) *)
  let source_part, where_opt =
    match split_on_first ~needle:" where " remainder_after_from with
    | Some (src, w) -> (trim src, Some (trim w))
    | None          -> (trim remainder_after_from, None)
  in
  (* 2) ON (optionnel) *)
  let source, on_opt =
    match split_on_first ~needle:" on " source_part with
    | Some (src, onp) -> (trim src, Some (trim onp))
    | None            -> (source_part, None)
  in
  (source, on_opt, where_opt)

(* -------------------------------------------------------------------------- *)
(*  Bloc mutuellement récursif                                                *)
(* -------------------------------------------------------------------------- *)

let rec parse_expr (s : string) : expr =
  let s = trim s in
  if s = "" then EIdent ""
  else
    match try_parse_filter_dsl s with
    | Some e -> e
    | None ->
      begin match parse_select_like s with
      | Some e -> e
      | None ->
        begin match parse_call_like s with
        | Some e -> e
        | None -> EIdent s
        end
      end

and try_parse_filter_dsl (payload : string) : expr option =
  (* Forme:  "x in xs where <predicate>" *)
  match split_on_first ~needle:" where " payload with
  | None -> None
  | Some (before_where, after_where) ->
      let before_where = trim before_where in
      let after_where  = trim after_where in
      (* Regex OCaml: les backslashes doivent être doublés. *)
      let re = Str.regexp "\\([A-Za-z_][A-Za-z0-9_]*\\)[ \\t]+in[ \\t]+\\([A-Za-z_][A-Za-z0-9_]*\\)" in
      if Str.string_match re before_where 0 then
        let param      = Str.matched_group 1 before_where in
        let collection = Str.matched_group 2 before_where in
        let predicate  = parse_expr after_where in
        Some (ECall ("filter", [EIdent param; EIdent collection; predicate]))
      else
        None

and parse_call_like (s : string) : expr option =
  match split_on_first ~needle:"(" s with
  | Some (fname, rest) when S.length rest > 0 && (S.get rest (S.length rest - 1)) = ')' ->
      let args_s = S.sub rest 0 (S.length rest - 1) in
      Some (parse_simple_call (trim fname) args_s)
  | _ -> None

and parse_select_like (s : string) : expr option =
  let lower = lowercase s in
  if S.length lower >= 7 && S.sub lower 0 7 = "select " then
    let after = S.sub s 7 (S.length s - 7) in
    parse_select_from after
  else None

and parse_simple_call (name : string) (args_s : string) : expr =
  (* parse basique d'appel f(a,b,c) en séparant par virgules non emboîtées. *)
  let rec split_args s i depth acc start =
    if i = S.length s then
      let last = S.sub s start (i - start) |> trim in
      L.rev (if last = "" then acc else last :: acc)
    else
      match (S.get s i) with
      | '(' | '[' | '{' -> split_args s (i+1) (depth+1) acc start
      | ')' | ']' | '}' -> split_args s (i+1) (depth-1) acc start
      | ',' when depth = 0 ->
          let piece = S.sub s start (i - start) |> trim in
          let acc = if piece = "" then acc else piece :: acc in
          split_args s (i+1) depth acc (i+1)
      | _ -> split_args s (i+1) depth acc start
  in
  let inside = trim args_s in
  let parts = if inside = "" then [] else split_args inside 0 0 [] 0 in
  let args = L.map parse_expr parts in
  ECall (name, args)

and parse_select_from (payload_after_select : string) : expr option =
  (* Formes attendues (adaptez selon votre AST):
     - "<what> from <source>"                      -> ECall("select_from", [...])
     - "<what> from <source> where <cond>"         -> ECall("select_from_where", [...])
     - "<what> from <source> on <cond> where <c2>" -> ECall("select_from_on_where", [...]) *)
  match split_on_first ~needle:" from " payload_after_select with
  | None -> None
  | Some (what, remainder) ->
      let what = trim what in
      let remainder = trim remainder in
      let (source, on_opt, where_opt) = parse_from_like remainder in
      let what_e   = parse_expr what in
      let source_e = parse_expr source in
      let on_e_opt = Option.map parse_expr on_opt in
      let where_e_opt = Option.map parse_expr where_opt in
      begin match (on_e_opt, where_e_opt) with
      | (None, None)       -> Some (ECall ("select_from", [what_e; source_e]))
      | (None, Some w)     -> Some (ECall ("select_from_where", [what_e; source_e; w]))
      | (Some o, None)     -> Some (ECall ("select_from_on", [what_e; source_e; o]))
      | (Some o, Some w)   -> Some (ECall ("select_from_on_where", [what_e; source_e; o; w]))
      end


(* --- API attendue par typing_driver : parse : string -> Ast_surface.query --- *)

(* 1) parse l'expression *)
let parse_expr_public (source : string) : Ast_surface.expr =
  parse_expr source

(* 2) l’envelopper en query *)
let parse (source : string) : Ast_surface.query =
  Ast_surface.QExpr (parse_expr_public source)
(* Si le constructeur n'est pas QExpr, remplace-le par le tien (ex: QSingle, QQuery, etc.) *)


(* -------------------------------------------------------------------------- *)
(* Fin du fichier                                                            *)
(* -------------------------------------------------------------------------- *)