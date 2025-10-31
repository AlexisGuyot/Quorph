(* src/bridge/coq_ast_bridge.ml *)
open Ast_surface

(* Modules extraits *)
module Ty        = Types.Types
module Ir        = Term.Term
module CoqString = String
module D         = Datatypes
module A         = Ascii

module L = Stdlib.List
module S = Stdlib.String

open Bridge_util

(* ====================================================================== *)

let elam x ty body = Bridge_util.elam x ty body
let eapp f x       = Ir.EApp (f, x)

let ebool b        = Bridge_util.ebool b
let eint  n        = Bridge_util.eint n
let estr  st       = Bridge_util.estring st

let evar  v        = Ir.EVar (s v)
let erec  fs       = Ir.ERecord (dlist_of_list (fun (k,v) -> dpair (s k, v)) fs)
let eproj e a      = Ir.EProj (e, s a)

let escan src      = Ir.EScan (s src)
let ewhere p c     = Ir.EWhere (p, c)
let emap f c       = Ir.EMap (f, c)
let ejoin th c1 c2 = Ir.EJoin (th, c1, c2)
let ecount c       = Ir.ECount c

(* ====================================================================== *)
(* Traduction surface -> IR (logique d'origine conservée)                  *)
(* ====================================================================== *)

let rec to_ir (e : expr) : Ir.expr =
  match e with
    | EBool b     -> ebool b
  | EInt n      -> eint n
  | EString st  -> estr st
  | EIdent v    -> evar v
  | EField (e', a) -> eproj (to_ir e') a
  | ERecord fs     -> erec (L.map (fun (k,u) -> (k, to_ir u)) fs)
  | EBinop (op,a,b) ->
      let ai = to_ir a and bi = to_ir b in
      let has_str = match a,b with EString _, _ | _, EString _ -> true | _ -> false in
      bin_apply ~op ~has_string:has_str ai bi
  | ECall (fn, [arg]) when S.lowercase_ascii fn = "not" ->
      Ir.EApp (Ir.EVar (s "not"), to_ir arg)
  | ECall (fn, [arg]) when S.lowercase_ascii fn = "isnull" ->
      Ir.EApp (Ir.EVar (s "isnull"), to_ir arg)
  | ECall (fn, [arg]) when S.lowercase_ascii fn = "count" ->
      let coll_ir = to_ir arg in
      (* NB: quand on n'a pas le type élément ici, on laisse () par défaut *)
      count_of coll_ir Ty.TUnit
  | ECall (f, args) -> L.fold_left eapp (evar f) (L.map to_ir args)

(* ====================================================================== *)
(* Pipeline / requêtes                                                    *)
(* ====================================================================== *)

type ctx = { env : env; row : Ty.ty; tenv : (string * Ty.ty) list }

let ctx_with_row ctx row = { ctx with row; tenv = set_row_ty ctx.tenv row }

let of_query_env (env : env) (q : Ast_surface.query) : Ir.expr =
  let row = find_src env.catalog q.from in
  let ctx0 = { env; row; tenv = set_row_ty [] row } in
  let c0  = escan q.from in

  let step (c, ctx) (st : Ast_surface.stage) =
    match st with
    | SWhere pred ->
        let v = fresh_name ctx.tenv "y" in
        let lam = elam v ctx.row (to_ir pred) in
        (ewhere lam c, ctx)

    | SSelect fields ->
        let lam_body = erec (L.map (fun (k,e) -> (k, to_ir e)) fields) in
        (emap (elam "_" ctx.row lam_body) c, ctx)

    | SCount arg ->
        let coll_ir = to_ir arg in
        (ecount (emap (elam "_" ctx.row Ir.EConstUnit) coll_ir), ctx)

    | SJoin { id2; src2; on } ->
        let row2 = find_src env.catalog src2 in
        let z = fresh_name ctx.tenv "z" in
        let both = Ty.TRecord (dfields_of [q.from_id, ctx.row; id2, row2]) in
        let theta = elam z both (to_ir on) in
        let c' = ejoin theta c (escan src2) in
        let ctx' = ctx_with_row ctx both in
        (c', ctx')

    | SOrder (_key, _coll) ->
        (* Laisse la logique originelle telle qu'elle l'était dans ta version. *)
        (c, ctx)
  in
  fst (L.fold_left step (c0, ctx0) q.stages)

let of_query ~(catalog : (CoqString.string * Ty.ty) list) (q : Ast_surface.query) : Ir.expr =
  of_query_env { catalog } q
