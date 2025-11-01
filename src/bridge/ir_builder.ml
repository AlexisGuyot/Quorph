(* src/bridge/ir_builder.ml - Construction d'expressions IR *)

module Ir = Term.Term
module CoqString = String

open Coq_conversion

(* ====================================================================== *)
(* IR expression builders                                                 *)
(* ====================================================================== *)

let lambda ~param ~param_ty ~body =
  Ir.ELam (coq_of_string param, param_ty, body)

let application fn arg =
  Ir.EApp (fn, arg)

let binary_application fn left right =
  application (application fn left) right

(* ====================================================================== *)
(* IR constant builders                                                   *)
(* ====================================================================== *)

let bool_const value =
  Ir.EConstBool (coq_bool value)

let int_const value =
  Ir.EConstInt (z_of_int value)

let string_const value =
  Ir.EConstString (coq_of_string value)

let unit_const =
  Ir.EConstUnit

(* ====================================================================== *)
(* IR variable and field access                                           *)
(* ====================================================================== *)

let variable name =
  Ir.EVar (coq_of_string name)

let field_access record field_name =
  Ir.EProj (record, coq_of_string field_name)

let record fields =
  let coq_fields =
    coq_list_of_ocaml_list
      (fun (name, expr) -> coq_pair (coq_of_string name, expr))
      fields
  in
  Ir.ERecord coq_fields

(* ====================================================================== *)
(* IR collection operations                                               *)
(* ====================================================================== *)

let scan source_name =
  Ir.EScan (coq_of_string source_name)

let where predicate collection =
  Ir.EWhere (predicate, collection)

let map mapper collection =
  Ir.EMap (mapper, collection)

let group_by key_fn collection =
  Ir.EGroupBy (key_fn, collection)

let order_by key_fn collection =
  Ir.EOrder (key_fn, collection)

let limit count collection =
  Ir.ELimit (count, collection)

let join condition left right =
  Ir.EJoin (condition, left, right)

let union left right =
  Ir.EUnion (left, right)

let union_all left right =
  Ir.EUnionAll (left, right)

let count collection =
  Ir.ECount collection

(* ====================================================================== *)
(* IR pair operations                                                     *)
(* ====================================================================== *)

let fst_projection pair =
  Ir.EFst pair

let snd_projection pair =
  Ir.ESnd pair