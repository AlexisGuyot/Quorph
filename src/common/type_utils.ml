(* src/common/type_utils.ml - Utilitaires pour manipulation de types *)

module Ty = Types.Types
module D = Datatypes
module S = Stdlib.String
module L = Stdlib.List

(* ====================================================================== *)
(* Type construction helpers                                              *)
(* ====================================================================== *)

let arrow_type from_ty to_ty = 
  Ty.TArrow (from_ty, to_ty)

let binary_arrow_type arg1_ty arg2_ty result_ty =
  Ty.TArrow (arg1_ty, Ty.TArrow (arg2_ty, result_ty))

let record_type fields =
  Ty.TRecord fields

let collection_type ~kind element_ty =
  Ty.TColl (kind, element_ty)

let bag_type element_ty =
  collection_type ~kind:Ty.Coq_kBag element_ty

let product_type left_ty right_ty =
  Ty.TProd (left_ty, right_ty)

(* ====================================================================== *)
(* Type inspection                                                        *)
(* ====================================================================== *)

let is_collection_type = function
  | Ty.TColl _ -> true
  | _ -> false

let is_product_type = function
  | Ty.TProd _ -> true
  | _ -> false

let extract_element_type = function
  | Ty.TColl (_, element_ty) -> Some element_ty
  | _ -> None

(* ====================================================================== *)
(* Record field utilities                                                 *)
(* ====================================================================== *)

let lookup_field_in_record record_ty field_name =
  match record_ty with
  | Ty.TRecord fields ->
      Coq_conversion.assoc_in_coq_list field_name fields
  | _ -> None

(* ====================================================================== *)
(* Type pretty-printing                                                   *)
(* ====================================================================== *)

let rec pretty_print_type ty =
  match ty with
  | Ty.TInt -> "Int"
  | Ty.TString -> "String"
  | Ty.TBool -> "Bool"
  | Ty.TUnit -> "Unit"
  | Ty.TProd (left, right) ->
      "(" ^ pretty_print_type left ^ " * " ^ pretty_print_type right ^ ")"
  | Ty.TRecord fields ->
      let field_strings =
        let rec extract_fields = function
          | D.Coq_nil -> []
          | D.Coq_cons (D.Coq_pair (name, field_ty), rest) ->
              let name_str = Coq_conversion.string_of_coq name in
              let ty_str = pretty_print_type field_ty in
              (name_str ^ ": " ^ ty_str) :: extract_fields rest
        in
        extract_fields fields
      in
      "{ " ^ S.concat ", " field_strings ^ " }"
  | Ty.TColl (_, element_ty) ->
      "Coll(" ^ pretty_print_type element_ty ^ ")"
  | Ty.TSum (left, right) ->
      "Sum(" ^ pretty_print_type left ^ " + " ^ pretty_print_type right ^ ")"
  | Ty.TOption inner_ty ->
      "Option(" ^ pretty_print_type inner_ty ^ ")"
  | Ty.TArrow (from_ty, to_ty) ->
      "(" ^ pretty_print_type from_ty ^ " -> " ^ pretty_print_type to_ty ^ ")"