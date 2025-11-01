(* src/bridge/coq_ast_bridge.ml - Version refactorisée *)
open Ast_surface
open Coq_conversion
open String_utils
open Type_utils
open Fresh_name
open Operators
open Ir_builder

module Ty = Types.Types
module Ir = Term.Term
module D = Datatypes
module S = Stdlib.String
module L = Stdlib.List

(* ====================================================================== *)
(* Type environment management                                            *)
(* ====================================================================== *)

type type_env = (string * Ty.ty) list

let row_type_marker = "__ROW_TYPE__"

let with_row_type env row_ty =
  let without_marker = L.filter (fun (name, _) -> name <> row_type_marker) env in
  (row_type_marker, row_ty) :: without_marker

let get_row_type env =
  match L.assoc_opt row_type_marker env with
  | Some ty -> ty
  | None -> failwith "Internal error: row type not set in environment"

(* ====================================================================== *)
(* Catalog operations                                                     *)
(* ====================================================================== *)

let find_source_type catalog source_name =
  let coq_name = coq_of_string source_name in
  let rec search = function
    | [] -> failwith ("Unknown source in catalog: " ^ source_name)
    | (name, ty) :: rest ->
        if name = coq_name then ty else search rest
  in
  search catalog

(* ====================================================================== *)
(* Type inference helpers                                                 *)
(* ====================================================================== *)

let rec infer_expression_type env expr =
  match expr with
  | EBool _ -> Some Ty.TBool
  | EInt _ -> Some Ty.TInt
  | EString _ -> Some Ty.TString
  
  | EIdent var_name ->
      (match L.assoc_opt var_name env with
       | Some ty -> Some ty
       | None -> 
           lookup_field_in_record (get_row_type env) (coq_of_string var_name))
  
  | EField (base_expr, field_name) ->
      (match infer_expression_type env base_expr with
       | Some base_ty -> 
           lookup_field_in_record base_ty (coq_of_string field_name)
       | None -> None)
  
  | ERecord _ -> None
  
  | EBinop (op, left, right) ->
      let _ = infer_expression_type env left in
      let _ = infer_expression_type env right in
      if is_boolean_operator op then Some Ty.TBool else None
  
  | ECall (fn, args) ->
      let _ = L.map (infer_expression_type env) args in
      let fn_lower = lowercase fn in
      (match fn_lower with
       | "count" -> Some Ty.TInt
       | "sum" | "min" | "max" | "avg" -> Some Ty.TInt
       | _ -> if is_boolean_operator fn_lower then Some Ty.TBool else None)

let rec looks_like_boolean env expr =
  match expr with
  | EBool _ -> true
  | EField _ | EIdent _ -> true
  | EBinop (op, left, right) ->
      let op_lower = lowercase op in
      if op_lower = "and" || op_lower = "or" then
        looks_like_boolean env left && looks_like_boolean env right
      else if is_comparison_operator op then
        true
      else
        false
  | ECall (fn, [arg]) when lowercase fn = "not" ->
      looks_like_boolean env arg
  | _ -> false

let infer_aggregate_type fn args env =
  let fn_lower = lowercase fn in
  match fn_lower with
  | "count" -> Ty.TInt
  | "sum" | "max" | "min" | "avg" ->
      (match args with
       | first_arg :: _ ->
           (match infer_expression_type env first_arg with
            | Some ty -> ty
            | None -> Ty.TInt)
       | [] -> Ty.TInt)
  | _ -> Ty.TInt

let require_boolean context env expr =
  if not (looks_like_boolean env expr) then
    failwith (context ^ ": predicate must be boolean")

(* ====================================================================== *)
(* Expression translation helpers                                         *)
(* ====================================================================== *)

let rec collect_free_identifiers expr =
  match expr with
  | EIdent name -> [name]
  | EField (base, _) -> collect_free_identifiers base
  | ERecord fields -> L.concat_map (fun (_, v) -> collect_free_identifiers v) fields
  | EBinop (_, left, right) -> 
      collect_free_identifiers left @ collect_free_identifiers right
  | ECall (_, args) -> L.concat_map collect_free_identifiers args
  | _ -> []

let choose_parameter_name env expr =
  let in_scope = L.map fst env in
  let candidates =
    collect_free_identifiers expr
    |> L.filter (fun name -> not (L.mem name in_scope))
  in
  match candidates with
  | name :: _ -> name
  | [] -> "y"

(* ====================================================================== *)
(* Collection resolution                                                  *)
(* ====================================================================== *)

let rec resolve_collection catalog env from_alias collection_expr =
  match collection_expr with
  | EField (EIdent alias, field_name) ->
      (match L.assoc_opt alias env with
       | Some row_ty ->
           let base_var = variable alias in
           (match lookup_field_in_record row_ty (coq_of_string field_name) with
            | Some (Ty.TColl (_, elem_ty)) ->
                (field_access base_var field_name, elem_ty)
            | Some scalar_ty ->
                (field_access base_var field_name, scalar_ty)
            | None ->
                (translate_expr catalog env from_alias collection_expr, Ty.TUnit))
       | None ->
           (translate_expr catalog env from_alias collection_expr, Ty.TUnit))
  
  | EIdent name ->
      let row_ty = get_row_type env in
      (match lookup_field_in_record row_ty (coq_of_string name) with
       | Some (Ty.TColl (_, elem_ty)) ->
           let ir = match from_alias with
             | Some alias -> field_access (variable alias) name
             | None -> variable name
           in
           (ir, elem_ty)
       | Some scalar_ty ->
           let ir = match from_alias with
             | Some alias -> field_access (variable alias) name
             | None -> variable name
           in
           (ir, scalar_ty)
       | None ->
           (try
              let source_ty = find_source_type catalog name in
              (scan name, source_ty)
            with _ ->
              (translate_expr catalog env from_alias collection_expr, Ty.TUnit)))
  
  | _ ->
      let ir = translate_expr catalog env from_alias collection_expr in
      let elem_ty = infer_element_type catalog env collection_expr in
      (ir, elem_ty)

and infer_element_type catalog env collection_expr =
  match collection_expr with
  | ECall (fn, [EIdent _; coll; _]) when lowercase fn = "filter" ->
      infer_element_type catalog env coll
  | ECall (fn, [_; coll]) when lowercase fn = "filter" ->
      infer_element_type catalog env coll
  | _ ->
      let fallback_with_row ty_default =
        match collection_expr with
        | EField (EIdent alias, field_name) ->
            (match L.assoc_opt alias env with
             | Some row_ty ->
                 (match lookup_field_in_record row_ty (coq_of_string field_name) with
                  | Some (Ty.TColl (_, elem_ty)) -> elem_ty
                  | Some ty -> ty
                  | None -> ty_default)
             | None -> ty_default)
        | EIdent name ->
            let row_ty = get_row_type env in
            (match lookup_field_in_record row_ty (coq_of_string name) with
             | Some (Ty.TColl (_, elem_ty)) -> elem_ty
             | Some ty -> ty
             | None ->
                 (try find_source_type catalog name 
                  with _ -> ty_default))
        | _ -> ty_default
      in
      fallback_with_row Ty.TUnit

(* ====================================================================== *)
(* Main expression translation                                            *)
(* ====================================================================== *)

and translate_expr catalog env from_alias expr =
  match expr with
  | EInt n -> int_const n
  | EBool b -> bool_const b
  | EString s -> string_const s
  
  | EIdent var_name ->
      let row_ty = get_row_type env in
      (match lookup_field_in_record row_ty (coq_of_string var_name), from_alias with
       | Some _, Some alias -> field_access (variable alias) var_name
       | _ -> variable var_name)
  
  | EField (base, field_name) ->
      field_access (translate_expr catalog env from_alias base) field_name
  
  | ERecord fields ->
      let translated_fields = 
        L.map (fun (k, v) -> (k, translate_expr catalog env from_alias v)) fields 
      in
      record translated_fields
  
  | EBinop (op, left, right) ->
      let left_ir = translate_expr catalog env from_alias left in
      let right_ir = translate_expr catalog env from_alias right in
      let op_name = match left, right with
        | EString _, _ | _, EString _ -> disambiguate_for_strings op
        | _ -> op
      in
      binary_application (variable op_name) left_ir right_ir
  
  | ECall (fn, [arg]) when lowercase fn = "count" ->
      let coll_ir, elem_ty = resolve_collection catalog env from_alias arg in
      let unit_mapper = lambda ~param:"_" ~param_ty:elem_ty ~body:unit_const in
      let unit_collection = map unit_mapper coll_ir in
      count unit_collection
  
  | ECall (fn, [EIdent param; coll; pred]) when lowercase fn = "filter" ->
      translate_filter_dsl catalog env from_alias param coll pred
  
  | ECall (fn, [pred; coll]) when lowercase fn = "filter" ->
      translate_filter_simple catalog env from_alias pred coll
  
  | ECall (fn, args) ->
      let fn_var = variable fn in
      L.fold_left 
        (fun acc arg -> application acc (translate_expr catalog env from_alias arg))
        fn_var 
        args

and translate_filter_dsl catalog env from_alias param coll pred =
  let coll_ir, elem_ty = resolve_collection catalog env from_alias coll in
  let rec translate_predicate = function
    | EIdent name when name = param -> variable param
    | EField (base, field) -> field_access (translate_predicate base) field
    | ERecord fields ->
        record (L.map (fun (k, v) -> (k, translate_predicate v)) fields)
    | EBinop (op, left, right) ->
        let op_name = match left, right with
          | EString _, _ | _, EString _ -> disambiguate_for_strings op
          | _ -> op
        in
        binary_application (variable op_name) (translate_predicate left) (translate_predicate right)
    | ECall (fn, args) ->
        L.fold_left 
          (fun acc arg -> application acc (translate_predicate arg))
          (variable fn)
          args
    | other -> translate_expr catalog env from_alias other
  in
  let predicate_lambda = lambda ~param ~param_ty:elem_ty ~body:(translate_predicate pred) in
  where predicate_lambda coll_ir

and translate_filter_simple catalog env from_alias pred coll =
  let coll_ir, elem_ty = resolve_collection catalog env from_alias coll in
  let fresh_param = from_env ~avoid:(match from_alias with Some a -> [a] | None -> []) env "y" in
  let rec translate_predicate = function
    | EIdent name when name = fresh_param -> variable fresh_param
    | EField (base, field) -> field_access (translate_predicate base) field
    | ERecord fields ->
        record (L.map (fun (k, v) -> (k, translate_predicate v)) fields)
    | EBinop (op, left, right) ->
        let op_name = match left, right with
          | EString _, _ | _, EString _ -> disambiguate_for_strings op
          | _ -> op
        in
        binary_application (variable op_name) (translate_predicate left) (translate_predicate right)
    | ECall (fn, args) ->
        L.fold_left 
          (fun acc arg -> application acc (translate_predicate arg))
          (variable fn)
          args
    | other -> translate_expr catalog env from_alias other
  in
  let predicate_lambda = lambda ~param:fresh_param ~param_ty:elem_ty ~body:(translate_predicate pred) in
  where predicate_lambda coll_ir

(* ====================================================================== *)
(* Query stage translation                                                *)
(* ====================================================================== *)

let rec translate_stage catalog (current_ir, env) from_alias stage =
  let row_ty = get_row_type env in
  
  match stage with
  | Where predicate ->
      let pred_lambda = lambda ~param:from_alias ~param_ty:row_ty 
        ~body:(translate_expr catalog env (Some from_alias) predicate) in
      (where pred_lambda current_ir, env)
  
  | Select fields ->
      (match row_ty with
       | Ty.TProd _ ->
           translate_select_after_join catalog env from_alias fields current_ir row_ty
       | _ ->
           translate_select_simple catalog env from_alias fields current_ir row_ty)
  
  | Group_by (key_expr, aggregates) ->
      translate_group_by catalog env from_alias key_expr aggregates current_ir row_ty
  
  | Order_by _ ->
      let empty_record_lambda = 
        lambda ~param:"row" ~param_ty:row_ty ~body:(record []) in
      (order_by empty_record_lambda current_ir, env)
  
  | Limit n ->
      (limit (int_const n) current_ir, env)
  
  | Distinct ->
      translate_distinct current_ir row_ty env
  
  | Union (_, source2) ->
      let source2_name = extract_source_name source2 in
      (union current_ir (scan source2_name), env)
  
  | Union_all (_, source2) ->
      let source2_name = extract_source_name source2 in
      (union_all current_ir (scan source2_name), env)
  
  | Join (alias2, source2_raw, on_expr) ->
      translate_join catalog env from_alias alias2 source2_raw on_expr current_ir row_ty

and translate_select_simple catalog env from_alias fields current_ir row_ty =
  let field_types =
    L.map (fun (name, expr) ->
      match infer_expression_type env expr with
      | Some ty -> (name, ty)
      | None -> (name, Ty.TString)
    ) fields
  in
  let body_record =
    record (L.map (fun (k, v) -> 
      (k, translate_expr catalog env (Some from_alias) v)) fields)
  in
  let new_row_ty = record_type (coq_list_of_ocaml_list 
    (fun (k, ty) -> coq_pair (coq_of_string k, ty)) field_types) in
  let mapper = lambda ~param:from_alias ~param_ty:row_ty ~body:body_record in
  (map mapper current_ir, with_row_type env new_row_ty)

and translate_select_after_join catalog env from_alias fields current_ir row_ty =
  let other_alias =
    L.find_map (fun (name, _) ->
      if name <> row_type_marker && name <> from_alias then Some name else None
    ) env
    |> Option.value ~default:from_alias
  in
  
  let pair_param = "z" in
  let left_projection = fst_projection (variable pair_param) in
  let right_projection = snd_projection (variable pair_param) in
  
  let rec translate_for_join = function
    | EIdent name when name = from_alias -> left_projection
    | EIdent name when name = other_alias -> right_projection
    | EIdent name -> variable name
    | EField (base, field) -> field_access (translate_for_join base) field
    | EInt n -> int_const n
    | EBool b -> bool_const b
    | EString s -> string_const s
    | ERecord fs -> record (L.map (fun (k, v) -> (k, translate_for_join v)) fs)
    | EBinop (op, left, right) ->
        let op_name = match left, right with
          | EString _, _ | _, EString _ -> disambiguate_for_strings op
          | _ -> op
        in
        binary_application (variable op_name) (translate_for_join left) (translate_for_join right)
    | ECall (fn, [arg]) when lowercase fn = "count" ->
        let coll_ir, elem_ty = resolve_collection catalog env (Some from_alias) arg in
        let unit_mapper = lambda ~param:"_" ~param_ty:elem_ty ~body:unit_const in
        count (map unit_mapper coll_ir)
    | ECall (fn, [EIdent param; coll; pred]) when lowercase fn = "filter" ->
        let coll_ir, elem_ty = resolve_collection catalog env (Some from_alias) coll in
        let rec trans_pred = function
          | EIdent n when n = param -> variable param
          | EField (e, a) -> field_access (trans_pred e) a
          | ERecord fs -> record (L.map (fun (k, v) -> (k, trans_pred v)) fs)
          | EBinop (op, l, r) ->
              let op_name = match l, r with
                | EString _, _ | _, EString _ -> disambiguate_for_strings op
                | _ -> op
              in
              binary_application (variable op_name) (trans_pred l) (trans_pred r)
          | ECall (f, args) ->
              L.fold_left (fun acc a -> application acc (trans_pred a)) (variable f) args
          | other -> translate_for_join other
        in
        where (lambda ~param ~param_ty:elem_ty ~body:(trans_pred pred)) coll_ir
    | ECall (fn, [pred; coll]) when lowercase fn = "filter" ->
        let coll_ir, elem_ty = resolve_collection catalog env (Some from_alias) coll in
        let fresh = from_env ~avoid:[from_alias] env "y" in
        let rec trans_pred = function
          | EIdent n when n = fresh -> variable fresh
          | EField (e, a) -> field_access (trans_pred e) a
          | ERecord fs -> record (L.map (fun (k, v) -> (k, trans_pred v)) fs)
          | EBinop (op, l, r) ->
              let op_name = match l, r with
                | EString _, _ | _, EString _ -> disambiguate_for_strings op
                | _ -> op
              in
              binary_application (variable op_name) (trans_pred l) (trans_pred r)
          | ECall (f, args) ->
              L.fold_left (fun acc a -> application acc (trans_pred a)) (variable f) args
          | other -> translate_for_join other
        in
        where (lambda ~param:fresh ~param_ty:elem_ty ~body:(trans_pred pred)) coll_ir
    | ECall (fn, args) ->
        L.fold_left (fun acc arg -> application acc (translate_for_join arg)) (variable fn) args
  in
  
  let field_types =
    L.map (fun (name, expr) ->
      match infer_expression_type env expr with
      | Some ty -> (name, ty)
      | None -> (name, Ty.TString)
    ) fields
  in
  let body_record = record (L.map (fun (k, v) -> (k, translate_for_join v)) fields) in
  let new_row_ty = record_type (coq_list_of_ocaml_list 
    (fun (k, ty) -> coq_pair (coq_of_string k, ty)) field_types) in
  let mapper = lambda ~param:pair_param ~param_ty:row_ty ~body:body_record in
  (map mapper current_ir, with_row_type env new_row_ty)

and translate_group_by catalog env from_alias key_expr aggregates current_ir row_ty =
  let key_ty = match infer_expression_type env key_expr with
    | Some ty -> ty
    | None -> Ty.TInt
  in
  
  let key_lambda = match row_ty with
    | Ty.TProd _ ->
        let other_alias =
          L.find_map (fun (name, _) ->
            if name <> row_type_marker && name <> from_alias then Some name else None
          ) env
          |> Option.value ~default:from_alias
        in
        let pair_param = "row" in
        let left_proj = fst_projection (variable pair_param) in
        let right_proj = snd_projection (variable pair_param) in
        let rec trans = function
          | EIdent name when name = from_alias -> left_proj
          | EIdent name when name = other_alias -> right_proj
          | EIdent name -> variable name
          | EField (base, field) -> field_access (trans base) field
          | EInt n -> int_const n
          | EBool b -> bool_const b
          | EString s -> string_const s
          | ERecord fs -> record (L.map (fun (k, v) -> (k, trans v)) fs)
          | EBinop (op, left, right) ->
              let op_name = match left, right with
                | EString _, _ | _, EString _ -> disambiguate_for_strings op
                | _ -> op
              in
              binary_application (variable op_name) (trans left) (trans right)
          | ECall (fn, args) ->
              L.fold_left (fun acc arg -> application acc (trans arg)) (variable fn) args
        in
        lambda ~param:pair_param ~param_ty:row_ty ~body:(trans key_expr)
    | _ ->
        lambda ~param:from_alias ~param_ty:row_ty 
          ~body:(translate_expr catalog env (Some from_alias) key_expr)
  in
  
  let grouped_ir = group_by key_lambda current_ir in
  
  let agg_field_types =
    L.map (fun (agg : agg) -> 
      (agg.out, infer_aggregate_type agg.fn agg.args env)) aggregates
  in
  
  let result_body =
    let make_agg_field (agg : agg) =
      match lowercase agg.fn with
      | "count" | "max" | "min" | "sum" | "avg" -> 
          (agg.out, int_const 0)
      | _ -> (agg.out, int_const 0)
    in
    record (L.map make_agg_field aggregates)
  in
  
  let pair_ty = product_type key_ty (bag_type row_ty) in
  let result_mapper = lambda ~param:"z" ~param_ty:pair_ty ~body:result_body in
  let mapped_ir = map result_mapper grouped_ir in
  
  let new_row_ty = record_type (coq_list_of_ocaml_list 
    (fun (k, ty) -> coq_pair (coq_of_string k, ty)) agg_field_types) in
  (mapped_ir, with_row_type env new_row_ty)

and translate_distinct current_ir row_ty env =
  let identity_lambda = lambda ~param:"row" ~param_ty:row_ty ~body:(variable "row") in
  let grouped_ir = group_by identity_lambda current_ir in
  
  let pair_ty = product_type row_ty (bag_type row_ty) in
  let extract_key = lambda ~param:"z" ~param_ty:pair_ty ~body:(fst_projection (variable "z")) in
  let distinct_ir = map extract_key grouped_ir in
  (distinct_ir, env)

and translate_join catalog env from_alias alias2 source2_raw on_expr current_ir left_ty =
  let source2_name = extract_source_name source2_raw in
  let right_ty = find_source_type catalog source2_name in
  let right_ir = scan source2_name in
  
  require_boolean "join/on" ((alias2, right_ty) :: env) on_expr;
  
  let pair_param = "z" in
  let pair_ty = product_type left_ty right_ty in
  let left_proj = fst_projection (variable pair_param) in
  let right_proj = snd_projection (variable pair_param) in
  
  let rec translate_on = function
    | EIdent name when name = from_alias -> left_proj
    | EIdent name when name = alias2 -> right_proj
    | EIdent name -> variable name
    | EField (base, field) -> field_access (translate_on base) field
    | EInt n -> int_const n
    | EBool b -> bool_const b
    | EString s -> string_const s
    | ERecord fs -> record (L.map (fun (k, v) -> (k, translate_on v)) fs)
    | EBinop (op, left, right) ->
        let op_name = match left, right with
          | EString _, _ | _, EString _ -> disambiguate_for_strings op
          | _ -> op
        in
        binary_application (variable op_name) (translate_on left) (translate_on right)
    | ECall (fn, args) ->
        L.fold_left (fun acc arg -> application acc (translate_on arg)) (variable fn) args
  in
  
  let theta_lambda = lambda ~param:pair_param ~param_ty:pair_ty ~body:(translate_on on_expr) in
  let joined_ir = join theta_lambda current_ir right_ir in
  let new_env = with_row_type ((alias2, right_ty) :: env) pair_ty in
  (joined_ir, new_env)

(* ====================================================================== *)
(* Main query translation                                                 *)
(* ====================================================================== *)

type translation_env = { catalog : (String.string * Ty.ty) list }

let translate_query env query =
  let source_name = extract_source_name query.from_source in
  let row_ty = find_source_type env.catalog source_name in
  let initial_ir = scan source_name in
  
  let initial_env = with_row_type [(query.from_id, row_ty)] row_ty in
  
  let translate_one_stage acc_state stage =
    translate_stage env.catalog acc_state query.from_id stage
  in
  
  let final_ir, _ = L.fold_left translate_one_stage (initial_ir, initial_env) query.stages in
  final_ir

(* ====================================================================== *)
(* Public API                                                             *)
(* ====================================================================== *)

let of_query ~catalog query =
  translate_query { catalog } query