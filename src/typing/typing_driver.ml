(* src/typing/typing_driver.ml - Version refactorisée *)
open Ast_surface
open Coq_conversion
open Type_utils
open Operators

module Ty = Types.Types
module D = Datatypes
module AT = AlgoTyping.AlgoTyping
module Bridge = Coq_ast_bridge

module S = Stdlib.String

(* ====================================================================== *)
(* Prelude: Built-in operators and their types                           *)
(* ====================================================================== *)

let create_prelude () =
  let bool_ty = Ty.TBool and int_ty = Ty.TInt and string_ty = Ty.TString in
  let bag elem_ty = Ty.TColl (Ty.Coq_kBag, elem_ty) in
  
  [
    (* Logical operators *)
    (coq_of_string "and", binary_arrow_type bool_ty bool_ty bool_ty);
    (coq_of_string "or",  binary_arrow_type bool_ty bool_ty bool_ty);
    (coq_of_string "not", arrow_type bool_ty bool_ty);
    
    (* Integer comparisons *)
    (coq_of_string "=",  binary_arrow_type int_ty int_ty bool_ty);
    (coq_of_string "<>", binary_arrow_type int_ty int_ty bool_ty);
    (coq_of_string "<",  binary_arrow_type int_ty int_ty bool_ty);
    (coq_of_string "<=", binary_arrow_type int_ty int_ty bool_ty);
    (coq_of_string ">",  binary_arrow_type int_ty int_ty bool_ty);
    (coq_of_string ">=", binary_arrow_type int_ty int_ty bool_ty);
    
    (* String comparisons *)
    (coq_of_string "=s",  binary_arrow_type string_ty string_ty bool_ty);
    (coq_of_string "<>s", binary_arrow_type string_ty string_ty bool_ty);
    (coq_of_string "<s",  binary_arrow_type string_ty string_ty bool_ty);
    (coq_of_string "<=s", binary_arrow_type string_ty string_ty bool_ty);
    (coq_of_string ">s",  binary_arrow_type string_ty string_ty bool_ty);
    (coq_of_string ">=s", binary_arrow_type string_ty string_ty bool_ty);
    
    (* Aggregate functions *)
    (coq_of_string "min2", arrow_type (bag string_ty) string_ty);
    (coq_of_string "min",  arrow_type (bag int_ty) int_ty);
    (coq_of_string "max",  arrow_type (bag int_ty) int_ty);
    (coq_of_string "sum",  arrow_type (bag int_ty) int_ty);
    (coq_of_string "avg",  arrow_type (bag int_ty) int_ty);
    
    (* Higher-order helper *)
    (coq_of_string "filter",
      arrow_type
        (arrow_type string_ty bool_ty)
        (arrow_type (bag string_ty) (bag string_ty)));
  ]

(* ====================================================================== *)
(* Validation helpers                                                     *)
(* ====================================================================== *)

let rec validate_expression expr =
  match expr with
  | EBool _ | EInt _ | EString _ | EIdent _ -> Ok ()
  
  | EField (_, _) -> Ok ()
  
  | ERecord fields ->
      let rec validate_fields = function
        | [] -> Ok ()
        | (_, value) :: rest ->
            (match validate_expression value with
             | Ok () -> validate_fields rest
             | Error _ as err -> err)
      in
      validate_fields fields
  
  | EBinop (_, left, right) ->
      (match validate_expression left with
       | Ok () -> validate_expression right
       | Error _ as err -> err)
  
  | ECall (_, args) ->
      let rec validate_args = function
        | [] -> Ok ()
        | arg :: rest ->
            (match validate_expression arg with
             | Ok () -> validate_args rest
             | Error _ as err -> err)
      in
      validate_args args

let rec expression_looks_boolean expr =
  match expr with
  | EBool _ -> true
  | EField _ | EIdent _ -> true
  | EBinop (op, left, right) ->
      let op_lower = S.lowercase_ascii op in
      if op_lower = "and" || op_lower = "or" then
        expression_looks_boolean left && expression_looks_boolean right
      else if is_comparison_operator op then
        true
      else
        false
  | ECall (fn, [arg]) when S.lowercase_ascii fn = "not" ->
      expression_looks_boolean arg
  | _ -> false

let validate_stage stage =
  match stage with
  | Where predicate ->
      if expression_looks_boolean predicate then Ok ()
      else Error "Type error: WHERE predicate must be boolean"
  
  | Select fields ->
      let rec validate_fields = function
        | [] -> Ok ()
        | (_, expr) :: rest ->
            (match validate_expression expr with
             | Ok () -> validate_fields rest
             | Error _ as err -> err)
      in
      validate_fields fields
  
  | Group_by _ | Order_by _ | Limit _ | Distinct 
  | Union _ | Union_all _ | Join _ ->
      Ok ()

let precheck_query query =
  let rec validate_stages = function
    | [] -> Ok ()
    | stage :: rest ->
        (match validate_stage stage with
         | Ok () -> validate_stages rest
         | Error _ as err -> err)
  in
  validate_stages query.stages

(* ====================================================================== *)
(* Type checking                                                          *)
(* ====================================================================== *)

let typecheck_query query =
  match precheck_query query with
  | Error msg -> Error msg
  | Ok () ->
      try
        let ir_expr = Bridge.of_query ~catalog:Catalog.default query in
        let catalog_ir = coq_list_of_ocaml_list coq_pair Catalog.default in
        let env_ir = coq_list_of_ocaml_list coq_pair (create_prelude ()) in
        
        match AT.typecheck catalog_ir env_ir ir_expr with
        | AT.Ok _ -> Ok ()
        | AT.Err error_msg -> Error (string_of_coq error_msg)
      with
      | Failure msg -> Error msg
      | exn -> Error (Printexc.to_string exn)

(* ====================================================================== *)
(* Public API - Text-based                                                *)
(* ====================================================================== *)

let typecheck_text source =
  try
    let query = Simple_parser.parse source in
    typecheck_query query
  with
  | Simple_parser.Parse_error msg -> Error ("Parse error: " ^ msg)
  | Failure msg -> Error msg
  | exn -> Error (Printexc.to_string exn)

let type_of_text source =
  try
    let query = Simple_parser.parse source in
    match typecheck_query query with
    | Error msg -> Error msg
    | Ok () ->
        let ir_expr = Bridge.of_query ~catalog:Catalog.default query in
        let catalog_ir = coq_list_of_ocaml_list coq_pair Catalog.default in
        let env_ir = coq_list_of_ocaml_list coq_pair (create_prelude ()) in
        
        match AT.typecheck catalog_ir env_ir ir_expr with
        | AT.Ok result_ty -> Ok (pretty_print_type result_ty)
        | AT.Err error_msg -> Error (ocaml_string_of_coq error_msg)
  with
  | Simple_parser.Parse_error msg -> Error ("Parse error: " ^ msg)
  | Failure msg -> Error msg
  | exn -> Error (Printexc.to_string exn)

(* ====================================================================== *)
(* Public API - AST-based                                                 *)
(* ====================================================================== *)

let typecheck_pipeline query =
  typecheck_query query