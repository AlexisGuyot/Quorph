open Datatypes
open String

module AlgoTyping :
 sig
  type 'a result =
  | Ok of 'a
  | Err of string

  type env = (string, Types.Types.ty) prod list

  type catalog = (string, Types.Types.ty) prod list

  val lookup : string -> (string, 'a1) prod list -> 'a1 option

  val in_fields : string -> (string, Types.Types.ty) prod list -> bool

  val filter_schema :
    string list -> (string, Types.Types.ty) prod list -> (string,
    Types.Types.ty) prod list

  val coq_KappaEqb : Types.Types.kappa -> Types.Types.kappa -> bool

  val coq_TyEqb : Types.Types.ty -> Types.Types.ty -> bool

  val show_ty : Types.Types.ty -> string

  val show_head : Term.Term.expr -> string

  val typecheck : catalog -> env -> Term.Term.expr -> Types.Types.ty result
 end
