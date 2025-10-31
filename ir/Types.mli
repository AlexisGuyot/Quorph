open Datatypes
open String

module Types :
 sig
  type kappa =
  | Coq_kBag
  | Coq_kSet

  type ty =
  | TUnit
  | TBool
  | TInt
  | TString
  | TProd of ty * ty
  | TSum of ty * ty
  | TOption of ty
  | TArrow of ty * ty
  | TColl of kappa * ty
  | TRecord of (string, ty) prod list
 end
