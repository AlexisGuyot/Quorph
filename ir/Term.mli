open BinNums
open Datatypes
open String

module Term :
 sig
  type expr =
  | EVar of string
  | EConstUnit
  | EConstBool of bool
  | EConstInt of coq_Z
  | EConstString of string
  | ERecord of (string, expr) prod list
  | EProj of expr * string
  | EFst of expr
  | ESnd of expr
  | EPair of expr * expr
  | EInl of expr
  | EInr of expr
  | ESome of expr
  | ENone
  | ELam of string * Types.Types.ty * expr
  | EApp of expr * expr
  | EScan of string
  | EMap of expr * expr
  | EWhere of expr * expr
  | EFlatten of expr
  | EProject of string list * expr
  | EJoin of expr * expr * expr
  | ESemiJoinL of expr * expr * expr
  | EAntiJoinL of expr * expr * expr
  | ESemiJoinR of expr * expr * expr
  | EAntiJoinR of expr * expr * expr
  | ELeftOuter of expr * expr * expr
  | ERightOuter of expr * expr * expr
  | EFullOuter of expr * expr * expr
  | EUnionAll of expr * expr
  | EUnion of expr * expr
  | EDistinct of expr
  | EGroupBy of expr * expr
  | EAggregate of string * expr
  | EHaving of expr * expr
  | EOrder of expr * expr
  | ELimit of expr * expr
  | ECount of expr

  val expr_rect :
    (string -> 'a1) -> 'a1 -> (bool -> 'a1) -> (coq_Z -> 'a1) -> (string ->
    'a1) -> ((string, expr) prod list -> 'a1) -> (expr -> 'a1 -> string ->
    'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
    expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> 'a1) -> 'a1 -> (string -> Types.Types.ty -> expr -> 'a1
    -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (string -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (expr -> 'a1 -> 'a1) -> (string list -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
    expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr
    -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
    expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr
    -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (string -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (expr -> 'a1 -> 'a1) -> expr -> 'a1

  val expr_rec :
    (string -> 'a1) -> 'a1 -> (bool -> 'a1) -> (coq_Z -> 'a1) -> (string ->
    'a1) -> ((string, expr) prod list -> 'a1) -> (expr -> 'a1 -> string ->
    'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
    expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> 'a1) -> 'a1 -> (string -> Types.Types.ty -> expr -> 'a1
    -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (string -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (expr -> 'a1 -> 'a1) -> (string list -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
    expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr
    -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
    expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr
    -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (string -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    'a1) -> (expr -> 'a1 -> 'a1) -> expr -> 'a1
 end
