open BinNums
open Datatypes
open String

module Term =
 struct
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

  (** val expr_rect :
      (string -> 'a1) -> 'a1 -> (bool -> 'a1) -> (coq_Z -> 'a1) -> (string ->
      'a1) -> ((string, expr) prod list -> 'a1) -> (expr -> 'a1 -> string ->
      'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) ->
      (expr -> 'a1 -> 'a1) -> 'a1 -> (string -> Types.Types.ty -> expr -> 'a1
      -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (string -> 'a1) ->
      (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
      'a1) -> (expr -> 'a1 -> 'a1) -> (string list -> expr -> 'a1 -> 'a1) ->
      (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
      expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 ->
      'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr ->
      'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr ->
      'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr ->
      'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr ->
      'a1 -> 'a1) -> (string -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr
      -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1
      -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> expr -> 'a1 **)

  let rec expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 = function
  | EVar x -> f x
  | EConstUnit -> f0
  | EConstBool b -> f1 b
  | EConstInt n -> f2 n
  | EConstString s -> f3 s
  | ERecord fs -> f4 fs
  | EProj (e0, a) ->
    f5 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0) a
  | EFst e0 ->
    f6 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | ESnd e0 ->
    f7 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | EPair (e1, e2) ->
    f8 e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e1) e2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e2)
  | EInl e0 ->
    f9 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | EInr e0 ->
    f10 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | ESome e0 ->
    f11 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | ENone -> f12
  | ELam (x, arg_ty, body) ->
    f13 x arg_ty body
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 body)
  | EApp (f37, e0) ->
    f14 f37
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 f37) e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | EScan r -> f15 r
  | EMap (f37, c) ->
    f16 f37
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 f37) c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EWhere (p, c) ->
    f17 p
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 p) c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EFlatten c ->
    f18 c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EProject (fields, c) ->
    f19 fields c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EJoin (theta, c1, c2) ->
    f20 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ESemiJoinL (theta, c1, c2) ->
    f21 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EAntiJoinL (theta, c1, c2) ->
    f22 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ESemiJoinR (theta, c1, c2) ->
    f23 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EAntiJoinR (theta, c1, c2) ->
    f24 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ELeftOuter (theta, c1, c2) ->
    f25 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ERightOuter (theta, c1, c2) ->
    f26 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EFullOuter (theta, c1, c2) ->
    f27 theta
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EUnionAll (u, v) ->
    f28 u
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 u) v
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 v)
  | EUnion (u, v) ->
    f29 u
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 u) v
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 v)
  | EDistinct c ->
    f30 c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EGroupBy (k, c) ->
    f31 k
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 k) c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EAggregate (agg, c) ->
    f32 agg c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EHaving (psi, g) ->
    f33 psi
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 psi) g
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 g)
  | EOrder (k, c) ->
    f34 k
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 k) c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | ELimit (n, c) ->
    f35 n
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 n) c
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | ECount e0 ->
    f36 e0
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)

  (** val expr_rec :
      (string -> 'a1) -> 'a1 -> (bool -> 'a1) -> (coq_Z -> 'a1) -> (string ->
      'a1) -> ((string, expr) prod list -> 'a1) -> (expr -> 'a1 -> string ->
      'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) ->
      (expr -> 'a1 -> 'a1) -> 'a1 -> (string -> Types.Types.ty -> expr -> 'a1
      -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (string -> 'a1) ->
      (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
      'a1) -> (expr -> 'a1 -> 'a1) -> (string list -> expr -> 'a1 -> 'a1) ->
      (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
      expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 ->
      'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr ->
      'a1 -> expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr ->
      'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr ->
      'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 ->
      expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr ->
      'a1 -> 'a1) -> (string -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr
      -> 'a1 -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> 'a1) -> (expr -> 'a1
      -> expr -> 'a1 -> 'a1) -> (expr -> 'a1 -> 'a1) -> expr -> 'a1 **)

  let rec expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 = function
  | EVar x -> f x
  | EConstUnit -> f0
  | EConstBool b -> f1 b
  | EConstInt n -> f2 n
  | EConstString s -> f3 s
  | ERecord fs -> f4 fs
  | EProj (e0, a) ->
    f5 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0) a
  | EFst e0 ->
    f6 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | ESnd e0 ->
    f7 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | EPair (e1, e2) ->
    f8 e1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e1) e2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e2)
  | EInl e0 ->
    f9 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | EInr e0 ->
    f10 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | ESome e0 ->
    f11 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | ENone -> f12
  | ELam (x, arg_ty, body) ->
    f13 x arg_ty body
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 body)
  | EApp (f37, e0) ->
    f14 f37
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 f37) e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
  | EScan r -> f15 r
  | EMap (f37, c) ->
    f16 f37
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 f37) c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EWhere (p, c) ->
    f17 p
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 p) c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EFlatten c ->
    f18 c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EProject (fields, c) ->
    f19 fields c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EJoin (theta, c1, c2) ->
    f20 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ESemiJoinL (theta, c1, c2) ->
    f21 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EAntiJoinL (theta, c1, c2) ->
    f22 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ESemiJoinR (theta, c1, c2) ->
    f23 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EAntiJoinR (theta, c1, c2) ->
    f24 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ELeftOuter (theta, c1, c2) ->
    f25 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | ERightOuter (theta, c1, c2) ->
    f26 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EFullOuter (theta, c1, c2) ->
    f27 theta
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 theta) c1
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c1) c2
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c2)
  | EUnionAll (u, v) ->
    f28 u
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 u) v
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 v)
  | EUnion (u, v) ->
    f29 u
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 u) v
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 v)
  | EDistinct c ->
    f30 c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EGroupBy (k, c) ->
    f31 k
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 k) c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EAggregate (agg, c) ->
    f32 agg c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | EHaving (psi, g) ->
    f33 psi
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 psi) g
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 g)
  | EOrder (k, c) ->
    f34 k
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 k) c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | ELimit (n, c) ->
    f35 n
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 n) c
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 c)
  | ECount e0 ->
    f36 e0
      (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        f34 f35 f36 e0)
 end
