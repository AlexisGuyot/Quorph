From Coq Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Quorph.Impl Require Import Types.

Module Term.
Import Types.

Inductive expr : Type :=
| EVar   (x:string)
| EConstUnit
| EConstBool (b:bool)
| EConstInt  (n:Z)
| EConstString (s:string)
| ERecord (fs:list (string * expr))
| EProj   (e:expr) (a:string)
| EFst : expr -> expr
| ESnd : expr -> expr
| EPair   (e1 e2:expr)
| EInl    (e:expr) | EInr (e:expr)
| ESome   (e:expr) | ENone
| ELam    (x:string) (arg_ty:ty) (body:expr)
| EApp    (f e:expr)
| EScan   (R:string)
| EMap    (f:expr) (c:expr)
| EWhere  (p:expr) (c:expr)
| EFlatten (c:expr)
| EProject (fields:list string) (c:expr)
| EJoin   (theta:expr) (c1 c2:expr)
| ESemiJoinL (theta:expr) (c1 c2:expr)
| EAntiJoinL (theta:expr) (c1 c2:expr)
| ESemiJoinR (theta:expr) (c1 c2:expr)
| EAntiJoinR (theta:expr) (c1 c2:expr)
| ELeftOuter  (theta:expr) (c1 c2:expr)
| ERightOuter (theta:expr) (c1 c2:expr)
| EFullOuter  (theta:expr) (c1 c2:expr)
| EUnionAll (u v:expr)
| EUnion    (u v:expr)
| EDistinct (c:expr)
| EGroupBy (k:expr) (c:expr)
| EAggregate (agg:string) (c:expr)
| EHaving (psi:expr) (g:expr)
| EOrder (k:expr) (c:expr)
| ELimit (n:expr) (c:expr)
| ECount  : expr -> expr.

End Term.
