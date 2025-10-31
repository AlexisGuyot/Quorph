From Coq Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module Types.

Inductive kappa := kBag | kSet.

Inductive ty : Type :=
| TUnit
| TBool
| TInt
| TString
| TProd (a b : ty)
| TSum  (a b : ty)
| TOption (a : ty)
| TArrow (a b : ty)
| TColl (k : kappa) (a : ty)
| TRecord (fs : list (string * ty)).

Definition fields (t:ty) : list string :=
  match t with
  | TRecord fs => map fst fs
  | _ => []
  end.

End Types.
