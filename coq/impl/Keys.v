From Coq Require Import String List ZArith Program.Tactics.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module Keys.

Class TotalOrder (A:Type) := {
  leA : A -> A -> Prop;
  le_refl  : forall x, leA x x;
  le_trans : forall x y z, leA x y -> leA y z -> leA x z;
  le_antisym : forall x y, leA x y -> leA y x -> x = y;
  le_total : forall x y, leA x y \/ leA y x
}.

Program Instance TotalOrder_prod
  {A B} `{TotalOrder A} `{TotalOrder B} : TotalOrder (A*B) := { 
  leA '(a1,b1) '(a2,b2) := (leA a1 a2 /\ ~(leA a2 a1)) \/ (a1 = a2 /\ leA b1 b2)
}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Instance TotalOrder_sum
  {A B} `{TotalOrder A} `{TotalOrder B} : TotalOrder (sum A B) := {
  leA x y :=
    match x,y with
    | inl a1, inl a2 => leA a1 a2
    | inl _,  inr _  => True
    | inr b1, inr b2 => leA b1 b2
    | inr _,  inl _  => False
    end
}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

End Keys.
