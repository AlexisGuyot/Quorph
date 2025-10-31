From Coq Require Import String List ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Quorph.Impl Require Import Types.
Module SemanticsSig.
Import Types.

Parameter J : ty -> Type.

Parameter T : kappa -> Type -> Type.

Parameter ret : forall {k A}, A -> T k A.
Parameter bind : forall {k A B}, T k A -> (A -> T k B) -> T k B.

Parameter tmap : forall {k A B}, (A -> B) -> T k A -> T k B.
Parameter tconcat : forall {k A}, T k (T k A) -> T k A.

Axiom tmap_bind : forall k A B (f:A->B) (ma:T k A) (g:B->T k A),
  bind (tmap f ma) g = bind ma (fun a => g (f a)).

Definition JOption (A:Type) := option A.

Parameter JUnit : J TUnit = unit.
Parameter JBool : J TBool = bool.
Parameter JInt  : J TInt  = Z.
Parameter JString : J TString = string.

Parameter JProd : forall a b, J (TProd a b) = (J a * J b)%type.
Parameter JSum  : forall a b, J (TSum a b) = sum (J a) (J b).
Parameter JOption_t : forall a, J (TOption a) = option (J a).
Parameter JArrow : forall a b, J (TArrow a b) = (J a -> J b).
Parameter JColl   : forall k a, J (TColl k a) = T k (J a).

Parameter JRecord : forall fs, J (TRecord fs) : Type.

End SemanticsSig.
