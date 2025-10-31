From Coq Require Import List.
Import ListNotations.
Module MonadBag.
Definition M (A:Type) := list A.
Definition ret {A}(a:A) : M A := [a].
Definition bind {A B}(ma:M A)(f:A->M B) : M B := concat (map f ma).
End MonadBag.
