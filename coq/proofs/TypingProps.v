From Coq Require Import String List.
Import ListNotations.
Open Scope string_scope.

From Quorph.Impl Require Import Types Term Typing.
Module TypingProps.
Import Types Term Typing.

Lemma weakening :
  forall Γ Γ' e τ,
    (forall x t, lookup x Γ = Some t -> lookup x Γ' = Some t) ->
    has_type Γ e τ ->
    has_type Γ' e τ.
Proof. Admitted.

Lemma substitution :
  forall Γ x σ e τ v,
    has_type ((x,σ)::Γ) e τ ->
    has_type Γ v σ ->
    has_type Γ (Term.EApp (Term.ELam x σ e) v) τ.
Proof. Admitted.

Lemma determinism :
  forall Γ e τ1 τ2,
    has_type Γ e τ1 -> has_type Γ e τ2 -> τ1 = τ2.
Proof. Admitted.

End TypingProps.
