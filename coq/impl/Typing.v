From Coq Require Import String List ZArith Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Quorph.Impl Require Import Types Term.
Module Typing.
Import Types Term.

Definition env := list (string * ty).

Fixpoint lookup (x:string) (Γ:env) : option ty :=
  match Γ with
  | [] => None
  | (y,t)::Γ' => if String.eqb x y then Some t else lookup x Γ'
  end.

Fixpoint in_fields (a:string) (I:list (string*ty)) : bool :=
  match I with
  | [] => false
  | (b,_)::I' => if String.eqb a b then true else in_fields a I'
  end.

Inductive has_type : env -> Term.expr -> ty -> Prop :=
| T_Var Γ x τ :
    lookup x Γ = Some τ -> has_type Γ (EVar x) τ
| T_Unit Γ : has_type Γ EConstUnit TUnit
| T_Bool Γ b : has_type Γ (EConstBool b) TBool
| T_Int Γ n : has_type Γ (EConstInt n) TInt
| T_String Γ s : has_type Γ (EConstString s) TString
| T_Record Γ fs τs :
    (forall a e τ, In (a,e) fs -> In (a,τ) τs -> has_type Γ e τ) ->
    has_type Γ (ERecord fs) (TRecord τs)
| T_Proj Γ e a fs τ :
    has_type Γ e (TRecord fs) -> In (a,τ) fs -> has_type Γ (EProj e a) τ
| T_Pair Γ e1 e2 τ σ :
    has_type Γ e1 τ -> has_type Γ e2 σ -> has_type Γ (EPair e1 e2) (TProd τ σ)
| T_Inl Γ e τ σ :
    has_type Γ e τ -> has_type Γ (EInl e) (TSum τ σ)
| T_Inr Γ e τ σ :
    has_type Γ e σ -> has_type Γ (EInr e) (TSum τ σ)
| T_Fst : forall Γ e τ σ,
    has_type Γ e (TProd τ σ) ->
    has_type Γ (EFst e) τ
| T_Snd : forall Γ e τ σ,
    has_type Γ e (TProd τ σ) ->
    has_type Γ (ESnd e) σ
| T_Some Γ e τ :
    has_type Γ e τ -> has_type Γ (ESome e) (TOption τ)
| T_None Γ τ :
    has_type Γ ENone (TOption τ)
| T_Lam Γ x τ σ body :
    has_type ((x,τ)::Γ) body σ -> has_type Γ (ELam x τ body) (TArrow τ σ)
| T_App Γ f e τ σ :
    has_type Γ f (TArrow τ σ) -> has_type Γ e τ -> has_type Γ (EApp f e) σ
| T_Scan Γ R τR :
    has_type Γ (EScan R) (TColl kBag τR)
| T_Map Γ f c τ σ κ :
    has_type Γ c (TColl κ τ) -> has_type Γ f (TArrow τ σ) -> has_type Γ (EMap f c) (TColl κ σ)
| T_Where Γ p c τ κ :
    has_type Γ c (TColl κ τ) -> has_type Γ p (TArrow τ TBool) -> has_type Γ (EWhere p c) (TColl κ τ)
| T_Flatten Γ c τ κ :
    has_type Γ c (TColl κ (TColl κ τ)) -> has_type Γ (EFlatten c) (TColl κ τ)
| T_Project Γ c fs I κ :
    has_type Γ c (TColl κ (TRecord I)) ->
    Forall (fun a => in_fields a I = true) fs ->
    has_type Γ
      (EProject fs c)
      (TColl κ (TRecord (filter (fun p => existsb (fun x => String.eqb (fst p) x) fs) I)))
| T_Join Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (EJoin θ c1 c2) (TColl κ (TProd τ σ))
| T_SemiL Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (ESemiJoinL θ c1 c2) (TColl κ τ)
| T_AntiL Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (EAntiJoinL θ c1 c2) (TColl κ τ)
| T_SemiR Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (ESemiJoinR θ c1 c2) (TColl κ σ)
| T_AntiR Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (EAntiJoinR θ c1 c2) (TColl κ σ)
| T_LeftOuter Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (ELeftOuter θ c1 c2) (TColl κ (TProd τ (TOption σ)))
| T_RightOuter Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (ERightOuter θ c1 c2) (TColl κ (TProd (TOption τ) σ))
| T_FullOuter Γ θ c1 c2 τ σ κ :
    has_type Γ c1 (TColl κ τ) -> has_type Γ c2 (TColl κ σ) ->
    has_type Γ θ (TArrow (TProd τ σ) TBool) ->
    has_type Γ (EFullOuter θ c1 c2) (TColl κ (TProd (TOption τ) (TOption σ)))
| T_UnionAll Γ u v τ κ :
    has_type Γ u (TColl κ τ) -> has_type Γ v (TColl κ τ) ->
    has_type Γ (EUnionAll u v) (TColl κ τ)
| T_Union Γ u v τ κ :
    has_type Γ u (TColl κ τ) -> has_type Γ v (TColl κ τ) ->
    has_type Γ (EUnion u v) (TColl kSet τ)
| T_Distinct Γ c τ :
    has_type Γ c (TColl kBag τ) -> has_type Γ (EDistinct c) (TColl kSet τ)
| T_GroupBy Γ k c τ K κ :
    has_type Γ c (TColl κ τ) -> has_type Γ k (TArrow τ K) ->
    has_type Γ (EGroupBy k c) (TColl κ (TProd K (TColl κ τ)))
| T_Aggregate Γ agg c τ :
    has_type Γ c (TColl kBag τ) ->
    has_type Γ (EAggregate agg c) (TRecord [])  (* placeholder α *)
| T_Having Γ psi g K β κ :
    has_type Γ g (TColl κ (TProd K β)) -> has_type Γ psi (TArrow (TProd K β) TBool) ->
    has_type Γ (EHaving psi g) (TColl κ (TProd K β))
| T_Order Γ k c τ :
    has_type Γ c (TColl kBag τ) -> has_type Γ k (TArrow τ (TRecord [])) ->
    has_type Γ (EOrder k c) (TColl kBag τ)
| T_Limit Γ n c τ κ :
    has_type Γ n TInt -> has_type Γ c (TColl κ τ) ->
    has_type Γ (ELimit n c) (TColl κ τ)
| T_Count Γ e κ :
    has_type Γ e (TColl κ TUnit) ->
    has_type Γ (ECount e) TInt.
End Typing.
