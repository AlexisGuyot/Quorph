(* algo/AlgoTyping.v *)
From Coq Require Import String List ZArith Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Quorph.Impl Require Import Types Term Typing.

Module AlgoTyping.
Import Types Term Typing.

(* ------------------------------------------------------------------ *)
(* Result minimal *)

Inductive result (A:Type) : Type :=
| Ok (a:A)
| Err (msg:string).
Arguments Ok {A}.
Arguments Err {A}.

Definition env := list (string * ty).
Definition catalog := list (string * ty).

(* ------------------------------------------------------------------ *)
(* Utilitaires *)

Fixpoint lookup {A} (x:string) (g:list (string*A)) : option A :=
  match g with
  | [] => None
  | (y,t)::g' => if String.eqb x y then Some t else lookup x g'
  end.

Fixpoint in_fields (a:string) (sch:list (string*ty)) : bool :=
  match sch with
  | [] => false
  | (b,_)::sch' => if String.eqb a b then true else in_fields a sch'
  end.

Fixpoint filter_schema (fs:list string) (sch:list (string*ty)) : list (string*ty) :=
  match sch with
  | [] => []
  | p::sch' =>
      let a := fst p in
      let t := snd p in
      if existsb (fun x => String.eqb a x) fs
      then (a,t)::filter_schema fs sch'
      else filter_schema fs sch'
  end.

Definition KappaEqb (k1 k2:kappa) : bool :=
  match k1, k2 with
  | kBag, kBag => true
  | kSet, kSet => true
  | _, _ => false
  end.

Fixpoint TyEqb (t1 t2:ty) : bool :=
  match t1, t2 with
  | TUnit, TUnit => true
  | TBool, TBool => true
  | TInt,  TInt  => true
  | TString, TString => true
  | TProd a1 b1, TProd a2 b2 => TyEqb a1 a2 && TyEqb b1 b2
  | TSum  a1 b1, TSum  a2 b2 => TyEqb a1 a2 && TyEqb b1 b2
  | TOption a1,  TOption a2  => TyEqb a1 a2
  | TArrow  a1 b1, TArrow  a2 b2 => TyEqb a1 a2 && TyEqb b1 b2
  | TColl k1 a1,  TColl k2 a2  => KappaEqb k1 k2 && TyEqb a1 a2
  | TRecord fs1,  TRecord fs2  =>
      let fix eq_fields l1 l2 :=
        match l1, l2 with
        | [], [] => true
        | h1::r1, h2::r2 =>
            let a1 := fst h1 in let u1 := snd h1 in
            let a2 := fst h2 in let u2 := snd h2 in
            String.eqb a1 a2 && TyEqb u1 u2 && eq_fields r1 r2
        | _, _ => false
        end
      in eq_fields fs1 fs2
  | _, _ => false
  end.

(* Helpers très simples pour du debug (types courts) *)
Definition show_ty (t:Types.ty) : string :=
  match t with
  | Types.TInt => "Int"
  | Types.TBool => "Bool"
  | Types.TString => "String"
  | Types.TUnit => "Unit"
  | Types.TArrow _ _ => "Arrow"
  | Types.TSum _ _ => "Sum"
  | Types.TProd _ _ => "Prod"
  | Types.TOption _ => "Option"
  | Types.TRecord _ => "Record"
  | Types.TColl κ _ =>
      match κ with
      | Types.kBag => "Coll(Bag, _)"
      | Types.kSet => "Coll(Set, _)"
      (* | Types.KList => "Coll(List, _)" *)
      end
  end.

Definition show_head (e:Term.expr) : string :=
  match e with
  | Term.EVar x => "var:" ++ x
  | Term.EProj _ lbl => "proj:." ++ lbl
  | Term.EApp (Term.EVar x) _ => "call:" ++ x
  | Term.EApp _ _ => "app"
  | Term.ELam _ _ _ => "lam"
  | Term.ECount _ => "count"
  | Term.EWhere _ _ => "where"
  | Term.EMap _ _ => "map"
  | _ => "expr"
  end.

(* ------------------------------------------------------------------ *)
(* Typechecker — un seul Fixpoint, décroissance sur [e] *)

Fixpoint typecheck (Σ:catalog) (Γ:env) (e:expr) {struct e} : result ty :=
  match e with
  | EVar x =>
      match lookup x Γ with
      | Some τ => Ok τ | None => Err ("unbound var: " ++ x) end

  | EConstUnit   => Ok TUnit
  | EConstBool _ => Ok TBool
  | EConstInt  _ => Ok TInt
  | EConstString _ => Ok TString

  | ERecord fs =>
      (* petit fix local, décroissant sur la liste [fs] *)
      let fix loop l :=
        match l with
        | [] => Ok ([] : list (string*ty))
        | p::l' =>
            let a := fst p in
            let ex := snd p in
            match typecheck Σ Γ ex with
            | Ok τ =>
                match loop l' with
                | Ok τs => Ok ((a,τ)::τs)
                | Err m => Err m
                end
            | Err m => Err m
            end
        end in
      match loop fs with
      | Ok τs => Ok (TRecord τs)
      | Err m => Err m
      end

  | EProj e1 a =>
      match typecheck Σ Γ e1 with
      | Ok (TRecord sch) =>
          match lookup a sch with
          | Some τ => Ok τ | None => Err ("unknown field: " ++ a)
          end
      | Ok _   => Err "projection on non-record"
      | Err m  => Err m
      end

  | EPair e1 e2 =>
      match typecheck Σ Γ e1 with
      | Ok τ =>
          match typecheck Σ Γ e2 with
          | Ok σ => Ok (TProd τ σ)
          | Err m => Err m
          end
      | Err m => Err m
      end

  | EInl _ => Err "inl requires an annotated target sum type"
  | EInr _ => Err "inr requires an annotated target sum type"

  | EFst e =>
    match typecheck Σ Γ e with
    | Ok (TProd τ σ) => Ok τ
    | Ok _           => Err "fst expects a product"
    | Err msg        => Err msg
    end

  | ESnd e =>
    match typecheck Σ Γ e with
    | Ok (TProd τ σ) => Ok σ
    | Ok _           => Err "snd expects a product"
    | Err msg        => Err msg
    end

  | ESome e1 =>
      match typecheck Σ Γ e1 with
      | Ok τ => Ok (TOption τ) | Err m => Err m end
  | ENone => Err "none requires an annotated option type"

  | ELam x τ body =>
      match typecheck Σ ((x,τ)::Γ) body with
      | Ok σ => Ok (TArrow τ σ) | Err m => Err m end

  (* | EApp f a1 =>
      match typecheck Σ Γ f with
      | Ok (TArrow τ σ) =>
          match typecheck Σ Γ a1 with
          | Ok τ' => if TyEqb τ τ' then Ok σ else Err "app: arg type mismatch"
          | Err m => Err m
          end
      | Ok _  => Err "app: function not of arrow type"
      | Err m => Err m
      end *)
    | Term.EApp f a =>
        match typecheck Σ Γ f, typecheck Σ Γ a with
        | Ok (Types.TArrow tparam tret), Ok targ =>
            if TyEqb tparam targ then Ok tret
            else Err
            ("app: arg type mismatch {fun=" ++ show_head f
            ++ "; expected=" ++ show_ty tparam
            ++ "; got=" ++ show_ty targ ++ "}")
        | Ok tfun, Ok _ =>
            Err ("app: not a function {fun=" ++ show_head f
                ++ "; type=" ++ show_ty tfun ++ "}")
        | Err m, _ => Err m
        | _, Err m => Err m
        end

  | EScan r =>
      match lookup r Σ with
      | Some τR => Ok (TColl kBag τR)
      | None    => Err ("unknown relation: " ++ r)
      end

  | EMap f c =>
      match typecheck Σ Γ c with
      | Ok (TColl κ τ) =>
          match typecheck Σ Γ f with
          | Ok (TArrow τ' σ) =>
              if TyEqb τ τ' then Ok (TColl κ σ) else Err "map: f arg mismatch"
          | Ok _  => Err "map: f not arrow"
          | Err m => Err m
          end
      | Ok _  => Err "map: input not a collection"
      | Err m => Err m
      end

  | EWhere p c =>
      match typecheck Σ Γ c with
      | Ok (TColl κ τ) =>
          match typecheck Σ Γ p with
          | Ok (TArrow τ' TBool) =>
              if TyEqb τ τ' then Ok (TColl κ τ) else Err "where: predicate arg mismatch"
          | Ok _  => Err "where: predicate not τ→Bool"
          | Err m => Err m
          end
      | Ok _  => Err "where: input not a collection"
      | Err m => Err m
      end

  | EFlatten c =>
      match typecheck Σ Γ c with
      | Ok (TColl κ (TColl κ' τ)) =>
          if KappaEqb κ κ' then Ok (TColl κ τ) else Err "flatten: mismatched κ"
      | Ok _  => Err "flatten: not Coll (Coll τ)"
      | Err m => Err m
      end

  | EProject fs c =>
      match typecheck Σ Γ c with
      | Ok (TColl κ (TRecord sch)) =>
          if forallb (fun a => in_fields a sch) fs
          then Ok (TColl κ (TRecord (filter_schema fs sch)))
          else Err "project: unknown field(s)"
      | Ok _  => Err "project: input not Coll Record"
      | Err m => Err m
      end

  | EJoin θ c1 c2 =>
      match typecheck Σ Γ c1 with
      | Ok (TColl κ τ) =>
          match typecheck Σ Γ c2 with
          | Ok (TColl κ' σ) =>
              if negb (KappaEqb κ κ') then Err "join: mismatched κ" else
              match typecheck Σ Γ θ with
              | Ok (TArrow (TProd τ1 σ1) TBool) =>
                  if TyEqb τ τ1 && TyEqb σ σ1
                  then Ok (TColl κ (TProd τ σ))
                  else Err "join: theta arg mismatch"
              | Ok _  => Err "join: theta not (τ×σ)→Bool"
              | Err m => Err m
              end
          | Ok _  => Err "join: right not collection"
          | Err m => Err m
          end
      | Ok _  => Err "join: left not collection"
      | Err m => Err m
      end

  | ESemiJoinL _ _ _
  | EAntiJoinL _ _ _
  | ESemiJoinR _ _ _
  | EAntiJoinR _ _ _
  | ELeftOuter _ _ _
  | ERightOuter _ _ _
  | EFullOuter _ _ _ =>
      Err "outer/semi/anti joins: NYI in algo checker"

  | EUnionAll u v =>
      match typecheck Σ Γ u with
      | Ok (TColl κ τ) =>
          match typecheck Σ Γ v with
          | Ok (TColl κ' τ') =>
              if KappaEqb κ κ' && TyEqb τ τ' then Ok (TColl κ τ)
              else Err "unionAll: type mismatch"
          | Ok _  => Err "unionAll: right not collection"
          | Err m => Err m
          end
      | Ok _  => Err "unionAll: left not collection"
      | Err m => Err m
      end

  | EUnion u v =>
      match typecheck Σ Γ u with
      | Ok (TColl _ τ) =>
          match typecheck Σ Γ v with
          | Ok (TColl _ τ') =>
              if TyEqb τ τ' then Ok (TColl kSet τ) else Err "union: element type mismatch"
          | Ok _  => Err "union: right not collection"
          | Err m => Err m
          end
      | Ok _  => Err "union: left not collection"
      | Err m => Err m
      end

  | EDistinct c =>
      match typecheck Σ Γ c with
      | Ok (TColl kBag τ) => Ok (TColl kSet τ)
      | Ok (TColl kSet τ) => Ok (TColl kSet τ)
      | Ok _  => Err "distinct: input not a collection"
      | Err m => Err m
      end

  | EGroupBy k c =>
      match typecheck Σ Γ c with
      | Ok (TColl κ τ) =>
          match typecheck Σ Γ k with
          | Ok (TArrow τ' kty) =>
              if TyEqb τ τ' then Ok (TColl κ (TProd kty (TColl κ τ)))
              else Err "group_by: key arg mismatch"
          | Ok _  => Err "group_by: key not τ→K"
          | Err m => Err m
          end
      | Ok _  => Err "group_by: input not collection"
      | Err m => Err m
      end

  | EAggregate _ c =>
      match typecheck Σ Γ c with
      | Ok (TColl kBag _) => Ok (TRecord [])
      | Ok _  => Err "aggregate: requires bag input"
      | Err m => Err m
      end

  | EHaving psi g =>
      match typecheck Σ Γ g with
      | Ok (TColl κ (TProd kty bty)) =>
          match typecheck Σ Γ psi with
          | Ok (TArrow (TProd kty' bty') TBool) =>
              if TyEqb kty kty' && TyEqb bty bty'
              then Ok (TColl κ (TProd kty bty))
              else Err "having: predicate arg mismatch"
          | Ok _  => Err "having: predicate not (K×β)→Bool"
          | Err m => Err m
          end
      | Ok _  => Err "having: input not Coll (K×β)"
      | Err m => Err m
      end

  | EOrder k c =>
      match typecheck Σ Γ c with
      | Ok (TColl kBag τ) =>
          match typecheck Σ Γ k with
          | Ok (TArrow τ' (TRecord [])) =>
              if TyEqb τ τ' then Ok (TColl kBag τ)
              else Err "order: key arg mismatch"
          | Ok _  => Err "order: key not τ→{}"
          | Err m => Err m
          end
      | Ok _  => Err "order: requires bag input"
      | Err m => Err m
      end

  | ELimit n c =>
      match typecheck Σ Γ n with
      | Ok TInt =>
          match typecheck Σ Γ c with
          | Ok (TColl κ τ) => Ok (TColl κ τ)
          | Ok _  => Err "limit: input not a collection"
          | Err m => Err m
          end
      | Ok _  => Err "limit: n not int"
      | Err m => Err m
      end

    | ECount c =>
        match typecheck Σ Γ c with
        | Ok (TColl κ TUnit) => Ok TInt
        | Ok _               => Err "count: input not Coll κ Unit"
        | Err m              => Err m
        end
  end.

(* ------------------------------------------------------------------ *)
(* Correction — à prouver ensuite *)

Theorem typecheck_sound :
  forall Σ Γ e τ, typecheck Σ Γ e = Ok τ -> has_type Γ e τ.
Proof. Admitted.

End AlgoTyping.
