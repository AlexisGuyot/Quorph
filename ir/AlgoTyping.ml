open Ascii
open Datatypes
open List
open String

module AlgoTyping =
 struct
  type 'a result =
  | Ok of 'a
  | Err of string

  type env = (string, Types.Types.ty) prod list

  type catalog = (string, Types.Types.ty) prod list

  (** val lookup : string -> (string, 'a1) prod list -> 'a1 option **)

  let rec lookup x = function
  | Coq_nil -> None
  | Coq_cons (p, g') ->
    let Coq_pair (y, t) = p in
    (match eqb x y with
     | Coq_true -> Some t
     | Coq_false -> lookup x g')

  (** val in_fields : string -> (string, Types.Types.ty) prod list -> bool **)

  let rec in_fields a = function
  | Coq_nil -> Coq_false
  | Coq_cons (p, sch') ->
    let Coq_pair (b, _) = p in
    (match eqb a b with
     | Coq_true -> Coq_true
     | Coq_false -> in_fields a sch')

  (** val filter_schema :
      string list -> (string, Types.Types.ty) prod list -> (string,
      Types.Types.ty) prod list **)

  let rec filter_schema fs = function
  | Coq_nil -> Coq_nil
  | Coq_cons (p, sch') ->
    let a = fst p in
    let t = snd p in
    (match existsb (fun x -> eqb a x) fs with
     | Coq_true -> Coq_cons ((Coq_pair (a, t)), (filter_schema fs sch'))
     | Coq_false -> filter_schema fs sch')

  (** val coq_KappaEqb : Types.Types.kappa -> Types.Types.kappa -> bool **)

  let coq_KappaEqb k1 k2 =
    match k1 with
    | Types.Types.Coq_kBag ->
      (match k2 with
       | Types.Types.Coq_kBag -> Coq_true
       | Types.Types.Coq_kSet -> Coq_false)
    | Types.Types.Coq_kSet ->
      (match k2 with
       | Types.Types.Coq_kBag -> Coq_false
       | Types.Types.Coq_kSet -> Coq_true)

  (** val coq_TyEqb : Types.Types.ty -> Types.Types.ty -> bool **)

  let rec coq_TyEqb t1 t2 =
    match t1 with
    | Types.Types.TUnit ->
      (match t2 with
       | Types.Types.TUnit -> Coq_true
       | _ -> Coq_false)
    | Types.Types.TBool ->
      (match t2 with
       | Types.Types.TBool -> Coq_true
       | _ -> Coq_false)
    | Types.Types.TInt ->
      (match t2 with
       | Types.Types.TInt -> Coq_true
       | _ -> Coq_false)
    | Types.Types.TString ->
      (match t2 with
       | Types.Types.TString -> Coq_true
       | _ -> Coq_false)
    | Types.Types.TProd (a1, b1) ->
      (match t2 with
       | Types.Types.TProd (a2, b2) ->
         (match coq_TyEqb a1 a2 with
          | Coq_true -> coq_TyEqb b1 b2
          | Coq_false -> Coq_false)
       | _ -> Coq_false)
    | Types.Types.TSum (a1, b1) ->
      (match t2 with
       | Types.Types.TSum (a2, b2) ->
         (match coq_TyEqb a1 a2 with
          | Coq_true -> coq_TyEqb b1 b2
          | Coq_false -> Coq_false)
       | _ -> Coq_false)
    | Types.Types.TOption a1 ->
      (match t2 with
       | Types.Types.TOption a2 -> coq_TyEqb a1 a2
       | _ -> Coq_false)
    | Types.Types.TArrow (a1, b1) ->
      (match t2 with
       | Types.Types.TArrow (a2, b2) ->
         (match coq_TyEqb a1 a2 with
          | Coq_true -> coq_TyEqb b1 b2
          | Coq_false -> Coq_false)
       | _ -> Coq_false)
    | Types.Types.TColl (k1, a1) ->
      (match t2 with
       | Types.Types.TColl (k2, a2) ->
         (match coq_KappaEqb k1 k2 with
          | Coq_true -> coq_TyEqb a1 a2
          | Coq_false -> Coq_false)
       | _ -> Coq_false)
    | Types.Types.TRecord fs1 ->
      (match t2 with
       | Types.Types.TRecord fs2 ->
         let rec eq_fields l1 l2 =
           match l1 with
           | Coq_nil ->
             (match l2 with
              | Coq_nil -> Coq_true
              | Coq_cons (_, _) -> Coq_false)
           | Coq_cons (h1, r1) ->
             (match l2 with
              | Coq_nil -> Coq_false
              | Coq_cons (h2, r2) ->
                let a1 = fst h1 in
                let u1 = snd h1 in
                let a2 = fst h2 in
                let u2 = snd h2 in
                (match match eqb a1 a2 with
                       | Coq_true -> coq_TyEqb u1 u2
                       | Coq_false -> Coq_false with
                 | Coq_true -> eq_fields r1 r2
                 | Coq_false -> Coq_false))
         in eq_fields fs1 fs2
       | _ -> Coq_false)

  (** val show_ty : Types.Types.ty -> string **)

  let show_ty = function
  | Types.Types.TUnit ->
    String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)))))))
  | Types.Types.TBool ->
    String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_false,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))
  | Types.Types.TInt ->
    String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), EmptyString)))))
  | Types.Types.TString ->
    String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
      Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), EmptyString)))))))))))
  | Types.Types.TProd (_, _) ->
    String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      EmptyString)))))))
  | Types.Types.TSum (_, _) ->
    String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), EmptyString)))))
  | Types.Types.TOption _ ->
    String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), EmptyString)))))))))))
  | Types.Types.TArrow (_, _) ->
    String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), EmptyString)))))))))
  | Types.Types.TColl (_UU03ba_, _) ->
    (match _UU03ba_ with
     | Types.Types.Coq_kBag ->
       String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)),
         EmptyString)))))))))))))))))))))))
     | Types.Types.Coq_kSet ->
       String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)),
         EmptyString))))))))))))))))))))))))
  | Types.Types.TRecord _ ->
    String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      EmptyString)))))))))))

  (** val show_head : Term.Term.expr -> string **)

  let show_head = function
  | Term.Term.EVar x ->
    append (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
      Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false, Coq_false)), EmptyString)))))))) x
  | Term.Term.EProj (_, lbl) ->
    append (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
      Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
      Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
      Coq_false)), EmptyString)))))))))))) lbl
  | Term.Term.ELam (_, _, _) ->
    String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), EmptyString)))))
  | Term.Term.EApp (f, _) ->
    (match f with
     | Term.Term.EVar x ->
       append (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_false)), EmptyString)))))))))) x
     | _ ->
       String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))
  | Term.Term.EMap (_, _) ->
    String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), EmptyString)))))
  | Term.Term.EWhere (_, _) ->
    String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), EmptyString)))))))))
  | Term.Term.ECount _ ->
    String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), EmptyString)))))))))
  | _ ->
    String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      EmptyString)))))))

  (** val typecheck :
      catalog -> env -> Term.Term.expr -> Types.Types.ty result **)

  let rec typecheck _UU03a3_ _UU0393_ = function
  | Term.Term.EVar x ->
    (match lookup x _UU0393_ with
     | Some _UU03c4_ -> Ok _UU03c4_
     | None ->
       Err
         (append (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
           (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false)),
           EmptyString)))))))))))))))))))))))))) x))
  | Term.Term.EConstUnit -> Ok Types.Types.TUnit
  | Term.Term.EConstBool _ -> Ok Types.Types.TBool
  | Term.Term.EConstInt _ -> Ok Types.Types.TInt
  | Term.Term.EConstString _ -> Ok Types.Types.TString
  | Term.Term.ERecord fs ->
    let loop =
      let rec loop = function
      | Coq_nil -> Ok Coq_nil
      | Coq_cons (p, l') ->
        let a = fst p in
        let ex = snd p in
        (match typecheck _UU03a3_ _UU0393_ ex with
         | Ok _UU03c4_ ->
           (match loop l' with
            | Ok _UU03c4_s ->
              Ok (Coq_cons ((Coq_pair (a, _UU03c4_)), _UU03c4_s))
            | Err m -> Err m)
         | Err m -> Err m)
      in loop
    in
    (match loop fs with
     | Ok _UU03c4_s -> Ok (Types.Types.TRecord _UU03c4_s)
     | Err m -> Err m)
  | Term.Term.EProj (e1, a) ->
    (match typecheck _UU03a3_ _UU0393_ e1 with
     | Ok a0 ->
       (match a0 with
        | Types.Types.TRecord sch ->
          (match lookup a sch with
           | Some _UU03c4_ -> Ok _UU03c4_
           | None ->
             Err
               (append (String ((Ascii (Coq_true, Coq_false, Coq_true,
                 Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
                 Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)),
                 EmptyString)))))))))))))))))))))))))))))) a))
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EFst e0 ->
    (match typecheck _UU03a3_ _UU0393_ e0 with
     | Ok a ->
       (match a with
        | Types.Types.TProd (_UU03c4_, _) -> Ok _UU03c4_
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString)))))))))))))))))))))))))))))))))))))))))))
     | Err msg -> Err msg)
  | Term.Term.ESnd e0 ->
    (match typecheck _UU03a3_ _UU0393_ e0 with
     | Ok a ->
       (match a with
        | Types.Types.TProd (_, _UU03c3_) -> Ok _UU03c3_
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString)))))))))))))))))))))))))))))))))))))))))))
     | Err msg -> Err msg)
  | Term.Term.EPair (e1, e2) ->
    (match typecheck _UU03a3_ _UU0393_ e1 with
     | Ok _UU03c4_ ->
       (match typecheck _UU03a3_ _UU0393_ e2 with
        | Ok _UU03c3_ -> Ok (Types.Types.TProd (_UU03c4_, _UU03c3_))
        | Err m -> Err m)
     | Err m -> Err m)
  | Term.Term.EInl _ ->
    Err (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
      Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_false)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | Term.Term.EInr _ ->
    Err (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
      Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
      Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_false)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | Term.Term.ESome e1 ->
    (match typecheck _UU03a3_ _UU0393_ e1 with
     | Ok _UU03c4_ -> Ok (Types.Types.TOption _UU03c4_)
     | Err m -> Err m)
  | Term.Term.ENone ->
    Err (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | Term.Term.ELam (x, _UU03c4_, body) ->
    (match typecheck _UU03a3_ (Coq_cons ((Coq_pair (x, _UU03c4_)), _UU0393_))
             body with
     | Ok _UU03c3_ -> Ok (Types.Types.TArrow (_UU03c4_, _UU03c3_))
     | Err m -> Err m)
  | Term.Term.EApp (f, a) ->
    (match typecheck _UU03a3_ _UU0393_ f with
     | Ok tfun ->
       (match tfun with
        | Types.Types.TProd (_, _) ->
          (match typecheck _UU03a3_ _UU0393_ a with
           | Ok _ ->
             Err
               (append (String ((Ascii (Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
                 (Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_false)),
                 EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
                 (append (show_head f)
                   (append (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     EmptyString))))))))))))))
                     (append (show_ty tfun) (String ((Ascii (Coq_true,
                       Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                       Coq_true, Coq_false)), EmptyString))))))
           | Err m -> Err m)
        | Types.Types.TSum (_, _) ->
          (match typecheck _UU03a3_ _UU0393_ a with
           | Ok _ ->
             Err
               (append (String ((Ascii (Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
                 (Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_false)),
                 EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
                 (append (show_head f)
                   (append (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     EmptyString))))))))))))))
                     (append (show_ty tfun) (String ((Ascii (Coq_true,
                       Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                       Coq_true, Coq_false)), EmptyString))))))
           | Err m -> Err m)
        | Types.Types.TOption _ ->
          (match typecheck _UU03a3_ _UU0393_ a with
           | Ok _ ->
             Err
               (append (String ((Ascii (Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
                 (Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_false)),
                 EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
                 (append (show_head f)
                   (append (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     EmptyString))))))))))))))
                     (append (show_ty tfun) (String ((Ascii (Coq_true,
                       Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                       Coq_true, Coq_false)), EmptyString))))))
           | Err m -> Err m)
        | Types.Types.TArrow (tparam, tret) ->
          (match typecheck _UU03a3_ _UU0393_ a with
           | Ok targ ->
             (match coq_TyEqb tparam targ with
              | Coq_true -> Ok tret
              | Coq_false ->
                Err
                  (append (String ((Ascii (Coq_true, Coq_false, Coq_false,
                    Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                    (String ((Ascii (Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                    (String ((Ascii (Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                    (String ((Ascii (Coq_false, Coq_true, Coq_false,
                    Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                    (String ((Ascii (Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                    (String ((Ascii (Coq_true, Coq_false, Coq_false,
                    Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                    (String ((Ascii (Coq_false, Coq_true, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                    (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_false, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_false, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                    Coq_false, Coq_true, Coq_false, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_true, Coq_false, Coq_true,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                    Coq_true, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                    Coq_false, Coq_true, Coq_true, Coq_false)), (String
                    ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                    Coq_true, Coq_true, Coq_false, Coq_false)),
                    EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    (append (show_head f)
                      (append (String ((Ascii (Coq_true, Coq_true, Coq_false,
                        Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                        (String ((Ascii (Coq_false, Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
                        Coq_false)), EmptyString))))))))))))))))))))))
                        (append (show_ty tparam)
                          (append (String ((Ascii (Coq_true, Coq_true,
                            Coq_false, Coq_true, Coq_true, Coq_true,
                            Coq_false, Coq_false)), (String ((Ascii
                            (Coq_false, Coq_false, Coq_false, Coq_false,
                            Coq_false, Coq_true, Coq_false, Coq_false)),
                            (String ((Ascii (Coq_true, Coq_true, Coq_true,
                            Coq_false, Coq_false, Coq_true, Coq_true,
                            Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                            Coq_true, Coq_true, Coq_false, Coq_true,
                            Coq_true, Coq_false)), (String ((Ascii
                            (Coq_false, Coq_false, Coq_true, Coq_false,
                            Coq_true, Coq_true, Coq_true, Coq_false)),
                            (String ((Ascii (Coq_true, Coq_false, Coq_true,
                            Coq_true, Coq_true, Coq_true, Coq_false,
                            Coq_false)), EmptyString))))))))))))
                            (append (show_ty targ) (String ((Ascii (Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_true, Coq_true, Coq_false)), EmptyString)))))))))
           | Err m -> Err m)
        | Types.Types.TColl (_, _) ->
          (match typecheck _UU03a3_ _UU0393_ a with
           | Ok _ ->
             Err
               (append (String ((Ascii (Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
                 (Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_false)),
                 EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
                 (append (show_head f)
                   (append (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     EmptyString))))))))))))))
                     (append (show_ty tfun) (String ((Ascii (Coq_true,
                       Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                       Coq_true, Coq_false)), EmptyString))))))
           | Err m -> Err m)
        | _ ->
          (match typecheck _UU03a3_ _UU0393_ a with
           | Ok _ ->
             Err
               (append (String ((Ascii (Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                 Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                 Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                 (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                 Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                 Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
                 (Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                 Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                 Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                 Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                 (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                 Coq_true, Coq_true, Coq_false, Coq_false)),
                 EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
                 (append (show_head f)
                   (append (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     EmptyString))))))))))))))
                     (append (show_ty tfun) (String ((Ascii (Coq_true,
                       Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                       Coq_true, Coq_false)), EmptyString))))))
           | Err m -> Err m))
     | Err m -> Err m)
  | Term.Term.EScan r ->
    (match lookup r _UU03a3_ with
     | Some _UU03c4_R ->
       Ok (Types.Types.TColl (Types.Types.Coq_kBag, _UU03c4_R))
     | None ->
       Err
         (append (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
           (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
           (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
           EmptyString)))))))))))))))))))))))))))))))))))) r))
  | Term.Term.EMap (f, c) ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, _UU03c4_) ->
          (match typecheck _UU03a3_ _UU0393_ f with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TArrow (_UU03c4_', _UU03c3_) ->
                (match coq_TyEqb _UU03c4_ _UU03c4_' with
                 | Coq_true -> Ok (Types.Types.TColl (_UU03ba_, _UU03c3_))
                 | Coq_false ->
                   Err (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))
              | _ ->
                Err (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_true, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EWhere (p, c) ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, _UU03c4_) ->
          (match typecheck _UU03a3_ _UU0393_ p with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TArrow (_UU03c4_', b) ->
                (match b with
                 | Types.Types.TBool ->
                   (match coq_TyEqb _UU03c4_ _UU03c4_' with
                    | Coq_true -> Ok (Types.Types.TColl (_UU03ba_, _UU03c4_))
                    | Coq_false ->
                      Err (String ((Ascii (Coq_true, Coq_true, Coq_true,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                        (String ((Ascii (Coq_false, Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                        (String ((Ascii (Coq_true, Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)),
                        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 | _ ->
                   Err (String ((Ascii (Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              | _ ->
                Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_true)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_true)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_true)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_false, Coq_true)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false, Coq_true)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EFlatten c ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, a0) ->
          (match a0 with
           | Types.Types.TColl (_UU03ba_', _UU03c4_) ->
             (match coq_KappaEqb _UU03ba_ _UU03ba_' with
              | Coq_true -> Ok (Types.Types.TColl (_UU03ba_, _UU03c4_))
              | Coq_false ->
                Err (String ((Ascii (Coq_false, Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))
           | _ ->
             Err (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
               Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
               Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)),
               (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_true)), (String ((Ascii
               (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true)), (String ((Ascii (Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EProject (fs, c) ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, a0) ->
          (match a0 with
           | Types.Types.TRecord sch ->
             (match forallb (fun a1 -> in_fields a1 sch) fs with
              | Coq_true ->
                Ok (Types.Types.TColl (_UU03ba_, (Types.Types.TRecord
                  (filter_schema fs sch))))
              | Coq_false ->
                Err (String ((Ascii (Coq_false, Coq_false, Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_true, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_false, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))
           | _ ->
             Err (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
               Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EJoin (_UU03b8_, c1, c2) ->
    (match typecheck _UU03a3_ _UU0393_ c1 with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, _UU03c4_) ->
          (match typecheck _UU03a3_ _UU0393_ c2 with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TColl (_UU03ba_', _UU03c3_) ->
                (match negb (coq_KappaEqb _UU03ba_ _UU03ba_') with
                 | Coq_true ->
                   Err (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_false, Coq_true)),
                     EmptyString))))))))))))))))))))))))))))))))))))))
                 | Coq_false ->
                   (match typecheck _UU03a3_ _UU0393_ _UU03b8_ with
                    | Ok a1 ->
                      (match a1 with
                       | Types.Types.TArrow (a2, b) ->
                         (match a2 with
                          | Types.Types.TProd (_UU03c4_1, _UU03c3_1) ->
                            (match b with
                             | Types.Types.TBool ->
                               (match match coq_TyEqb _UU03c4_ _UU03c4_1 with
                                      | Coq_true ->
                                        coq_TyEqb _UU03c3_ _UU03c3_1
                                      | Coq_false -> Coq_false with
                                | Coq_true ->
                                  Ok (Types.Types.TColl (_UU03ba_,
                                    (Types.Types.TProd (_UU03c4_, _UU03c3_))))
                                | Coq_false ->
                                  Err (String ((Ascii (Coq_false, Coq_true,
                                    Coq_false, Coq_true, Coq_false, Coq_true,
                                    Coq_true, Coq_false)), (String ((Ascii
                                    (Coq_true, Coq_true, Coq_true, Coq_true,
                                    Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_true,
                                    Coq_false, Coq_false, Coq_true,
                                    Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_true, Coq_true, Coq_true, Coq_false,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_false, Coq_true, Coq_false,
                                    Coq_true, Coq_true, Coq_true, Coq_false,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_false, Coq_false,
                                    Coq_false, Coq_true, Coq_false,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_true, Coq_false, Coq_true,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_false, Coq_false, Coq_false,
                                    Coq_true, Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_true,
                                    Coq_false, Coq_true, Coq_false,
                                    Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_true, Coq_false, Coq_true,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_true, Coq_false, Coq_false,
                                    Coq_false, Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_false, Coq_false,
                                    Coq_false, Coq_true, Coq_false,
                                    Coq_false)), (String ((Ascii (Coq_true,
                                    Coq_false, Coq_false, Coq_false,
                                    Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_true, Coq_false, Coq_false, Coq_true,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_true, Coq_true, Coq_true,
                                    Coq_false, Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_false, Coq_false,
                                    Coq_false, Coq_true, Coq_false,
                                    Coq_false)), (String ((Ascii (Coq_true,
                                    Coq_false, Coq_true, Coq_true, Coq_false,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_true, Coq_false, Coq_false,
                                    Coq_true, Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_true,
                                    Coq_true, Coq_false, Coq_false, Coq_true,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_true, Coq_false, Coq_true,
                                    Coq_true, Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_true,
                                    Coq_false, Coq_false, Coq_false,
                                    Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_true, Coq_false, Coq_true,
                                    Coq_true, Coq_true, Coq_false)), (String
                                    ((Ascii (Coq_true, Coq_true, Coq_false,
                                    Coq_false, Coq_false, Coq_true, Coq_true,
                                    Coq_false)), (String ((Ascii (Coq_false,
                                    Coq_false, Coq_false, Coq_true,
                                    Coq_false, Coq_true, Coq_true,
                                    Coq_false)),
                                    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
                             | _ ->
                               Err (String ((Ascii (Coq_false, Coq_true,
                                 Coq_false, Coq_true, Coq_false, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_true, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_true, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_true, Coq_false,
                                 Coq_false, Coq_true, Coq_false, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_false, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_true, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_true,
                                 Coq_false, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_false)), (String ((Ascii
                                 (Coq_false, Coq_false, Coq_false, Coq_false,
                                 Coq_false, Coq_true, Coq_false, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_false,
                                 Coq_true, Coq_false, Coq_true, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_false, Coq_false, Coq_false, Coq_true,
                                 Coq_false, Coq_true, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_true, Coq_false,
                                 Coq_true, Coq_false, Coq_false, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_false, Coq_false, Coq_true, Coq_false,
                                 Coq_true, Coq_true, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_true, Coq_false,
                                 Coq_false, Coq_false, Coq_false, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_false, Coq_false, Coq_false, Coq_false,
                                 Coq_false, Coq_true, Coq_false, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_true,
                                 Coq_true, Coq_true, Coq_false, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_true, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_true, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_false,
                                 Coq_true, Coq_false, Coq_true, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_false, Coq_false, Coq_false, Coq_false,
                                 Coq_false, Coq_true, Coq_false, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_false,
                                 Coq_false, Coq_true, Coq_false, Coq_true,
                                 Coq_false, Coq_false)), (String ((Ascii
                                 (Coq_true, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_false, Coq_true, Coq_true)),
                                 (String ((Ascii (Coq_false, Coq_false,
                                 Coq_true, Coq_false, Coq_false, Coq_false,
                                 Coq_false, Coq_true)), (String ((Ascii
                                 (Coq_true, Coq_true, Coq_false, Coq_false,
                                 Coq_false, Coq_false, Coq_true, Coq_true)),
                                 (String ((Ascii (Coq_true, Coq_true,
                                 Coq_true, Coq_false, Coq_true, Coq_false,
                                 Coq_false, Coq_true)), (String ((Ascii
                                 (Coq_true, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_false, Coq_true, Coq_true)),
                                 (String ((Ascii (Coq_true, Coq_true,
                                 Coq_false, Coq_false, Coq_false, Coq_false,
                                 Coq_false, Coq_true)), (String ((Ascii
                                 (Coq_true, Coq_false, Coq_false, Coq_true,
                                 Coq_false, Coq_true, Coq_false, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_true,
                                 Coq_false, Coq_false, Coq_false, Coq_true,
                                 Coq_true, Coq_true)), (String ((Ascii
                                 (Coq_false, Coq_true, Coq_true, Coq_false,
                                 Coq_false, Coq_false, Coq_false, Coq_true)),
                                 (String ((Ascii (Coq_false, Coq_true,
                                 Coq_false, Coq_false, Coq_true, Coq_false,
                                 Coq_false, Coq_true)), (String ((Ascii
                                 (Coq_false, Coq_true, Coq_false, Coq_false,
                                 Coq_false, Coq_false, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_true, Coq_true,
                                 Coq_true, Coq_true, Coq_false, Coq_true,
                                 Coq_true, Coq_false)), (String ((Ascii
                                 (Coq_true, Coq_true, Coq_true, Coq_true,
                                 Coq_false, Coq_true, Coq_true, Coq_false)),
                                 (String ((Ascii (Coq_false, Coq_false,
                                 Coq_true, Coq_true, Coq_false, Coq_true,
                                 Coq_true, Coq_false)),
                                 EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                          | _ ->
                            Err (String ((Ascii (Coq_false, Coq_true,
                              Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_true, Coq_true, Coq_true, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_false, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false, Coq_false)), (String ((Ascii
                              (Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_false)),
                              (String ((Ascii (Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_false, Coq_false, Coq_false, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_true, Coq_false, Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_true, Coq_true,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_true, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_true, Coq_false,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_true, Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_true)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_true,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_true, Coq_true)), (String
                              ((Ascii (Coq_true, Coq_true, Coq_true,
                              Coq_false, Coq_true, Coq_false, Coq_false,
                              Coq_true)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_true, Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_true)), (String
                              ((Ascii (Coq_true, Coq_true, Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_false,
                              Coq_true, Coq_false, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_true, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_true)), (String ((Ascii (Coq_false,
                              Coq_true, Coq_true, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true)), (String
                              ((Ascii (Coq_false, Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_false,
                              Coq_true)), (String ((Ascii (Coq_false,
                              Coq_true, Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_true, Coq_true,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_true, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_true,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)),
                              EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       | _ ->
                         Err (String ((Ascii (Coq_false, Coq_true, Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                           Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_false, Coq_true,
                           Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_false, Coq_true, Coq_false,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_true, Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_false, Coq_true,
                           Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                           Coq_false, Coq_false, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_false, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false, Coq_true, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_true, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_false,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_false,
                           Coq_true, Coq_true)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_false, Coq_false, Coq_true)), (String ((Ascii
                           (Coq_true, Coq_true, Coq_false, Coq_false,
                           Coq_false, Coq_false, Coq_true, Coq_true)),
                           (String ((Ascii (Coq_true, Coq_true, Coq_true,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_true)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_false,
                           Coq_true, Coq_true)), (String ((Ascii (Coq_true,
                           Coq_true, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_false, Coq_true)), (String ((Ascii
                           (Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_false, Coq_true, Coq_true,
                           Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_true, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true)), (String ((Ascii (Coq_false,
                           Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_false, Coq_false, Coq_true)), (String ((Ascii
                           (Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_false, Coq_false, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_true, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_false,
                           Coq_true, Coq_true, Coq_false)),
                           EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    | Err m -> Err m))
              | _ ->
                Err (String ((Ascii (Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EUnionAll (u, v) ->
    (match typecheck _UU03a3_ _UU0393_ u with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, _UU03c4_) ->
          (match typecheck _UU03a3_ _UU0393_ v with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TColl (_UU03ba_', _UU03c4_') ->
                (match match coq_KappaEqb _UU03ba_ _UU03ba_' with
                       | Coq_true -> coq_TyEqb _UU03c4_ _UU03c4_'
                       | Coq_false -> Coq_false with
                 | Coq_true -> Ok (Types.Types.TColl (_UU03ba_, _UU03c4_))
                 | Coq_false ->
                   Err (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))))))))))
              | _ ->
                Err (String ((Ascii (Coq_true, Coq_false, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EUnion (u, v) ->
    (match typecheck _UU03a3_ _UU0393_ u with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_, _UU03c4_) ->
          (match typecheck _UU03a3_ _UU0393_ v with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TColl (_, _UU03c4_') ->
                (match coq_TyEqb _UU03c4_ _UU03c4_' with
                 | Coq_true ->
                   Ok (Types.Types.TColl (Types.Types.Coq_kSet, _UU03c4_))
                 | Coq_false ->
                   Err (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              | _ ->
                Err (String ((Ascii (Coq_true, Coq_false, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EDistinct c ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_, _UU03c4_) ->
          Ok (Types.Types.TColl (Types.Types.Coq_kSet, _UU03c4_))
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EGroupBy (k, c) ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, _UU03c4_) ->
          (match typecheck _UU03a3_ _UU0393_ k with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TArrow (_UU03c4_', kty) ->
                (match coq_TyEqb _UU03c4_ _UU03c4_' with
                 | Coq_true ->
                   Ok (Types.Types.TColl (_UU03ba_, (Types.Types.TProd (kty,
                     (Types.Types.TColl (_UU03ba_, _UU03c4_))))))
                 | Coq_false ->
                   Err (String ((Ascii (Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))
              | _ ->
                Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_true)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_true)), (String ((Ascii
                  (Coq_false, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_true, Coq_true, Coq_true)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
                  Coq_false, Coq_true)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false, Coq_true)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EAggregate (_, c) ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (k, _) ->
          (match k with
           | Types.Types.Coq_kBag -> Ok (Types.Types.TRecord Coq_nil)
           | Types.Types.Coq_kSet ->
             Err (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EHaving (psi, g) ->
    (match typecheck _UU03a3_ _UU0393_ g with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_UU03ba_, a0) ->
          (match a0 with
           | Types.Types.TProd (kty, bty) ->
             (match typecheck _UU03a3_ _UU0393_ psi with
              | Ok a1 ->
                (match a1 with
                 | Types.Types.TArrow (a2, b) ->
                   (match a2 with
                    | Types.Types.TProd (kty', bty') ->
                      (match b with
                       | Types.Types.TBool ->
                         (match match coq_TyEqb kty kty' with
                                | Coq_true -> coq_TyEqb bty bty'
                                | Coq_false -> Coq_false with
                          | Coq_true ->
                            Ok (Types.Types.TColl (_UU03ba_,
                              (Types.Types.TProd (kty, bty))))
                          | Coq_false ->
                            Err (String ((Ascii (Coq_false, Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_true, Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_false, Coq_true, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_true, Coq_true,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_true, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_true, Coq_false,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_true, Coq_false, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_true, Coq_false, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_true, Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_true, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)),
                              EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       | _ ->
                         Err (String ((Ascii (Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_true, Coq_true, Coq_false,
                           Coq_true, Coq_true, Coq_true, Coq_false)), (String
                           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_false, Coq_true, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_false, Coq_false, Coq_true, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_true, Coq_false, Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_false, Coq_false, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_true, Coq_false,
                           Coq_true, Coq_true, Coq_true, Coq_false)), (String
                           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_false, Coq_true, Coq_false,
                           Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_false,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_true, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_true)), (String ((Ascii
                           (Coq_true, Coq_true, Coq_true, Coq_false,
                           Coq_true, Coq_false, Coq_false, Coq_true)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_false, Coq_false, Coq_true, Coq_true,
                           Coq_false, Coq_true)), (String ((Ascii (Coq_true,
                           Coq_false, Coq_false, Coq_true, Coq_false,
                           Coq_true, Coq_false, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_true)), (String
                           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
                           Coq_false, Coq_false, Coq_false, Coq_true)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_false,
                           Coq_true, Coq_true, Coq_false)),
                           EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    | _ ->
                      Err (String ((Ascii (Coq_false, Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                        (String ((Ascii (Coq_true, Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                        Coq_true)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)),
                        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 | _ ->
                   Err (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              | Err m -> Err m)
           | _ ->
             Err (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
               (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_true, Coq_true)), (String
               ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_false, Coq_true)), (String ((Ascii (Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false, Coq_true)), (String
               ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_false, Coq_false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true)), (String ((Ascii (Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false, Coq_true)), (String ((Ascii (Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.EOrder (k, c) ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (k0, _UU03c4_) ->
          (match k0 with
           | Types.Types.Coq_kBag ->
             (match typecheck _UU03a3_ _UU0393_ k with
              | Ok a0 ->
                (match a0 with
                 | Types.Types.TArrow (_UU03c4_', b) ->
                   (match b with
                    | Types.Types.TRecord fs ->
                      (match fs with
                       | Coq_nil ->
                         (match coq_TyEqb _UU03c4_ _UU03c4_' with
                          | Coq_true ->
                            Ok (Types.Types.TColl (Types.Types.Coq_kBag,
                              _UU03c4_))
                          | Coq_false ->
                            Err (String ((Ascii (Coq_true, Coq_true,
                              Coq_true, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_false, Coq_true, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_false, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_true, Coq_false, Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_false, Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_true, Coq_false)), (String ((Ascii
                              (Coq_false, Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false, Coq_false)),
                              (String ((Ascii (Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_false, Coq_true,
                              Coq_false, Coq_false)), (String ((Ascii
                              (Coq_true, Coq_true, Coq_false, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_false)),
                              (String ((Ascii (Coq_true, Coq_false, Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_false, Coq_true, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_false,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_true, Coq_false,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_true, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_false,
                              Coq_false, Coq_false, Coq_true, Coq_false,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_false, Coq_false, Coq_true,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_true, Coq_false, Coq_true,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_false, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_true,
                              Coq_false, Coq_true, Coq_true, Coq_true,
                              Coq_false)), (String ((Ascii (Coq_true,
                              Coq_true, Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_true, Coq_false)), (String
                              ((Ascii (Coq_false, Coq_false, Coq_false,
                              Coq_true, Coq_false, Coq_true, Coq_true,
                              Coq_false)),
                              EmptyString)))))))))))))))))))))))))))))))))))))))))))))))
                       | Coq_cons (_, _) ->
                         Err (String ((Ascii (Coq_true, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_false, Coq_false, Coq_true, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_true, Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                           Coq_false, Coq_true, Coq_true, Coq_true,
                           Coq_false, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_true, Coq_true, Coq_false,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                           Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                           Coq_false, Coq_false, Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_true,
                           Coq_true, Coq_true, Coq_false)), (String ((Ascii
                           (Coq_false, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false)),
                           (String ((Ascii (Coq_true, Coq_true, Coq_true,
                           Coq_true, Coq_false, Coq_false, Coq_true,
                           Coq_true)), (String ((Ascii (Coq_false, Coq_false,
                           Coq_true, Coq_false, Coq_false, Coq_false,
                           Coq_false, Coq_true)), (String ((Ascii (Coq_false,
                           Coq_true, Coq_false, Coq_false, Coq_false,
                           Coq_true, Coq_true, Coq_true)), (String ((Ascii
                           (Coq_false, Coq_true, Coq_true, Coq_false,
                           Coq_false, Coq_false, Coq_false, Coq_true)),
                           (String ((Ascii (Coq_false, Coq_true, Coq_false,
                           Coq_false, Coq_true, Coq_false, Coq_false,
                           Coq_true)), (String ((Ascii (Coq_true, Coq_true,
                           Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                           Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                           Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
                           Coq_false)),
                           EmptyString)))))))))))))))))))))))))))))))))))))))))))))
                    | _ ->
                      Err (String ((Ascii (Coq_true, Coq_true, Coq_true,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                        (String ((Ascii (Coq_false, Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                        (String ((Ascii (Coq_false, Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_false,
                        Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_false, Coq_true,
                        Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
                        Coq_true)), (String ((Ascii (Coq_true, Coq_true,
                        Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
                        Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                        Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
                        Coq_false)),
                        EmptyString)))))))))))))))))))))))))))))))))))))))))))))
                 | _ ->
                   Err (String ((Ascii (Coq_true, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_false,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
                     (String ((Ascii (Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                     (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_false, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
                     Coq_false, Coq_false, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_false, Coq_true, Coq_true, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
                     Coq_false, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
                     Coq_true, Coq_false, Coq_false, Coq_true)), (String
                     ((Ascii (Coq_true, Coq_true, Coq_false, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false)), (String
                     ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
                     Coq_true, Coq_true, Coq_true, Coq_false)),
                     EmptyString)))))))))))))))))))))))))))))))))))))))))))))
              | Err m -> Err m)
           | Types.Types.Coq_kSet ->
             Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
               Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.ELimit (n, c) ->
    (match typecheck _UU03a3_ _UU0393_ n with
     | Ok a ->
       (match a with
        | Types.Types.TInt ->
          (match typecheck _UU03a3_ _UU0393_ c with
           | Ok a0 ->
             (match a0 with
              | Types.Types.TColl (_UU03ba_, _UU03c4_) ->
                Ok (Types.Types.TColl (_UU03ba_, _UU03c4_))
              | _ ->
                Err (String ((Ascii (Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
                  Coq_false, Coq_false)), (String ((Ascii (Coq_false,
                  Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
                  (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
                  Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
                  Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
                  Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
                  Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_false, Coq_false,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_false,
                  Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
                  Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
                  Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
                  (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
                  Coq_false, Coq_true, Coq_true, Coq_false)),
                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           | Err m -> Err m)
        | _ ->
          Err (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | Term.Term.ECount c ->
    (match typecheck _UU03a3_ _UU0393_ c with
     | Ok a ->
       (match a with
        | Types.Types.TColl (_, a0) ->
          (match a0 with
           | Types.Types.TUnit -> Ok Types.Types.TInt
           | _ ->
             Err (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
               (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
               Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
               Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
               Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
               Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
               (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_true)), (String ((Ascii
               (Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
               Coq_false, Coq_true)), (String ((Ascii (Coq_false, Coq_false,
               Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
               Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)), (String
               ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
               Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
               Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
               Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
               Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        | _ ->
          Err (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
            (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
            (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
            (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
            Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true)), (String ((Ascii (Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)),
            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | Err m -> Err m)
  | _ ->
    Err (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_false, Coq_false)), (String ((Ascii
      (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_true, Coq_false, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
      Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
      (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false)),
      (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
      Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
      ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_false, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
      Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
      (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
      Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end
