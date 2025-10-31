(* src/bridge/coq_ast_bridge.ml *)
open Ast_surface

(* Modules extraits *)
module Ty        = Types.Types
module Ir        = Term.Term
module CoqString = String
module D         = Datatypes
module A         = Ascii

module L = Stdlib.List
module S = Stdlib.String

(* ====================================================================== *)
(* Listes et paires Coq                                                   *)
(* ====================================================================== *)

let dlist_map f xs =
  L.fold_right (fun x acc -> D.Coq_cons (f x, acc)) xs D.Coq_nil

let dpair (a, b) = D.Coq_pair (a, b)

(* ====================================================================== *)
(* ascii /S.string Coq <-> OCaml                                    *)
(* ====================================================================== *)

let coq_bool (b:bool) = if b then D.Coq_true else D.Coq_false

let ascii_of_char (c : char) : A.ascii =
  let n = Stdlib.Char.code c in
  let bit i = if (n lsr i) land 1 = 1 then D.Coq_true else D.Coq_false in
  A.Ascii (bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let char_of_ascii (a : A.ascii) : char =
  let b v k = if v = D.Coq_true then (1 lsl k) else 0 in
  match a with
  | A.Ascii (b0,b1,b2,b3,b4,b5,b6,b7) ->
      Stdlib.Char.chr (b b0 0 lor b b1 1 lor b b2 2 lor b b3 3 lor
                       b b4 4 lor b b5 5 lor b b6 6 lor b b7 7)

let s (str : string) : CoqString.string =
  let rec build i =
    if i = Stdlib.String.length str then CoqString.EmptyString
    else CoqString.String (ascii_of_char (Stdlib.String.get str i), build (i+1))
  in
  build 0

let ocaml_string (cs : CoqString.string) : string =
  let buf = Buffer.create 32 in
  let rec loop = function
    | CoqString.EmptyString -> ()
    | CoqString.String (a, rest) ->
        Buffer.add_char buf (char_of_ascii a);
        loop rest
  in
  loop cs; Buffer.contents buf


let dfields_of (xs : (string * Ty.ty) list) =
  dlist_map (fun (k,t) -> D.Coq_pair (s k, t)) xs

let record_ty_of (xs : (string * Ty.ty) list) : Ty.ty =
  Ty.TRecord (dfields_of xs)

(* --- Assoc sur liste Coq (D.list) de paires D.Coq_pair --- *)
let rec assoc_coq k l =
  match l with
  | D.Coq_nil -> None
  | D.Coq_cons (p, tl) ->
      (match p with
       | D.Coq_pair (k', v) -> if k' = k then Some v else assoc_coq k tl)

(* Champ d'un Ty.TRecord (liste Coq) *)
let lookup_field (ty : Ty.ty) (fname : string) : Ty.ty option =
  match ty with
  | Ty.TRecord fs -> assoc_coq (s fname) fs
  | _ -> None

(* Trouver le type de ligne d'une source dans le catalogue (liste OCaml) *)
let find_src (catalog : (CoqString.string * Ty.ty) list) (name : string) : Ty.ty =
  let target = s name in
  let rec go = function
    | [] -> failwith ("unknown source in catalog: " ^ name)
    | (k, ty) :: tl -> if k = target then ty else go tl
  in
  go catalog

(* Génère un identifiant frais qui n'entre pas en collision avec les noms présents dans [tenv]
   et, éventuellement, avec une liste d'identifiants à éviter via ~avoid. *)
let fresh_name ?(avoid : string list = []) (tenv : (string * Ty.ty) list) (base : string) : string =
  let open Stdlib in
  let used =
    (* noms déjà utilisés dans l’environnement *)
    L.map fst tenv @ avoid
  in
  let rec loop i =
    let cand = if i = 0 then base else base ^ string_of_int i in
    if L.exists (fun x -> String.equal x cand) used
    then loop (i + 1)
    else cand
  in
  loop 0


(* ====================================================================== *)
(* Z helpers (BinNums)                                                    *)
(* ====================================================================== *)

let rec positive_of_int (n : int) : BinNums.positive =
  if n <= 1 then BinNums.Coq_xH
  else if n land 1 = 0
  then BinNums.Coq_xO (positive_of_int (n lsr 1))
  else BinNums.Coq_xI (positive_of_int (n lsr 1))

let z_of_int (n : int) : BinNums.coq_Z =
  if n = 0 then BinNums.Z0
  else if n > 0 then BinNums.Zpos (positive_of_int n)
  else BinNums.Zneg (positive_of_int (Stdlib.abs n))

(* ====================================================================== *)
(* Utils sources / catalog                                                *)
(* ====================================================================== *)

let cut_source (raw : string) : string =
  let len = S.length raw in
  let rec find_stop i =
    if i >= len then i else
    match S.get raw i with
    | '|' | ' ' | '\t' | '\n' -> i
    | _ -> find_stop (i+1)
  in
  let k = find_stop 0 in
  S.sub raw 0 k

(* let find_src (catalog : (CoqString.string * Ty.ty) list) (name_coq : CoqString.string) : Ty.ty =
  let name_ocaml = ocaml_string name_coq in
  let rec go = function
    | [] -> failwith ("unknown source: "^name_ocaml)
    | (k, ty)::tl ->
        if S.equal (ocaml_string k) name_ocaml then ty else go tl
  in
  go catalog *)

(* ====================================================================== *)
(* Vérif champs & mini-inférence surface (Bool/Int/String)                *)
(* ====================================================================== *)

let ocaml_label (l : CoqString.string) = ocaml_string l

(* let lookup_field (ty : Ty.ty) (lbl : string) : Ty.ty option =
  match ty with
  | Ty.TRecord fields ->
      let rec find = function
        | D.Coq_nil -> None
        | D.Coq_cons (D.Coq_pair (k, v), tl) ->
            if S.equal (ocaml_label k) lbl then Some v else find tl
      in
      find fields
  | _ -> None *)

type tyenv = (string * Ty.ty) list

(* Track current row type in tenv (internal) *)
let __rowty__ = "__ROW_TYPE__"

let set_row_ty (tenv:tyenv) (ty:Ty.ty) : tyenv =
  let rec drop = function
    | [] -> []
    | (k,_)::tl when S.equal k __rowty__ -> drop tl
    | x::tl -> x :: drop tl
  in
  ( __rowty__, ty ) :: drop tenv

let get_row_ty (tenv:tyenv) : Ty.ty =
  match L.assoc_opt __rowty__ tenv with
  | Some ty -> ty
  | None -> failwith "internal: row type not set"

(* Opérateurs qui donnent (ou composent) un Bool *)
let bool_ops =
  [ "eq"; "ne"; "lt"; "le"; "gt"; "ge"           (* noms verbaux *)
  ; "="; "<>"; "<"; "<="; ">"; ">="              (* symboles *)
  ; "and"; "or"; "not"                           (* logiques *)
  ]

(* Petit helper : est-ce un comparateur ? *)
let is_cmp (op:string) =
  let op = S.lowercase_ascii op in
  L.mem op [ "eq"; "ne"; "lt"; "le"; "gt"; "ge"; "="; "<>"; "<"; "<="; ">"; ">=" ]

(* Heuristique “surface” robuste pour reconnaître un booléen. 
   On reste permissif (les erreurs réelles seront attrapées par le typechecker Coq). *)
let rec looks_bool_surface (tenv:tyenv) (e:Ast_surface.expr) : bool =
  match e with
  | EBool _ -> true
  | EField (_, _) -> true                                     (* champ supposé bool : vérifié plus tard *)
  | EIdent _ -> true                                          (* idem *)
  | EBinop (op,a,b) ->
      let lop = S.lowercase_ascii op in
      if lop = "and" || lop = "or" then
        looks_bool_surface tenv a && looks_bool_surface tenv b
      else if is_cmp op then
        true
      else
        false
  | ECall (fn, [x]) ->
      S.lowercase_ascii fn = "not" && looks_bool_surface tenv x
  | _ -> false

let rec infer_ty (tenv : tyenv) (e : Ast_surface.expr) : Ty.ty option =
  match e with
  | EBool _   -> Some Ty.TBool
  | EInt _    -> Some Ty.TInt
  | EString _ -> Some Ty.TString
  | EIdent v ->
      (* 1) variable liée dans l'env *)
      (match L.assoc_opt v tenv with
       | Some t -> Some t
       | None ->
         (* 2) sinon, champ du type de ligne courant ? *)
         let row_ty = get_row_ty tenv in
         lookup_field row_ty v)
  | EField (e', a) ->
      (match infer_ty tenv e' with
       | Some ty ->
           (match lookup_field ty a with
            | Some ty' -> Some ty'
            | None -> failwith ("unknown field '" ^ a ^ "' on that record"))
       | None -> None)
  | ERecord _      -> None
  | EBinop (op,a,b) ->
      ignore (infer_ty tenv a); ignore (infer_ty tenv b);
      if L.mem op bool_ops then Some Ty.TBool else None
  | ECall (fn,args) ->
      let lower = S.lowercase_ascii fn in
      L.iter (fun arg -> ignore (infer_ty tenv arg)) args;
      match lower, args with
      | "count", [_] -> Some Ty.TInt
      | ("sum" | "min" | "max" | "avg"), [_] ->
          (* Agrégats numériques -> Int dans ton système de types actuel *)
          Some Ty.TInt
      | _ ->
          if L.mem lower bool_ops then Some Ty.TBool else None
  (* | EBinop (op,a,b) ->
      let _ = infer_ty tenv a in
      let _ = infer_ty tenv b in
      if L.exists (fun s -> S.equal s op) bool_ops
      then Some Ty.TBool else None
  | ECall (fn,args) ->
      L.iter (fun arg -> ignore (infer_ty tenv arg)) args;
      if L.exists (fun s -> S.equal s fn) bool_ops
      then Some Ty.TBool else None *)

let ty_of_agg (fn:string) (args:Ast_surface.expr list) (tenv:tyenv) : Ty.ty =
  let lower = S.lowercase_ascii fn in
  let default_int = Ty.TInt in
  match lower with
  | "count" -> Ty.TInt
  | "sum" | "max" | "min" | "avg" ->
      (* try to infer type of first arg; fallback to Int *)
      (match args with
       | a::_ -> (match infer_ty tenv a with Some t -> t | None -> default_int)
       | [] -> default_int)
  | _ ->
      (* conservative default *)
      default_int

let require_bool_strict (ctx : string) (tenv : tyenv) (e : Ast_surface.expr) =
  if looks_bool_surface tenv e then () else failwith (ctx ^ ": predicate must be boolean")

(* -------- Helpers for higher-order calls like filter/map ---------------- *)

(* Collect identifiers used in a surface expression *)
let rec collect_idents (e : Ast_surface.expr) : string list =
  match e with
  | EIdent v        -> [v]
  | EField (e', _)  -> collect_idents e'
  | ERecord fs      -> L.flatten (L.map (fun (_k,v) -> collect_idents v) fs)
  | EBinop (_op,a,b)-> collect_idents a @ collect_idents b
  | ECall (_f,args) -> L.concat (L.map collect_idents args)
  | _               -> []

let pick_param_name (tenv:tyenv) (e:Ast_surface.expr) : string =
  let in_scope = L.map fst tenv in
  let cands =
    collect_idents e
    |> L.filter (fun v -> not (L.mem v in_scope))
  in
  match cands with
  | v::_ -> v
  | []   -> "y"

(* Assoc pour listes Coq (D.list) de paires D.Coq_pair *)
(* let rec assoc_coq k l =
  match l with
  | D.Coq_nil -> None
  | D.Coq_cons (p, tl) ->
      (match p with
       | D.Coq_pair (k', v) ->
           if k' = k then Some v else assoc_coq k tl) *)

(* Récupère le type d'un champ d'un record Ty.TRecord (liste Coq) *)
let lookup_record_field (ty : Ty.ty) (fname : string) : Ty.ty option =
  match ty with
  | Ty.TRecord fields -> assoc_coq (s fname) fields
  | _ -> None

let element_ty_of_collection_ty (ty : Ty.ty) : Ty.ty option =
  match ty with
  | Ty.TColl (_, t) -> Some t
  | _ -> None

(* Type élément d'une collection 'coll', en tenant compte des abréviations. *)
(* let infer_elt_ty (tenv : tyenv) (coll : Ast_surface.expr) : Ty.ty =
  let refine_with_row_field tdefault =
    match coll with
    | EField (EIdent alias, fld) -> (
        match L.assoc_opt alias tenv with
        | Some row_ty -> (
            match lookup_field row_ty fld with
            | Some (Ty.TColl (_k, t)) -> t
            | Some t                  -> t
            | None                    -> tdefault)
        | None -> tdefault)
    | EIdent fld -> (
        let row_ty = get_row_ty tenv in
        match lookup_field row_ty fld with
        | Some (Ty.TColl (_k, t)) -> t
        | Some t                  -> t
        | None                    -> tdefault)
    | _ -> tdefault
  in
  match infer_ty tenv coll with
  | Some (Ty.TColl (_k, t)) -> t
  | Some t_noncoll          -> refine_with_row_field t_noncoll
  | None                    -> refine_with_row_field Ty.TUnit *)

  (* Résout la collection autant en IR qu'en type élément.
   - si 'coll' est 'EIdent fld' et que fld est un champ du row courant,
     on renvoie la projection IR 'EProj(EVar from_id, fld)'
   - sinon, on laisse la traduction standard. *)
(* let resolve_collection (tenv : tyenv) (from_id : string option) (coll : Ast_surface.expr)
  : Ir.expr * Ty.ty =
  match coll with
  | EIdent fld -> (
      let row_ty = get_row_ty tenv in
      match lookup_field row_ty fld with
      | Some field_ty ->
          let elt_ty =
            match field_ty with
            | Ty.TColl (_k, t) -> t
            | t                -> t
          in
          let ir =
            match from_id with
            | Some id -> Ir.EProj (Ir.EVar (s id), s fld)
            | None    -> expr_to_ir_with tenv from_id coll
          in
          (ir, elt_ty)
      | None ->
          (expr_to_ir_with tenv from_id coll, infer_elt_ty tenv coll))
  | _ ->
      (expr_to_ir_with tenv from_id coll, infer_elt_ty tenv coll) *)


(* ====================================================================== *)
(* Shorthands IR                                                          *)
(* ====================================================================== *)

let elam x ty body = Ir.ELam (x, ty, body)
let eapp f x       = Ir.EApp (f, x)

let ebool b        = Ir.EConstBool (coq_bool b)
let eint  n        = Ir.EConstInt (z_of_int n)
let estr  st       = Ir.EConstString (s st)

let evar  v        = Ir.EVar (s v)
let erec  fs       = Ir.ERecord (dlist_map (fun (k,v) -> dpair (s k, v)) fs)
let eproj e a      = Ir.EProj (e, s a)

let escan src      = Ir.EScan (s src)
let ewhere p c     = Ir.EWhere (p, c)
let eorder keys c  = Ir.EOrder (keys, c)
let egroup k c     = Ir.EGroupBy (k, c)
let elimit n c     = Ir.ELimit (n, c)
let ejoin th c1 c2 = Ir.EJoin (th, c1, c2)

(* Choose operator name, disambiguating string comparisons. *)
let disamb_cmp_op (tenv : (string * Ty.ty) list) (op:string) (a:Ast_surface.expr) (b:Ast_surface.expr) : string =
  let lop = S.lowercase_ascii op in
  if L.mem lop [ "eq"; "ne"; "lt"; "le"; "gt"; "ge"; "="; "<>"; "<"; "<="; ">"; ">=" ] then
    let ta = infer_ty tenv a and tb = infer_ty tenv b in
    match ta, tb with
    | Some Ty.TString, _ | _, Some Ty.TString -> op ^ "s"
    | _ -> op
  else op

(* ====================================================================== *)
(* Traduction surface -> IR                                               *)
(* ====================================================================== *)

type env = { catalog : (CoqString.string * Ty.ty) list }

(* ===== Mutuellement récursives : expr_to_ir_with / resolve_collection / infer_elt_ty ===== *)

let rec expr_to_ir_with
    (catalog : (CoqString.string * Ty.ty) list)
    (tenv    : (string * Ty.ty) list)
    (from_id : string option)
    (e       : Ast_surface.expr) : Ir.expr =
  match e with
  | EInt n            -> Ir.EConstInt (z_of_int n)
  | EBool b           -> Ir.EConstBool (coq_bool b)
  | EString t         -> Ir.EConstString (s t)
  | EIdent v ->
      (* Si [v] est un champ de la ligne courante, projeter ; sinon variable libre *)
      let row_ty = get_row_ty tenv in
      (match lookup_field row_ty v, from_id with
      | (Some _), (Some id) -> Ir.EProj (Ir.EVar (s id), s v)
      | _                   -> Ir.EVar (s v))
  | EField (e', a)    -> Ir.EProj (expr_to_ir_with catalog tenv from_id e', s a)
  | ERecord fs        ->
      Ir.ERecord (dlist_map (fun (k,v) -> D.Coq_pair (s k, expr_to_ir_with catalog tenv from_id v)) fs)
  | EBinop (op, a, b) ->
      let a_ir = expr_to_ir_with catalog tenv from_id a in
      let b_ir = expr_to_ir_with catalog tenv from_id b in
      let op0 =
        match (a, b) with
        | EString _, _ | _, EString _ -> op ^ "s"
        | _ -> op
      in
      Ir.EApp (Ir.EApp (Ir.EVar (s op0), a_ir), b_ir)

  (* --- count(e)  ==>  count(map (λ_:τ.()) e) --- *)
  | ECall (fn, [arg]) when S.lowercase_ascii fn = "count" ->
      let coll_ir, elt_ty = resolve_collection catalog tenv from_id arg in
      let lam_unit = Ir.ELam (s "_", elt_ty, Ir.EConstUnit) in
      let coll_unit = Ir.EMap (lam_unit, coll_ir) in
      Ir.ECount coll_unit

  (* --- DSL: filter(y in coll where pred)  ==>  EWhere (λ(y:τ).pred, coll) --- *)
  | ECall (fn, [EIdent v; coll; pred]) when S.lowercase_ascii fn = "filter" ->
      let coll_ir, elt_ty = resolve_collection catalog tenv from_id coll in
      let rec pred_under e =
        match e with
        | EIdent w when w = v -> Ir.EVar (s v)
        | EField (e', a)      -> Ir.EProj (pred_under e', s a)
        | ERecord fs          -> Ir.ERecord (dlist_map (fun (k,u)-> D.Coq_pair (s k, pred_under u)) fs)
        | EBinop (op,a,b)     ->
            let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
            Ir.EApp (Ir.EApp (Ir.EVar (s op0), pred_under a), pred_under b)
        | ECall (f,args)      ->
            L.fold_left (fun acc u -> Ir.EApp (acc, pred_under u)) (Ir.EVar (s f)) args
        | _                   -> expr_to_ir_with catalog tenv from_id e
      in
      let lam = Ir.ELam (s v, elt_ty, pred_under pred) in
      Ir.EWhere (lam, coll_ir)

  (* --- Variante tolérée: filter(pred, coll) --- *)
  | ECall (fn, [pred; coll]) when S.lowercase_ascii fn = "filter" ->
      let coll_ir, elt_ty = resolve_collection catalog tenv from_id coll in
      let fresh =
        let base = "y" in
        let rec loop i =
          let cand = if i = 0 then base else base ^ string_of_int i in
          if L.mem_assoc cand tenv then loop (i+1) else cand
        in loop 0
      in
      let rec pred_under e =
        match e with
        | EIdent w when w = fresh -> Ir.EVar (s fresh)
        | EField (e', a)          -> Ir.EProj (pred_under e', s a)
        | ERecord fs              -> Ir.ERecord (dlist_map (fun (k,u)-> D.Coq_pair (s k, pred_under u)) fs)
        | EBinop (op,a,b)         ->
            let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
            Ir.EApp (Ir.EApp (Ir.EVar (s op0), pred_under a), pred_under b)
        | ECall (f,args)          ->
            L.fold_left (fun acc u -> Ir.EApp (acc, pred_under u)) (Ir.EVar (s f)) args
        | _                       -> expr_to_ir_with catalog tenv from_id e
      in
      let lam = Ir.ELam (s fresh, elt_ty, pred_under pred) in
      Ir.EWhere (lam, coll_ir)

  | ECall (fn,args) ->
      let f = Ir.EVar (s fn) in
      L.fold_left
        (fun acc arg -> Ir.EApp (acc, expr_to_ir_with catalog tenv from_id arg))
        f args

and resolve_collection
    (catalog : (CoqString.string * Ty.ty) list)
    (tenv    : (string * Ty.ty) list)
    (from_id : string option)
    (coll    : Ast_surface.expr)
  : Ir.expr * Ty.ty =
  match coll with
  (* --- c.fld : on projette depuis la bonne base (alias si dispo), pas toujours from_id --- *)
  | EField (EIdent alias, fld) -> (
      match L.assoc_opt alias tenv with
      | Some row_ty -> (
          let base =
            match from_id with
            | Some id when id = alias -> Ir.EVar (s id)
            | _                        -> Ir.EVar (s alias)
          in
          match lookup_field row_ty fld with
          | Some (Ty.TColl (_k, t)) ->
              (Ir.EProj (base, s fld), t)
          | Some t_non_coll ->
              (* On autorise le cas non-collection : l'appelant utilisera 't_non_coll' comme τ élément. *)
              (Ir.EProj (base, s fld), t_non_coll)
          | None ->
              (* Champ inconnu : on retombe sur la traduction générique *)
              (expr_to_ir_with catalog tenv from_id coll, Ty.TUnit)
        )
      | None ->
          (* Alias non résolu dans l'env : fallback générique *)
          (expr_to_ir_with catalog tenv from_id coll, Ty.TUnit)
    )

  (* --- ident nu : soit champ de la row, soit source du catalogue --- *)
  | EIdent name -> (
      let row_ty = get_row_ty tenv in
      match lookup_field row_ty name with
      | Some (Ty.TColl (_k, t)) ->
          (* champ collection du row courant *)
          let ir =
            match from_id with
            | Some id -> Ir.EProj (Ir.EVar (s id), s name)
            | None    -> Ir.EVar (s name)
          in
          (ir, t)
      | Some t_scalar ->
          (* champ scalaire du row courant *)
          let ir =
            match from_id with
            | Some id -> Ir.EProj (Ir.EVar (s id), s name)
            | None    -> Ir.EVar (s name)
          in
          (ir, t_scalar)
      | None ->
          (* sinon : si 'name' est une source du catalogue, on fait un scan *)
          (try
             let row = find_src catalog name in
             (Ir.EScan (s name), row)
           with _ ->
             (* inconnu : traduction générique + type par défaut conservateur *)
             (expr_to_ir_with catalog tenv from_id coll, Ty.TUnit))
    )

  (* --- fallback générique --- *)
  | _ ->
      let ir = expr_to_ir_with catalog tenv from_id coll in
      let elt =
        match infer_elt_ty catalog tenv coll with
        | t -> t
      in
      (ir, elt)

and infer_elt_ty
    (catalog : (CoqString.string * Ty.ty) list)
    (tenv    : (string * Ty.ty) list)
    (coll    : Ast_surface.expr) : Ty.ty =
  match coll with
  | ECall (fn, [EIdent _y; c; _pred]) when S.lowercase_ascii fn = "filter" ->
      (* DSL: filter(y in c where pred) *)
      infer_elt_ty catalog tenv c
  | ECall (fn, [_pred; c]) when S.lowercase_ascii fn = "filter" ->
      (* Variante tolérée: filter(pred, c) *)
      infer_elt_ty catalog tenv c
  | _ ->
  let with_row_fallback tdefault =
    match coll with
    | EField (EIdent alias, fld) -> (
        match L.assoc_opt alias tenv with
        | Some row_ty -> (
            match lookup_field row_ty fld with
            | Some (Ty.TColl (_k, t)) -> t
            | Some t                  -> t
            | None                    -> tdefault)
        | None -> tdefault)
    | EIdent name -> (
        (* champ abrégé de la row ? *)
        let row_ty = get_row_ty tenv in
        match lookup_field row_ty name with
        | Some (Ty.TColl (_k, t)) -> t
        | Some t                  -> t
        | None -> (
            (* source du catalogue *)
            try find_src catalog name with _ -> tdefault))
    | _ -> tdefault
  in
  with_row_fallback Ty.TUnit



let of_query_env (env : env) (q : Ast_surface.query) : Ir.expr =
  let base    = cut_source q.from_source in
  let src     = s base in
  let ty_row  = find_src env.catalog (ocaml_string src) in
  let c0      = escan base in

  (* tenv pour vérifier champs et booléens en surface *)
  let tenv0 : tyenv = set_row_ty [ (q.from_id, ty_row) ] ty_row in

  let step (c, tenv) (st : Ast_surface.stage) : (Ir.expr * tyenv) =
    match st with
    | Where p ->
    let row_ty = get_row_ty tenv in
    let pred = Ir.ELam (s q.from_id, row_ty, expr_to_ir_with env.catalog tenv (Some q.from_id) p) in
    ( Ir.EWhere (pred, c), tenv )

    | Select fields ->
      let row_ty = get_row_ty tenv in
      (match row_ty with
      | Ty.TProd (_ty1, _ty2) ->
          (* Après un JOIN : binder sur la paire et réécrire c/e en fst/snd. *)
          let rec find_other = function
            | [] -> None
            | (k,_)::tl when S.equal k __rowty__ || S.equal k q.from_id -> find_other tl
            | (k,_)::_ -> Some k
          in
          let id2 = match find_other tenv with Some k -> k | None -> q.from_id in
          let z = s "z" in
          let x = Ir.EFst (Ir.EVar z) in
          let y = Ir.ESnd (Ir.EVar z) in
          let rec to_ir = function
            | EIdent v when v = q.from_id -> x
            | EIdent v when v = id2       -> y
            | EIdent v                    -> Ir.EVar (s v)
            | EField (e,a)                -> Ir.EProj (to_ir e, s a)
            | EInt n                      -> Ir.EConstInt (z_of_int n)
            | EBool b                     -> Ir.EConstBool (coq_bool b)
            | EString t                   -> Ir.EConstString (s t)
            | ERecord fs -> Ir.ERecord (dlist_map (fun (k,v) -> dpair (s k, to_ir v)) fs)
            | EBinop (op,a,b) ->
                let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                Ir.EApp (Ir.EApp (Ir.EVar (s op0), to_ir a), to_ir b)

            (* --- count(e)  ==>  count(map (λ (_:τ). ()) e) --- *)
            | ECall (fn, [arg]) when S.lowercase_ascii fn = "count" ->
                let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) arg in
                let lam_unit  = Ir.ELam (s "_", elt_ty, Ir.EConstUnit) in
                let coll_unit = Ir.EMap (lam_unit, coll_ir) in
                Ir.ECount coll_unit

            (* --- filter(y in coll where pred)  ==>  EWhere (λ(y:τ). pred’, coll_ir) --- *)
            | ECall (fn, [EIdent v; coll; pred]) when S.lowercase_ascii fn = "filter" ->
                let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) coll in
                let rec lower e =
                  match e with
                  | EIdent w when w = v -> Ir.EVar (s v)
                  | EField (e', a)      -> Ir.EProj (lower e', s a)
                  | ERecord fs          -> Ir.ERecord (dlist_map (fun (k,u)-> dpair (s k, lower u)) fs)
                  | EBinop (op,a,b)     ->
                      let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                      Ir.EApp (Ir.EApp (Ir.EVar (s op0), lower a), lower b)
                  | ECall (f,args)      -> L.fold_left (fun acc u -> Ir.EApp (acc, lower u)) (Ir.EVar (s f)) args
                  | _                   -> to_ir e      (* <-- IMPORTANT : PAS expr_to_ir_with *)
                in
                Ir.EWhere (Ir.ELam (s v, elt_ty, lower pred), coll_ir)

            (* --- filter(pred, coll)  ==>  EWhere (λ(fresh:τ). pred’[fresh], coll_ir) --- *)
            | ECall (fn, [pred; coll]) when S.lowercase_ascii fn = "filter" ->
                let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) coll in
                let fresh = fresh_name ~avoid:[q.from_id] tenv "y" in
                let rec lower e =
                  match e with
                  | EIdent w when w = fresh -> Ir.EVar (s fresh)
                  | EField (e', a)          -> Ir.EProj (lower e', s a)
                  | ERecord fs              -> Ir.ERecord (dlist_map (fun (k,u)-> dpair (s k, lower u)) fs)
                  | EBinop (op,a,b)         ->
                      let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                      Ir.EApp (Ir.EApp (Ir.EVar (s op0), lower a), lower b)
                  | ECall (f,args)          -> L.fold_left (fun acc u -> Ir.EApp (acc, lower u)) (Ir.EVar (s f)) args
                  | _                       -> to_ir e  (* <-- IMPORTANT *)
                in
                Ir.EWhere (Ir.ELam (s fresh, elt_ty, lower pred), coll_ir)

            (* fallback générique : appels « normaux » *)
            | ECall (fn,args) ->
                let f = Ir.EVar (s fn) in
                L.fold_left (fun acc arg -> Ir.EApp (acc, to_ir arg)) f args
          in
          let field_tys =
            L.map (fun (k,v) ->
              match infer_ty tenv v with
              | Some t -> (k,t) | None -> (k, Ty.TString)
            ) fields in
          let body = Ir.ERecord (dlist_map (fun (k,v) -> dpair (s k, to_ir v)) fields) in
          let row_ty' = record_ty_of field_tys in
          (Ir.EMap (Ir.ELam (z, row_ty, body), c), set_row_ty tenv row_ty')
      | _ ->
          (* Cas simple (pas de JOIN auparavant) *)
          let field_tys =
            L.map (fun (k,v) ->
              match infer_ty tenv v with
              | Some t -> (k,t) | None -> (k, Ty.TString)
            ) fields in
          let body =
            Ir.ERecord
              (dlist_map
                  (fun (k,v) -> D.Coq_pair (s k, expr_to_ir_with env.catalog tenv (Some q.from_id) v))
                  fields)
          in
          let row_ty' = record_ty_of field_tys in
          (Ir.EMap (Ir.ELam (s q.from_id, row_ty, body), c), set_row_ty tenv row_ty')
      )

    | Group_by (k, aggs) ->
        (* Type de ligne courant (peut être un produit après un JOIN) *)
        let row_ty = get_row_ty tenv in

        (* Type de la clé, d'après l'env courant *)
        let kty =
          match infer_ty tenv k with
          | Some t -> t
          | None   -> Ty.TInt
        in

        (* Construit la fonction de clé : row -> key *)
        let zrow = s "row" in
        let key_fun =
          match row_ty with
          | Ty.TProd (_l, _r) ->
              (* Cherche l'autre alias introduit par JOIN *)
              let rec find_other = function
                | [] -> None
                | (k,_)::tl when S.equal k __rowty__ || S.equal k q.from_id -> find_other tl
                | (k,_)::_ -> Some k
              in
              let id2 = match find_other tenv with Some k -> k | None -> q.from_id in
              let x = Ir.EFst (Ir.EVar zrow) in
              let y = Ir.ESnd (Ir.EVar zrow) in
              let rec to_ir = function
                | EIdent v when v = q.from_id -> x
                | EIdent v when v = id2       -> y
                | EIdent v                    -> Ir.EVar (s v)
                | EField (e,a)                -> Ir.EProj (to_ir e, s a)
                | EInt n                      -> Ir.EConstInt (z_of_int n)
                | EBool b                     -> Ir.EConstBool (coq_bool b)
                | EString t                   -> Ir.EConstString (s t)
                | ERecord fs -> Ir.ERecord (dlist_map (fun (k,v) -> dpair (s k, to_ir v)) fs)
                | EBinop (op,a,b) ->
                    let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                    Ir.EApp (Ir.EApp (Ir.EVar (s op0), to_ir a), to_ir b)

                (* --- count(e)  ==>  count(map (λ (_:τ). ()) e) --- *)
                | ECall (fn, [arg]) when S.lowercase_ascii fn = "count" ->
                    let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) arg in
                    let lam_unit  = Ir.ELam (s "_", elt_ty, Ir.EConstUnit) in
                    let coll_unit = Ir.EMap (lam_unit, coll_ir) in
                    Ir.ECount coll_unit

                (* --- filter(y in coll where pred)  ==>  EWhere (λ(y:τ). pred’, coll_ir) --- *)
                | ECall (fn, [EIdent v; coll; pred]) when S.lowercase_ascii fn = "filter" ->
                    let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) coll in
                    let rec lower e =
                      match e with
                      | EIdent w when w = v -> Ir.EVar (s v)
                      | EField (e', a)      -> Ir.EProj (lower e', s a)
                      | ERecord fs          -> Ir.ERecord (dlist_map (fun (k,u)-> dpair (s k, lower u)) fs)
                      | EBinop (op,a,b)     ->
                          let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                          Ir.EApp (Ir.EApp (Ir.EVar (s op0), lower a), lower b)
                      | ECall (f,args)      -> L.fold_left (fun acc u -> Ir.EApp (acc, lower u)) (Ir.EVar (s f)) args
                      | _                   -> to_ir e      (* <-- IMPORTANT : PAS expr_to_ir_with *)
                    in
                    Ir.EWhere (Ir.ELam (s v, elt_ty, lower pred), coll_ir)

                (* --- filter(pred, coll)  ==>  EWhere (λ(fresh:τ). pred’[fresh], coll_ir) --- *)
                | ECall (fn, [pred; coll]) when S.lowercase_ascii fn = "filter" ->
                    let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) coll in
                    let fresh = fresh_name ~avoid:[q.from_id] tenv "y" in
                    let rec lower e =
                      match e with
                      | EIdent w when w = fresh -> Ir.EVar (s fresh)
                      | EField (e', a)          -> Ir.EProj (lower e', s a)
                      | ERecord fs              -> Ir.ERecord (dlist_map (fun (k,u)-> dpair (s k, lower u)) fs)
                      | EBinop (op,a,b)         ->
                          let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                          Ir.EApp (Ir.EApp (Ir.EVar (s op0), lower a), lower b)
                      | ECall (f,args)          -> L.fold_left (fun acc u -> Ir.EApp (acc, lower u)) (Ir.EVar (s f)) args
                      | _                       -> to_ir e  (* <-- IMPORTANT *)
                    in
                    Ir.EWhere (Ir.ELam (s fresh, elt_ty, lower pred), coll_ir)

                (* fallback générique : appels « normaux » *)
                | ECall (fn,args) ->
                    let f = Ir.EVar (s fn) in
                    L.fold_left (fun acc arg -> Ir.EApp (acc, to_ir arg)) f args
              in
              Ir.ELam (zrow, row_ty, to_ir k)
          | _ ->
              (* Cas simple : binder sur l'alias principal *)
              Ir.ELam (s q.from_id, row_ty, expr_to_ir_with env.catalog tenv (Some q.from_id) k)
        in

        (* GroupBy avec une LAMBDA de clé *)
        let grouped = egroup key_fun c in

        (* z : (key_ty * Bag row_ty) – utiliser le type de ligne COURANT *)
        let z      = s "z" in
        let z_ty   = Ty.TProd (kty, Ty.TColl (Ty.Coq_kBag, row_ty)) in

        (* Types de sortie des agrégats *)
        let agg_fields_tys =
          L.map (fun (a:Ast_surface.agg) -> (a.out, ty_of_agg a.fn a.args tenv)) aggs in

        (* Corps : en l'état, des *placeholders* suffisent pour typer. *)
        let body =
          let mk_field (a:Ast_surface.agg) =
            let out = a.out in
            match S.lowercase_ascii a.fn with
            | "count" -> D.Coq_pair (s out, Ir.EConstInt (z_of_int 0))
            | "max" | "min" | "sum" | "avg" -> D.Coq_pair (s out, Ir.EConstInt (z_of_int 0))
            | _ -> D.Coq_pair (s out, Ir.EConstInt (z_of_int 0))
          in
          Ir.ERecord (dlist_map mk_field aggs)
        in

        let mapped  = Ir.EMap (Ir.ELam (z, z_ty, body), grouped) in
        let row_ty' = record_ty_of agg_fields_tys in
        (mapped, set_row_ty tenv row_ty')

    | Order_by _keys ->
        (* Le type-checker attend une clé de type τ → {} (enregistrement vide).
          On ignore la liste de clés ici et on produit systématiquement {}. *)
        let row_ty = get_row_ty tenv in
        let x = s "row" in
        let empty_record = Ir.ERecord D.Coq_nil in
        let lam = Ir.ELam (x, row_ty, empty_record) in
        (eorder lam c, tenv)


    | Limit n ->
        (elimit (eint n) c, tenv)

    | Distinct ->
        (* Implémente DISTINCT en bag: group by identité + map fst. *)
        let row_ty = get_row_ty tenv in
        let x = s "row" in
        (* clé : λ(row:τ). row *)
        let key_fun = Ir.ELam (x, row_ty, Ir.EVar x) in
        let grouped = egroup key_fun c in

        (* Chaque groupe : (key : τ) * (bag τ). On récupère la clé (= ligne distincte). *)
        let z    = s "z" in
        let z_ty = Ty.TProd (row_ty, Ty.TColl (Ty.Coq_kBag, row_ty)) in
        let body = Ir.EFst (Ir.EVar z) in
        let mapped = Ir.EMap (Ir.ELam (z, z_ty, body), grouped) in
        (mapped, tenv)

    | Union (_, src2) ->
        let base2 = cut_source src2 in
        let c2 = escan base2 in
        (Ir.EUnion (c, c2), tenv)

    | Union_all (_, src2) ->
        let base2 = cut_source src2 in
        let c2 = escan base2 in
        (Ir.EUnionAll (c, c2), tenv)

    | Join (id2, src2, on) ->
      let base2   = cut_source src2 in
      let src2    = s base2 in
      let ty_left = get_row_ty tenv in
      let ty_row2 = find_src env.catalog (ocaml_string src2) in
      let c2      = escan base2 in
      (* 'on' doit être booléen dans l'env étendu *)
      require_bool_strict "join/on" ((id2, ty_row2)::tenv) on;
      let z    = s "z" in
      let z_ty = Ty.TProd (ty_left, ty_row2) in
      let x    = Ir.EFst (Ir.EVar z) in
      let y    = Ir.ESnd (Ir.EVar z) in
      let rec to_ir_on = function
        | EIdent v when v = q.from_id -> x
        | EIdent v when v = id2       -> y
        | EIdent v                    -> Ir.EVar (s v)
        | EField (e,a)                -> Ir.EProj (to_ir_on e, s a)
        | EInt n                      -> Ir.EConstInt (z_of_int n)
        | EBool b                     -> Ir.EConstBool (coq_bool b)
        | EString t                   -> Ir.EConstString (s t)
        | ERecord fs ->
            Ir.ERecord (dlist_map (fun (k,v) -> dpair (s k, to_ir_on v)) fs)
        | EBinop (op,a,b) ->
            let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
            Ir.EApp (Ir.EApp (Ir.EVar (s op0), to_ir_on a), to_ir_on b)

        (* --- count(e)  ==>  count(map (λ (_:τ). ()) e) --- *)
        | ECall (fn, [arg]) when S.lowercase_ascii fn = "count" ->
            let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) arg in
            let lam_unit  = Ir.ELam (s "_", elt_ty, Ir.EConstUnit) in
            let coll_unit = Ir.EMap (lam_unit, coll_ir) in
            Ir.ECount coll_unit

        (* --- filter(y in coll where pred)  ==>  EWhere (λ(y:τ). pred’, coll_ir) --- *)
        | ECall (fn, [EIdent v; coll; pred]) when S.lowercase_ascii fn = "filter" ->
            let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) coll in
            let rec lower e =
              match e with
              | EIdent w when w = v -> Ir.EVar (s v)
              | EField (e', a)      -> Ir.EProj (lower e', s a)
              | ERecord fs          -> Ir.ERecord (dlist_map (fun (k,u)-> dpair (s k, lower u)) fs)
              | EBinop (op,a,b)     ->
                  let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                  Ir.EApp (Ir.EApp (Ir.EVar (s op0), lower a), lower b)
              | ECall (f,args)      -> L.fold_left (fun acc u -> Ir.EApp (acc, lower u)) (Ir.EVar (s f)) args
              | _                   -> to_ir_on e      (* <-- IMPORTANT : PAS expr_to_ir_with *)
            in
            Ir.EWhere (Ir.ELam (s v, elt_ty, lower pred), coll_ir)

        (* --- filter(pred, coll)  ==>  EWhere (λ(fresh:τ). pred’[fresh], coll_ir) --- *)
        | ECall (fn, [pred; coll]) when S.lowercase_ascii fn = "filter" ->
            let coll_ir, elt_ty = resolve_collection env.catalog tenv (Some q.from_id) coll in
            let fresh = fresh_name ~avoid:[q.from_id] tenv "y" in
            let rec lower e =
              match e with
              | EIdent w when w = fresh -> Ir.EVar (s fresh)
              | EField (e', a)          -> Ir.EProj (lower e', s a)
              | ERecord fs              -> Ir.ERecord (dlist_map (fun (k,u)-> dpair (s k, lower u)) fs)
              | EBinop (op,a,b)         ->
                  let op0 = match (a,b) with EString _, _ | _, EString _ -> op ^ "s" | _ -> op in
                  Ir.EApp (Ir.EApp (Ir.EVar (s op0), lower a), lower b)
              | ECall (f,args)          -> L.fold_left (fun acc u -> Ir.EApp (acc, lower u)) (Ir.EVar (s f)) args
              | _                       -> to_ir_on e  (* <-- IMPORTANT *)
            in
            Ir.EWhere (Ir.ELam (s fresh, elt_ty, lower pred), coll_ir)

        (* fallback générique : appels « normaux » *)
        | ECall (fn,args) ->
            let f = Ir.EVar (s fn) in
            L.fold_left (fun acc arg -> Ir.EApp (acc, to_ir_on arg)) f args
      in
      let theta_body = to_ir_on on in
      let theta      = elam z z_ty theta_body in
      let c'         = ejoin theta c c2 in
      (* >>> clé : enregistrer l'id joint + le nouveau row type produit <<< *)
      let tenv'      = set_row_ty ((id2, ty_row2)::tenv) z_ty in
      (c', tenv')
  in
  fst (L.fold_left step (c0, tenv0) q.stages)

(* API driver *)
let of_query ~(catalog : (CoqString.string * Ty.ty) list)
             (q : Ast_surface.query) : Ir.expr =
  of_query_env { catalog } q

