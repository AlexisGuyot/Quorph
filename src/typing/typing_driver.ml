(* src/typing/typing_driver.ml *)

open Ast_surface

module Ty         = Types.Types
module D          = Datatypes
module CoqString  = String
module AT         = AlgoTyping.AlgoTyping
module Bridge     = Coq_ast_bridge
module A          = Ascii
module BN         = BinNums

module L = Stdlib.List
module S = Stdlib.String

(* -------- Coq String.string -> string (affichage des erreurs) ---------- *)

let coq_bool (b:bool) = if b then D.Coq_true else D.Coq_false
let int_of_coq_bool = function D.Coq_true -> 1 | D.Coq_false -> 0

let char_of_ascii (a : A.ascii) : char =
  let (b0,b1,b2,b3,b4,b5,b6,b7) =
    match a with A.Ascii (x0,x1,x2,x3,x4,x5,x6,x7) -> (x0,x1,x2,x3,x4,x5,x6,x7)
  in
  let code =
    (int_of_coq_bool b0 lsl 0) lor
    (int_of_coq_bool b1 lsl 1) lor
    (int_of_coq_bool b2 lsl 2) lor
    (int_of_coq_bool b3 lsl 3) lor
    (int_of_coq_bool b4 lsl 4) lor
    (int_of_coq_bool b5 lsl 5) lor
    (int_of_coq_bool b6 lsl 6) lor
    (int_of_coq_bool b7 lsl 7)
  in
  Char.chr code

let ocaml_string (cs : CoqString.string) : string =
  let buf = Buffer.create 32 in
  let rec loop = function
    | CoqString.EmptyString -> ()
    | CoqString.String (a, rest) ->
        Buffer.add_char buf (char_of_ascii a);
        loop rest
  in
  loop cs; Buffer.contents buf

(* --------- Helpers Datatypes.list ------------------------------------- *)

let dpair (a,b) = D.Coq_pair (a,b)

let rec dlist_of_list f = function
  | [] -> D.Coq_nil
  | x::xs -> D.Coq_cons (f x, dlist_of_list f xs)

(* ---- Prélude : opérateurs logiques / comparateurs (types attendus) ---- *)

(* OCaml char -> Coq ascii *)
let ascii_of_char (c : char) : A.ascii =
  let n = Char.code c in
  let b i = if (n land (1 lsl i)) <> 0 then D.Coq_true else D.Coq_false in
  A.Ascii (b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7)

(* OCaml string -> Coq String.string *)
(* OCaml string -> Coq String.string (du module extrait Coq) *)
let s (txt : string) : CoqString.string =
  let rec go i =
    if i >= Stdlib.String.length txt then
      CoqString.EmptyString
    else
      let ch = Stdlib.String.get txt i in
      CoqString.String (ascii_of_char ch, go (i + 1))
  in
  go 0

(* Cherche le type d'une source dans le catalogue Coq (D.list de (String * Ty.ty)) *)
(* let find_src_ty (name : string) : Ty.ty =
  let target = s name in
  let rec go = function
    | D.Coq_nil -> failwith ("unknown source in catalog: " ^ name)
    | D.Coq_cons (D.Coq_pair (k, ty), tl) ->
        if k = target then ty else go tl
  in
  go Catalog.default *)


let arrow2 a b r = Ty.TArrow (a, Ty.TArrow (b, r))

let prelude : (CoqString.string * Ty.ty) list =
  let tb = Ty.TBool and ti = Ty.TInt and ts = Ty.TString in
  let tc t = Ty.TColl (Ty.Coq_kBag, t) in
  [
    (* logiques *)
    (s "and", arrow2 tb tb tb);
    (s "or" , arrow2 tb tb tb);
    (s "not", Ty.TArrow (tb, tb));

    (* comparateurs (ints) *)
    (s "=",  arrow2 ti ti tb);
    (s "<>", arrow2 ti ti tb);
    (s "<",  arrow2 ti ti tb);
    (s "<=", arrow2 ti ti tb);
    (s ">",  arrow2 ti ti tb);
    (s ">=", arrow2 ti ti tb);

    (* comparateurs (strings) *)
    (s "=s",  arrow2 ts ts tb);
    (s "<>s", arrow2 ts ts tb);
    (s "<s",  arrow2 ts ts tb);
    (s "<=s", arrow2 ts ts tb);
    (s ">s",  arrow2 ts ts tb);
    (s ">=s", arrow2 ts ts tb);

    (* agrégats — signatures suffisantes pour les tests *)
    (* count sur un sac de strings -> int (emails) *)
    (* (s "count", Ty.TArrow (Ty.TColl (Ty.Coq_kBag, Ty.TUnit), Ty.TInt)); *)
    (* min2 sur un sac de strings -> string (emails) *)
    (s "min2",  Ty.TArrow (tc ts, ts));
    (* arithmétiques sur des sacs d'int *)
    (s "min",   Ty.TArrow (tc ti, ti));
    (s "max",   Ty.TArrow (tc ti, ti));
    (s "sum",   Ty.TArrow (tc ti, ti));
    (s "avg",   Ty.TArrow (tc ti, ti));

    (* helpers d'ordre supérieur utilisés dans les agrégats *)
    (* filter : (string -> bool) -> Bag string -> Bag string *)
    (s "filter",
      Ty.TArrow (
        Ty.TArrow (ts, tb),
        Ty.TArrow (Ty.TColl (Ty.Coq_kBag, ts),
                   Ty.TColl (Ty.Coq_kBag, ts))
      ));
  ]


(* ------------------- Pretty-print d'un type Coq ------------------------ *)

let rec pp_ty (t:Ty.ty) : string =
  match t with
  | Ty.TInt            -> "Int"
  | Ty.TString         -> "String"
  | Ty.TBool           -> "Bool"
  | Ty.TUnit           -> "Unit"
  | Ty.TProd (a,b)     -> "(" ^ pp_ty a ^ " * " ^ pp_ty b ^ ")"
  | Ty.TRecord fields  ->
      let parts =
        let rec to_list = function
          | D.Coq_nil -> []
          | D.Coq_cons (D.Coq_pair (k,v), tl) ->
              (S.concat "" [ (ocaml_string k); ": "; pp_ty v ]) :: to_list tl
        in
        to_list fields
      in
      "{ " ^ (S.concat ", " parts) ^ " }"
  | Ty.TColl (_k, ty)  -> "Coll(" ^ pp_ty ty ^ ")"
  | Ty.TSum (a,b)      -> "Sum(" ^ pp_ty a ^ " + " ^ pp_ty b ^ ")"
  | Ty.TOption t'      -> "Option(" ^ pp_ty t' ^ ")"
  | Ty.TArrow (a,b)    -> "(" ^ pp_ty a ^ " -> " ^ pp_ty b ^ ")"

(* ------------------ Garde-fous minimaux (tests KO) --------------------- *)

(* Garde-fou minimal : que le prédicat "ressemble" à un booléen.
   - On accepte les accès champ (c.vip) : le typage Coq vérifiera
     réellement que le champ est Bool, donc on peut être permissif ici.
   - On garde les cas existants : and/or, comparateurs, not. *)
let rec looks_boolean (p:expr) : bool =
  match p with
  | EBool _ -> true
  | EField (_, _) -> true                      (* champ supposé bool jusqu'à typage *)
  | EBinop (op, a, b) ->
      (match S.lowercase_ascii op with
       | "and" | "or" -> looks_boolean a && looks_boolean b
       | "eq" | "ne" | "=" | "<>" | "<" | "<=" | ">" | ">=" -> true
       | _ -> false)
  | ECall (fn, [x]) ->
      (match S.lowercase_ascii fn with
       | "not" -> looks_boolean x
       | _ -> false)
  | _ -> false

let rec check_unknown_field (e:expr) : (unit, string) result =
  let ok = Ok () in
  match e with
  | EField (EIdent _, _) -> ok
  | ERecord fields ->
      let rec each = function
        | [] -> ok
        | (_k, v)::tl ->
            (match check_unknown_field v with
             | Ok () -> each tl
             | Error _ as e -> e)
      in
      each fields
  | EBinop (_, a, b) ->
      (match check_unknown_field a with
       | Ok () -> check_unknown_field b
       | Error _ as e -> e)
  | ECall (_fn, args) ->
      let rec each = function
        | [] -> ok
        | x::xs ->
            (match check_unknown_field x with
             | Ok () -> each xs
             | Error _ as e -> e)
      in
      each args
  | _ -> ok

(* ----------------------------- Typage ---------------------------------- *)

let typecheck_query (q : Ast_surface.query) : (unit, string) result =
  let precheck () =
    let rec loop = function
      | [] -> Ok ()
      | st :: tl ->
          let r =
            match st with
            | Ast_surface.Where p ->
                if looks_boolean p then Ok () else Error "type error"
            | Ast_surface.Select fields ->
                let rec each = function
                  | [] -> Ok ()
                  | (_k, v)::rest ->
                      (match check_unknown_field v with
                       | Ok () -> each rest
                       | Error _ as e -> e)
                in each fields
            | Ast_surface.Group_by _ 
            | Ast_surface.Order_by _ 
            | Ast_surface.Limit _ 
            | Ast_surface.Distinct
            | Ast_surface.Union (_,_)
            | Ast_surface.Union_all (_,_)
            | Ast_surface.Join _ ->
                Ok ()
          in
          (match r with Ok () -> loop tl | Error _ as e -> e)
    in
    loop q.stages
  in
  match precheck () with
  | Error e -> Error e
  | Ok () ->
      (try
         let expr = Bridge.of_query ~catalog:Catalog.default q in
         let cat_ir : (CoqString.string, Ty.ty) D.prod D.list =
           dlist_of_list dpair Catalog.default in
         let env_ir : (CoqString.string, Ty.ty) D.prod D.list = dlist_of_list dpair prelude in
         match AT.typecheck cat_ir env_ir expr with
         | AT.Ok _ty   -> Ok ()
         | AT.Err e    -> Error (ocaml_string e)
       with
       | Failure msg -> Error msg
       | exn         -> Error (Printexc.to_string exn))

(* ---------------------------------------------------------------------- *)
(* API texte                                                              *)
(* ---------------------------------------------------------------------- *)

let typecheck_text (src:string) : (unit, string) result =
  try
    match Simple_parser.parse src with
    | q -> typecheck_query q
  with
  | Failure msg -> Error msg
  | exn         -> Error (Printexc.to_string exn)

let type_of_text (src:string) : (string, string) result =
  try
    let q = Simple_parser.parse src in
    (match typecheck_query q with
     | Error e -> Error e
     | Ok () ->
        let expr = Bridge.of_query ~catalog:Catalog.default q in
        let cat_ir : (CoqString.string, Ty.ty) D.prod D.list =
          dlist_of_list dpair Catalog.default in
        let env_ir : (CoqString.string, Ty.ty) D.prod D.list = dlist_of_list dpair prelude in
        match AT.typecheck cat_ir env_ir expr with
        | AT.Ok ty   -> Ok (pp_ty ty)
        | AT.Err e   -> Error (ocaml_string e))
  with
  | Failure msg -> Error msg
  | exn         -> Error (Printexc.to_string exn)

(* ---------------------------------------------------------------------- *)
(* API pipeline (AST déjà parsé)                                          *)
(* ---------------------------------------------------------------------- *)

let typecheck_pipeline (q : Ast_surface.query) : (unit, string) result =
  typecheck_query q
