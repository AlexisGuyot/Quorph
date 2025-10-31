(* ====================================================================== *)
(* Bridge_util.ml — utilitaires extraits de coq_ast_bridge.ml              *)
(* ====================================================================== *)
(* Ce module regroupe les fonctions génériques et réutilisables, afin de   *)
(* réduire la duplication dans coq_ast_bridge.ml.                           *)
(* ---------------------------------------------------------------------- *)

module D = Datatypes
module A = Ascii
module CoqString = String
module Ty = Types.Types
module Ir = Term.Term
module L = Stdlib.List
module S = Stdlib.String

(* ====================================================================== *)
(* 1) Conversions Coq <-> OCaml pour string/ascii                         *)
(* ====================================================================== *)

let ascii_of_char (c : char) : A.ascii =
  let b i = if i land 1 = 1 then D.Coq_true else D.Coq_false in
  let code = Char.code c in
  A.Ascii (
    b code,
    b (code lsr 1), b (code lsr 2), b (code lsr 3),
    b (code lsr 4), b (code lsr 5), b (code lsr 6), b (code lsr 7)
  )

let char_of_ascii (a : A.ascii) : char =
  let bit = function D.Coq_true -> 1 | D.Coq_false -> 0 in
  let A.Ascii (b0,b1,b2,b3,b4,b5,b6,b7) = a in
  Char.chr (
    bit b0 lor (bit b1 lsl 1) lor (bit b2 lsl 2) lor (bit b3 lsl 3)
    lor (bit b4 lsl 4) lor (bit b5 lsl 5) lor (bit b6 lsl 6) lor (bit b7 lsl 7)
  )

let s (x : string) : CoqString.string =
  let rec build i =
    if i = S.length x then CoqString.EmptyString
    else CoqString.String (ascii_of_char (S.get x i), build (i+1))
  in
  build 0

let ocaml_string (cs : CoqString.string) : string =
  let buf = Buffer.create 32 in
  let rec loop = function
    | CoqString.EmptyString -> ()
    | CoqString.String (a, rest) -> Buffer.add_char buf (char_of_ascii a); loop rest
  in
  loop cs; Buffer.contents buf

(* ====================================================================== *)
(* 2) Helpers D.list (listes Coq)                                         *)
(* ====================================================================== *)

let dnil = D.Coq_nil
let dcons x xs = D.Coq_cons (x, xs)
let dpair (a,b) = D.Coq_pair (a,b)

let rec dlist_map f = function
  | D.Coq_nil -> D.Coq_nil
  | D.Coq_cons (x,xs) -> D.Coq_cons (f x, dlist_map f xs)

(* convertir une liste OCaml en D.list en appliquant f à chaque élément *)
let rec dlist_of_list f = function
  | [] -> D.Coq_nil
  | x::xs -> D.Coq_cons (f x, dlist_of_list f xs)

let dfields_of (xs : (string * Ty.ty) list) : (CoqString.string, Ty.ty) D.prod D.list =
  (* on conserve l'ordre d'entrée *)
  dlist_of_list (fun (k,t) -> dpair (s k, t)) xs

let rec assoc_coq (k : CoqString.string) (xs : (CoqString.string, 'a) D.prod D.list) : 'a option =
  match xs with
  | D.Coq_nil -> None
  | D.Coq_cons (D.Coq_pair (k',v), tl) -> if k'=k then Some v else assoc_coq k tl

(* ====================================================================== *)
(* 3) Aides sur les records & types                                       *)
(* ====================================================================== *)

let lookup_field (ty : Ty.ty) (fname : string) : Ty.ty option =
  match ty with
  | Ty.TRecord fields -> assoc_coq (s fname) fields
  | _ -> None

(* ====================================================================== *)
(* 4) Helpers numériques (BinNums)                                        *)
(* ====================================================================== *)

let rec positive_of_int (n:int) : BinNums.positive =
  if n <= 1 then BinNums.Coq_xH
  else if n land 1 = 0 then BinNums.Coq_xO (positive_of_int (n lsr 1))
  else BinNums.Coq_xI (positive_of_int (n lsr 1))

let z_of_int (n : int) : BinNums.coq_Z =
  if n = 0 then BinNums.Z0
  else if n > 0 then BinNums.Zpos (positive_of_int n)
  else BinNums.Zneg (positive_of_int (Stdlib.abs n))

(* ====================================================================== *)
(* 5) Constantes / shorthands IR                                          *)
(* ====================================================================== *)

let ebool (b : bool) : Ir.expr =
  Ir.EConstBool (if b then D.Coq_true else D.Coq_false)

let eint (n : int) : Ir.expr =
  Ir.EConstInt (z_of_int n)

let estring (t : string) : Ir.expr =
  Ir.EConstString (s t)

let eapp (f : Ir.expr) (x : Ir.expr) : Ir.expr = Ir.EApp (f, x)
let elam (x : string) (ty : Ty.ty) (body : Ir.expr) : Ir.expr = Ir.ELam (s x, ty, body)

(* Applique un opérateur binaire. Si l'une des branches est une string     *)
(* au niveau surface (signalé par le booléen has_string), on suffixe par s *)
let bin_apply ~(op:string) ~(has_string:bool) (a:Ir.expr) (b:Ir.expr) : Ir.expr =
  let op' = if has_string then op ^ "s" else op in
  eapp (eapp (Ir.EVar (s op')) a) b

(* ====================================================================== *)
(* 6) Schémas de transformation courants                                  *)
(* ====================================================================== *)

(* count(coll) = count (map (\_:τ. ()) coll) *)
let count_of (coll_ir : Ir.expr) (elt_ty : Ty.ty) : Ir.expr =
  let lam_unit = elam "_" elt_ty Ir.EConstUnit in
  Ir.ECount (Ir.EMap (lam_unit, coll_ir))

(* ====================================================================== *)
(* 7) Abstraction d'un "lower" avec substitutions de variables            *)
(* ====================================================================== *)

module type SURFACE = sig
  type expr
  val is_string_expr : expr -> bool
end

module Lower (Surf : SURFACE) = struct
  type subs = (string, Ir.expr) Hashtbl.t

  let create_subs () : subs = Hashtbl.create 7

  let with_binding (h:subs) (name:string) (ir:Ir.expr) = Hashtbl.replace h name ir

  let has_string (a:Surf.expr) (b:Surf.expr) = Surf.is_string_expr a || Surf.is_string_expr b

  let lower_bin ~(fallback:Surf.expr -> Ir.expr) ~(op:string) (a:Surf.expr) (b:Surf.expr) : Ir.expr =
    let ai = fallback a and bi = fallback b in
    bin_apply ~op ~has_string:(has_string a b) ai bi
end
