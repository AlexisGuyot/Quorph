(* src/typing/catalog.ml *)

(* Modules extraits imbriqués *)
module Ty        = Types.Types
module CoqString = String
module D         = Datatypes
module A         = Ascii
module L         = Stdlib.List

(* OCaml bool -> Coq bool *)
let coq_bool (b : bool) : D.bool =
  if b then D.Coq_true else D.Coq_false

(* OCaml char -> Coq ascii *)
let ascii_of_char (c : char) : A.ascii =
  let n = Char.code c in
  let bit k = (n land (1 lsl k)) <> 0 in
  A.Ascii ( coq_bool (bit 0), coq_bool (bit 1), coq_bool (bit 2), coq_bool (bit 3)
          , coq_bool (bit 4), coq_bool (bit 5), coq_bool (bit 6), coq_bool (bit 7) )

(* OCaml string -> Coq String.string (inductif: EmptyString | String(ascii, string)) *)
let s (x : string) : CoqString.string =
  let len = Stdlib.String.length x in
  let rec build i =
    if i >= len then CoqString.EmptyString
    else CoqString.String (ascii_of_char (Stdlib.String.get x i), build (i + 1))
  in
  build 0

(* OCaml list -> Coq Datatypes.list via mapping *)
let dlist_map f xs =
  L.fold_right (fun x acc -> D.Coq_cons (f x, acc)) xs D.Coq_nil

(* Construit les champs d’un TRecord : Datatypes.list (prod String.string Ty.ty) *)
let fields (xs : (string * Ty.ty) list) : (CoqString.string, Ty.ty) D.prod D.list =
  dlist_map (fun (name, ty) -> D.Coq_pair (s name, ty)) xs

(* Type du catalogue : noms de sources en Coq String.string *)
type t = (CoqString.string * Ty.ty) list

let default : t =
  [ (s "customers", Ty.TRecord (fields [ ("id", Ty.TInt); ("name", Ty.TString); ("vip", Ty.TBool) ]));
    (s "emails",    Ty.TRecord (fields [ ("cust_id", Ty.TInt); ("email", Ty.TString) ]));
    (s "orders",    Ty.TRecord (fields [ ("cust_id", Ty.TInt); ("amount", Ty.TInt); ("week", Ty.TInt) ])) ]
