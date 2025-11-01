(* src/common/coq_conversion.ml - Conversions entre types OCaml et Coq *)

module D = Datatypes
module A = Ascii
module CoqString = String
module S = Stdlib.String
module L = Stdlib.List
module C = Stdlib.Char

(* ====================================================================== *)
(* Bool conversions                                                       *)
(* ====================================================================== *)

let coq_bool (b : bool) : D.bool =
  if b then D.Coq_true else D.Coq_false

let int_of_coq_bool = function
  | D.Coq_true -> 1
  | D.Coq_false -> 0

let coq_bool_of_bit n i : D.bool =
  if (n land (1 lsl i)) <> 0 then D.Coq_true else D.Coq_false

(* ====================================================================== *)
(* Char/ASCII conversions                                                 *)
(* ====================================================================== *)

let code_of_coq_ascii : A.ascii -> int = function
  | A.Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
      (int_of_coq_bool b0 lsl 0)
    + (int_of_coq_bool b1 lsl 1)
    + (int_of_coq_bool b2 lsl 2)
    + (int_of_coq_bool b3 lsl 3)
    + (int_of_coq_bool b4 lsl 4)
    + (int_of_coq_bool b5 lsl 5)
    + (int_of_coq_bool b6 lsl 6)
    + (int_of_coq_bool b7 lsl 7)

let char_of_coq_ascii (a : A.ascii) : char =
  C.chr (code_of_coq_ascii a)

let coq_ascii_of_char (c : char) : A.ascii =
  let n = C.code c in
  A.Ascii ( coq_bool_of_bit n 0
          , coq_bool_of_bit n 1
          , coq_bool_of_bit n 2
          , coq_bool_of_bit n 3
          , coq_bool_of_bit n 4
          , coq_bool_of_bit n 5
          , coq_bool_of_bit n 6
          , coq_bool_of_bit n 7 )

(* ====================================================================== *)
(* String conversions                                                     *)
(* ====================================================================== *)

let rec string_of_coq (cs : CoqString.string) : string =
  match cs with
  | CoqString.EmptyString -> ""
  | CoqString.String (a, rest) ->
      S.make 1 (char_of_coq_ascii a) ^ string_of_coq rest

let coq_of_string (str : string) : CoqString.string =
  let rec go i =
    if i = S.length str then CoqString.EmptyString
    else
      let a = coq_ascii_of_char (S.get str i) in
      CoqString.String (a, go (i + 1))
  in
  go 0

(* ====================================================================== *)
(* Z (integer) conversions                                                *)
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
(* List conversions                                                       *)
(* ====================================================================== *)

let rec coq_list_of_ocaml_list (f : 'a -> 'b) (xs : 'a list) : 'b D.list =
  match xs with
  | [] -> D.Coq_nil
  | x :: rest -> D.Coq_cons (f x, coq_list_of_ocaml_list f rest)

let rec ocaml_list_of_coq_list (f : 'a -> 'b) (xs : 'a D.list) : 'b list =
  match xs with
  | D.Coq_nil -> []
  | D.Coq_cons (x, rest) -> f x :: ocaml_list_of_coq_list f rest

(* ====================================================================== *)
(* Pair conversions                                                       *)
(* ====================================================================== *)

let coq_pair (a, b) = D.Coq_pair (a, b)

(* ====================================================================== *)
(* Association list helpers                                               *)
(* ====================================================================== *)

let rec assoc_in_coq_list (key : 'k) (lst : ('k, 'v) D.prod D.list) : 'v option =
  match lst with
  | D.Coq_nil -> None
  | D.Coq_cons (D.Coq_pair (k, v), rest) ->
      if k = key then Some v else assoc_in_coq_list key rest