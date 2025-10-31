open Ascii
open Datatypes

type string =
| EmptyString
| String of ascii * string

(** val eqb : string -> string -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> Coq_true
     | String (_, _) -> Coq_false)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> Coq_false
     | String (c2, s2') ->
       (match Ascii.eqb c1 c2 with
        | Coq_true -> eqb s1' s2'
        | Coq_false -> Coq_false))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))
