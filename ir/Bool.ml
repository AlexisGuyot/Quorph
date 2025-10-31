open Datatypes

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> (match b2 with
                  | Coq_true -> Coq_false
                  | Coq_false -> Coq_true)
