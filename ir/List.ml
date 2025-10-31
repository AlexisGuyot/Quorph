open Datatypes

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Coq_nil -> Coq_false
| Coq_cons (a, l0) ->
  (match f a with
   | Coq_true -> Coq_true
   | Coq_false -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Coq_nil -> Coq_true
| Coq_cons (a, l0) ->
  (match f a with
   | Coq_true -> forallb f l0
   | Coq_false -> Coq_false)
