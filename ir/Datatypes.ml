
type bool =
| Coq_true
| Coq_false

(** val negb : bool -> bool **)

let negb = function
| Coq_true -> Coq_false
| Coq_false -> Coq_true

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Coq_pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Coq_pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Coq_pair (_, y) -> y

type 'a list =
| Coq_nil
| Coq_cons of 'a * 'a list
