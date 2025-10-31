
type bool =
| Coq_true
| Coq_false

val negb : bool -> bool

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Coq_pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Coq_nil
| Coq_cons of 'a * 'a list
