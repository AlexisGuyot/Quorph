open Bool
open Datatypes

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb : ascii -> ascii -> bool **)

let eqb a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | Coq_true -> eqb a1 b1
                                       | Coq_false -> Coq_false with
                                 | Coq_true -> eqb a2 b2
                                 | Coq_false -> Coq_false with
                           | Coq_true -> eqb a3 b3
                           | Coq_false -> Coq_false with
                     | Coq_true -> eqb a4 b4
                     | Coq_false -> Coq_false with
               | Coq_true -> eqb a5 b5
               | Coq_false -> Coq_false with
         | Coq_true -> eqb a6 b6
         | Coq_false -> Coq_false with
   | Coq_true -> eqb a7 b7
   | Coq_false -> Coq_false)
