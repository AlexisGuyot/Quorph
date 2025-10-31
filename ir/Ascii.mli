open Datatypes

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb : ascii -> ascii -> bool
