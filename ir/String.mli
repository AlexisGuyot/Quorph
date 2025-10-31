open Ascii
open Datatypes

type string =
| EmptyString
| String of ascii * string

val eqb : string -> string -> bool

val append : string -> string -> string
