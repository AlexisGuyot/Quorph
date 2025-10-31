(* src/typing/catalog.mli *)

module Ty        = Types.Types
module CoqString = String

val default : (CoqString.string * Ty.ty) list
