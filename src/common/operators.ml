(* src/common/operators.ml - Gestion des opérateurs et leur typage *)

module S = Stdlib.String
module L = Stdlib.List

(* ====================================================================== *)
(* Operator classification                                                *)
(* ====================================================================== *)

let boolean_operators = [
  "eq"; "ne"; "lt"; "le"; "gt"; "ge";
  "="; "<>"; "<"; "<="; ">"; ">=";
  "and"; "or"; "not"
]

let comparison_operators = [
  "eq"; "ne"; "lt"; "le"; "gt"; "ge";
  "="; "<>"; "<"; "<="; ">"; ">="
]

let is_boolean_operator op =
  let normalized = S.lowercase_ascii op in
  L.mem normalized boolean_operators

let is_comparison_operator op =
  let normalized = S.lowercase_ascii op in
  L.mem normalized comparison_operators

let is_logical_operator op =
  let normalized = S.lowercase_ascii op in
  L.mem normalized ["and"; "or"; "not"]

(* ====================================================================== *)
(* String operator disambiguation                                         *)
(* ====================================================================== *)

let disambiguate_for_strings op =
  if is_comparison_operator op then op ^ "s" else op

let maybe_add_string_suffix op needs_string_version =
  if needs_string_version then disambiguate_for_strings op else op