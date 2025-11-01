(* src/common/fresh_name.ml - Génération de noms uniques *)

module S = Stdlib.String
module L = Stdlib.List

(* ====================================================================== *)
(* Fresh name generation                                                  *)
(* ====================================================================== *)

let generate ?(avoid = []) ~used base_name =
  let all_used = used @ avoid in
  let rec try_suffix n =
    let candidate = 
      if n = 0 then base_name 
      else base_name ^ string_of_int n 
    in
    if L.exists (S.equal candidate) all_used then
      try_suffix (n + 1)
    else
      candidate
  in
  try_suffix 0

let from_env ?(avoid = []) env base_name =
  let used_names = L.map fst env in
  generate ~avoid ~used:used_names base_name