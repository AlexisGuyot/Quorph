open Ast_surface

let to_core_json (_q:query) : Yojson.Safe.t =
  `Assoc [ "core", `String "todo" ]
