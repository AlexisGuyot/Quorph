(* src/lib/quorph_frontend.ml *)

(* Renvoie le type (formaté) d’un pipeline texte *)
let type_of_text (text : string) : (string, string) result =
  Typing_driver.type_of_text text

(* Vérifie un pipeline texte *)
let typecheck_text (text : string) : (unit, string) result =
  Typing_driver.typecheck_text text

(* API attendue par tests/CLI : dans les tests, on lui passe un *texte* *)
let typecheck_pipeline (text : string) : (unit, string) result =
  Typing_driver.typecheck_text text

(* Optionnel : si un jour tu veux une entrée par AST *)
let typecheck_pipeline_ast (q : Ast_surface.query) : (unit, string) result =
  Typing_driver.typecheck_pipeline q
