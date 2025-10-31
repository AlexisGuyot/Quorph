From Coq Require Import Extraction.

(* Adapte les chemins de modules selon ton arborescence *)
From Quorph.Impl  Require Import Types Term Typing.
From Quorph.Algo Require Import AlgoTyping.

Extraction Language OCaml.

(* On déverse l’extraction dans ../ir (répertoire racine/ir) *)
Cd "../ir".

(* Extraction séparée : le module qui contient expr (Term),
   le jugement de typage (Typing) et le typechecker (AlgoTyping) *)
Separate Extraction
  Term
  Typing.has_type
  AlgoTyping.typecheck.

(* Retour éventuel au dossier Coq si tu enchaînes d’autres scripts *)
Cd "../coq".
