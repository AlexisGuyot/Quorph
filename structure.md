quorph-core/
├─ coq/
│  ├─ impl/        # Types.v, Context.v, Term.v, Typing.v, MonadBag.v, Semantics.v (placeholders)
│  └─ proofs/      # TypingProps.v, Laws.v, Soundness.v, Gen.v, Checks.v (placeholders)
├─ extraction/     # (dir prêt si on veut extraire plus tard; non utilisé par la CLI)
├─ src/
│  ├─ parser/      # syntaxe pipeline + désucrage (stubs à étoffer)
│  ├─ lib/         # runtime minimal (sans eval), stub typechecker front-end
│  └─ cli/         # sous-commandes: parse, type, pp, laws
├─ examples/       # fichiers .qp pour démos parse/type/pp
├─ tests/          # tests OCaml placeholders
└─ ...
