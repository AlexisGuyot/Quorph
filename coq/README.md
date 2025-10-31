# quorph-core — Coq must-have drop (typing algo + extraction)

This bundle adds:
- Declarative typing (`impl/Typing.v`)
- Algorithmic typechecker (`algo/AlgoTyping.v`) with a catalog parameter
- Extraction script (`extract/Extract.v`)

## Build

```bash
make clean || true
coq_makefile -f _CoqProject -o Makefile
make -j
```

## Extract to OCaml

```bash
coq_makefile -f _CoqProject -o Makefile
make -j extraction
# extracted files appear in: ir/
```

The algorithmic typechecker expects a **catalog** mapping relation names to their tuple type.
