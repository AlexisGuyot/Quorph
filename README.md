# quorph-core (validator artifact)

**Goal:** Provide a *mechanized* specification of Quorph **core** (types, terms, typing,
denotational semantics in Coq), plus a small **front-end** that only parses, type-checks
and pretty-prints the *pipeline* surface syntax. **No query engine. No plan checking.
No rewriting.**

This artifact accompanies the **syntax & semantics** paper as a *validator*:
- Coq files contain the **definitions** and placeholders for the main **theorems**.
- OCaml CLI offers only **developer ergonomics**: parse, type, and pretty-print.
- A `laws` command can run *algebraic law tests* (QuickChick) **internally**—it never
  executes user queries nor returns query results.

## Quick start

```bash
opam switch create . 5.2.1 --repos=default
opam install . --deps-only -y
dune build
./_build/default/src/cli/quorph.exe parse examples/rel_vip.qp
./_build/default/src/cli/quorph.exe type  examples/rel_vip.qp
./_build/default/src/cli/quorph.exe pp    examples/rel_vip.qp
```

## Layout

- `coq/impl`: Coq **definitions** (Types, Context, Term, Typing, Monad, Semantics).
- `coq/proofs`: Coq **proofs** (TypingProps, Laws, Soundness) — placeholders to be completed.
- `extraction/`: directives for future extraction (unused by the CLI in this artifact).
- `src/parser`: **pipeline** surface syntax (lexer/parser), desugaring stubs.
- `src/cli`: CLI `quorph` with subcommands: `parse`, `type`, `pp`, `laws`.
- `examples/`: small files used for parsing & typing demos.
- `tests/`: OCaml tests (round-trips, pretty-print).

## Commands

- `quorph parse PROG.qp` — parse and report success or syntax errors.
- `quorph type  PROG.qp` — run the front-end typechecker (stubbed to structure code; the
  authoritative typing rules live in Coq).
- `quorph pp    PROG.qp` — pretty-print the parsed tree in pipeline syntax.

**No** command returns query results. This is a **validator**, not a query engine.


## Typage via Coq (extraction) — How to run

1) Build Coq & extract the IR (generates `Types.ml`, `Term.ml`, `AlgoTyping.ml`):
```sh
cd coq
coq_makefile -f _CoqProject -o Makefile
make -j
coqc -Q impl Quorph.Impl -Q algo Quorph.Algo -Q extract Quorph.Extract extract/Extract.v
cd ..
mkdir -p ir
mv coq/*.ml ir/ 2>/dev/null || true
```

2) Build the CLI:
```sh
dune build @all
```

3) Type-check a query:
```sh
echo 'from c in customers | where c.vip | select { id: c.id, name: c.name } | limit 10' > /tmp/q.qp
dune exec quorph -- type /tmp/q.qp
```

### Notes
- The frontend now uses:
  - `src/bridge/coq_ast_bridge.ml` to map the surface AST to the extracted Coq IR.
  - `src/typing/catalog.ml` for a tiny default catalog (schemas).
  - `src/typing/typing_driver.ml` to call `AlgoTyping.typecheck` extracted from Coq.
- The bridge currently supports a conservative subset (where/join/select/order/limit). Extend it as needed.



# Quorph-core (POC front-end)

**Scope (paper 1)**: parse → type only. No execution, no rewriting/pushdown, no connectors.

## Notes (transparency for reviewers)
- **Parser**: the Menhir-based parser is intentionally a **stub** for now (`pipeline_parser.mly`). The POC uses a lightweight **hand-written parser** (`src/parser/simple_parser.ml`) sufficient for the examples.
- **Aggregates**: currently treated as **type-level placeholders** (no execution). Wiring in the bridge is minimal; the goal is to validate typing, not to evaluate results.
- **Algebraic laws**: the CLI `laws` command is a stub. Laws/proofs are to be run in Coq.
- **Type reporting**: `quorph type file.qp` now **prints the inferred type** from the Coq-extracted algorithmic typechecker.

## CLI
- `quorph parse file.qp` – parses the surface program
- `quorph pp file.qp` – pretty-prints the program
- `quorph type file.qp` – runs the Coq-extracted typechecker and prints the **type**

## Tests
- Alcotest suite includes: type ok, pp roundtrip, non-bool predicate error, unknown field error, **join types ok**.

## Future work (paper 2)
- Rewriting to (optimized) NF and pushdown; target translations; stitching; execution backends.

## Exposed operators (surface → IR)
- `where`, `select`, `join`, `group by … aggregate { … }`, `order by`, `limit`
- **New in this drop**: `distinct`, `union`, `union all` (as linear stages; `union[_all] X in SRC` unions with a second scan)
