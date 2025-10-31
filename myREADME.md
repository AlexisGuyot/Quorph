Dans WSL :

cd /mnt/c/Users/aguyot/Nextcloud/Main/Recherche/Quorph/quorph_core
dune clean
dune build
dune exec quorph -- --help

Voici le mémo rapide pour **recompiler** et **lancer les tests**.

# Coq (kernel mécanisé)

```bash
cd coq
make clean || true
coq_makefile -f _CoqProject -o Makefile
make -j
```

# OCaml / CLI (parse → bridge → type)

```bash
# À la racine du projet
dune clean
dune build @all

# Lancer la batterie de tests (Alcotest)
dune runtest
```

# Exemples de commandes CLI utiles

```bash
# Typage + affichage DU TYPE inféré
dune exec quorph -- type examples/rel_groupby.qp

# Parsing seul
dune exec quorph -- parse examples/rel_vip.qp

# Pretty-print (round-trip possible)
dune exec quorph -- pp examples/neq_filter.qp
```

# Notes

* Le **parser Menhir** est un **stub** ; c’est le **simple parser** qui est utilisé pour le POC.
* Aucune exécution/réécriture : on reste strictement **parse → type**.
