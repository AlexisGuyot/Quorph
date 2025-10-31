.PHONY: build test qc extraction

build:
	@dune build @all

test:
	@dune runtest

qc:
	@echo "QuickChick runs inside Coq; not wired in this CLI artifact."

extraction:
	@echo "[1/4] Build Coq"
	cd coq && coq_makefile -f _CoqProject -o Makefile
	$(MAKE) -C coq -j
	@echo "[2/4] Extraction OCaml"
	cd coq && coqc -Q impl Quorph.Impl -Q algo Quorph.Algo -Q extract Quorph.Extract extract/Extract.v
	@echo "[3/4] Prépare la lib IR"
	mkdir -p ir
	@echo "[4/4] Déplace les fichiers extraits"
	mv coq/*.ml ir/ 2>/dev/null || true
