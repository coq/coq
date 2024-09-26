all:
	dune build -p coq-stdlib @install

install:
	dune install --root . coq-stdlib

# Make of individual .vo
theories/%.vo:
	dune build $@
