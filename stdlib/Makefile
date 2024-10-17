all:
	dune build -p coq-stdlib @install

install:
	dune install --root . coq-stdlib

# Make of individual .vo
theories/%.vo:
	dune build $@

refman-html:
	dune build --root . --no-buffer @refman-html

stdlib-html:
	dune build --root . @stdlib-html
