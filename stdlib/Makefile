all:
	dune build -p rocq-stdlib @install

install:
	dune install --root . rocq-stdlib

# Make of individual .vo
theories/%.vo:
	dune build $@

refman-html:
	dune build --root . --no-buffer @refman-html

stdlib-html:
	dune build --root . @stdlib-html
