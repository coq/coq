#!/usr/bin/env bash

. ../template/init.sh

echo "let () = Foolib.foo ();;" >> src/test_aux.ml
export OCAMLPATH=$OCAMLPATH:$PWD/findlib
if which cygpath 2>/dev/null; then
  # the only way I found to pass OCAMLPATH on win is to have it contain
  # only one entry
  OCAMLPATH=$(cygpath -w "$PWD"/findlib)
  export OCAMLPATH
fi
make -C findlib/foo clean
coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
cat Makefile.local
make -C findlib/foo
make
make byte
