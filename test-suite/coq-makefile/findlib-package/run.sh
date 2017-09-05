#!/usr/bin/env bash

. ../template/init.sh

echo "let () = Foolib.foo ();;" >> src/test_aux.ml
export OCAMLPATH=$OCAMLPATH:$PWD/findlib
make -C findlib/foo clean
coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
cat Makefile.local
make -C findlib/foo
make
make byte
