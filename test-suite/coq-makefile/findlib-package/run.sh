#!/usr/bin/env bash

. ../template/init.sh

sed -i.old 's/rocq-runtime.plugins.ltac/rocq-runtime.plugins.ltac,foo/' src/META.coq-test-suite

echo "let () = Foolib.foo ();;" >> src/test_aux.ml
if which cygpath 2>/dev/null; then
  # separator is ; on windows
  OCAMLPATH=$OCAMLPATH;$(cygpath -m "$PWD"/findlib)
else
  OCAMLPATH=$OCAMLPATH:$PWD/findlib
fi
export OCAMLPATH
make -C findlib/foo clean
rocq makefile -f _CoqProject -o Makefile
cat Makefile.conf
cat Makefile.local
make -C findlib/foo
make
make byte
