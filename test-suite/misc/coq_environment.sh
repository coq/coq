#!/usr/bin/env bash

# Make
CoqMakefile_in="$(realpath "../../tools/CoqMakefile.in")"

# Careful with this, some distros mount /tmp as noexec, so we cannot
# use mktmp and place binaries there.
# This does not work on Mac! Solution is to move to cram tests.
TMP=`mktemp -p $(pwd) -d`
cd $TMP

cat > coq_environment.txt <<EOT
# we override COQLIB because we can
COQLIB="$TMP/overridden" # bla bla
COQCORELIB="$TMP/overridden" # bla bla
OCAMLFIND="$TMP/overridden"
FOOBAR="one more"
EOT

cp $(which coqc) ./coqc
cp $(which coq_makefile) ./coq_makefile
mkdir -p overridden/tools/
cp $CoqMakefile_in overridden/tools/CoqMakefile.in

unset COQLIB
N=`./coqc -config | grep COQLIB | grep /overridden | wc -l`
if [ $N -ne 1 ]; then
  echo COQLIB not overridden by coq_environment
  coqc -config
  exit 1
fi
N=`./coqc -config | grep OCAMLFIND | grep /overridden | wc -l`
if [ $N -ne 1 ]; then
  echo OCAMLFIND not overridden by coq_environment
  coqc -config
  exit 1
fi
./coq_makefile -o CoqMakefile -R . foo > /dev/null
N=`grep COQMF_OCAMLFIND CoqMakefile.conf | grep /overridden | wc -l`
if [ $N -ne 1 ]; then
  echo COQMF_OCAMLFIND not overridden by coq_environment
  cat CoqMakefile.conf
  exit 1
fi

export COQLIB="/overridden2"
N=`./coqc -config | grep COQLIB | grep /overridden2 | wc -l`
if [ $N -ne 1 ]; then
  echo COQLIB not overridden by COQLIB when coq_environment present
  coqc -config
  exit 1
fi

rm -rf $TMP
exit 0
