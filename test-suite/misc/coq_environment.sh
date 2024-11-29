#!/usr/bin/env bash

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

TMP=`mktemp -d`
cd $TMP
mkdir -p overridden/theories/Init/

mkdir overridden/plugins
touch overridden/theories/Init/Prelude.vo

cat > coq_environment.txt <<EOT
# we override COQLIB because we can
COQLIB="$TMP/overridden" # bla bla
COQCORELIB="$TMP/overridden" # bla bla
OCAMLFIND="$TMP/overridden"
FOOBAR="one more"
EOT

cp $BIN/coqc .
cp $BIN/coq_makefile .
mkdir -p overridden/tools/
cp $COQLIB/../rocq-runtime/tools/CoqMakefile.in overridden/tools/

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

mkdir -p overridden2/theories/Init/

mkdir overridden2/plugins
touch overridden2/theories/Init/Prelude.vo

export COQLIB="$PWD/overridden2"
N=`./coqc -config | grep COQLIB | grep overridden2 | wc -l`
if [ $N -ne 1 ]; then
  echo COQLIB not overridden by COQLIB when coq_environment present
  coqc -config
  exit 1
fi

rm -rf $TMP
exit 0
