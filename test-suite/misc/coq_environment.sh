#!/usr/bin/env bash

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

TMP=`mktemp -d`
cd $TMP
mkdir -p overridden/theories/Init/

mkdir overridden/plugins
touch overridden/theories/Init/Prelude.vo

cat > coq_environment.txt <<EOT
# we override ROCQLIB because we can
ROCQLIB="$TMP/overridden" # bla bla
ROCQRUNTIMELIB="$TMP/overridden" # bla bla
OCAMLFIND="$TMP/overridden"
FOOBAR="one more"
EOT

cp $BIN/rocq .
cp $BIN/rocq makefile .
mkdir -p overridden/tools/
cp $ROCQLIB/../rocq-runtime/tools/CoqMakefile.in overridden/tools/

unset ROCQLIB
N=`./rocq c -config | grep COQLIB | grep /overridden | wc -l`
if [ $N -ne 1 ]; then
  echo ROCQLIB not overridden by coq_environment
  coqc -config
  exit 1
fi
N=`./rocq c -config | grep OCAMLFIND | grep /overridden | wc -l`
if [ $N -ne 1 ]; then
  echo OCAMLFIND not overridden by coq_environment
  coqc -config
  exit 1
fi
./rocq makefile -o CoqMakefile -R . foo > /dev/null
N=`grep COQMF_OCAMLFIND CoqMakefile.conf | grep /overridden | wc -l`
if [ $N -ne 1 ]; then
  echo COQMF_OCAMLFIND not overridden by coq_environment
  cat CoqMakefile.conf
  exit 1
fi

mkdir -p overridden2/theories/Init/

mkdir overridden2/plugins
touch overridden2/theories/Init/Prelude.vo

export ROCQLIB="$PWD/overridden2"
N=`./rocq c -config | grep COQLIB | grep overridden2 | wc -l`
if [ $N -ne 1 ]; then
  echo ROCQLIB not overridden by ROCQLIB when coq_environment present
  coqc -config
  exit 1
fi

rm -rf $TMP
exit 0
