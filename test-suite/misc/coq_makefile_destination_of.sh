#!/usr/bin/env bash

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

TMP=`mktemp -d`
cd $TMP

function assert_eq() {
  if [ "$1" != "$2" ]; then
    echo "coq_makefile generates destination" $1 "!=" $2
    cd /
    rm -rf $TMP
    exit 1
  fi
}

assert_eq `coq_makefile -destination-of src/Y/Z/Test.v -Q src X` "X//Y/Z"
mkdir src
assert_eq `coq_makefile -destination-of src/Y/Z/Test.v -Q src X` "X//Y/Z"
mkdir -p src/Y/Z
touch src/Y/Z/Test.v
assert_eq `coq_makefile -destination-of src/Y/Z/Test.v -Q src X` "X//Y/Z"
cd /
rm -rf $TMP
exit 0
