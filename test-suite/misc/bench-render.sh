#!/usr/bin/env bash

set -ex
set -o pipefail

export COQBIN=$BIN
export PATH="$COQBIN:$PATH"
export LC_ALL=C

cd misc/bench-render

coqtimelog2html foo.v foo.v.time1 foo.v.time2 > result.html.real

diff -u result.html result.html.real

if coqtimelog2html foo.v foo.v.time1 foo.v.time3 > bad1v3.html.real 2>stderr1v3.real
then >&2 echo "Should have failed!"; exit 1
fi

diff -u /dev/null bad1v3.html.real
diff -u stderr1v3 stderr1v3.real

if coqtimelog2html foo.v foo.v.time1 foo.v.time4 > bad1v4.html.real 2>stderr1v4.real
then >&2 echo "Should have failed!"; exit 1
fi

diff -u /dev/null bad1v4.html.real
diff -u stderr1v4 stderr1v4.real
