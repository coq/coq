#!/usr/bin/env bash

set -ex
set -o pipefail

export COQBIN=$BIN
export PATH="$COQBIN:$PATH"
export LC_ALL=C

diff() {
  command diff -a -u --strip-trailing-cr "$1" "$2"
}

cd misc/bench-render

rocq timelog2html foo.v foo.v.time1 foo.v.time2 > result.html.real

diff result.html result.html.real

if rocq timelog2html foo.v foo.v.time1 foo.v.time3 > bad1v3.html.real 2>stderr1v3.real
then >&2 echo "Should have failed!"; exit 1
fi

diff /dev/null bad1v3.html.real
diff stderr1v3 stderr1v3.real

if rocq timelog2html foo.v foo.v.time1 foo.v.time4 > bad1v4.html.real 2>stderr1v4.real
then >&2 echo "Should have failed!"; exit 1
fi

diff /dev/null bad1v4.html.real
diff stderr1v4 stderr1v4.real
