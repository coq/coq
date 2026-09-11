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

rocq timelog2html -raw-time-o foo.time.raw.real foo.v foo.v.time1 foo.v.time2 > result.html.real

diff result.html result.html.real
diff foo.time.raw foo.time.raw.real

rocq timelog2html -raw-instr-o foo.instr.raw.real -min-diff 0.00001 foo.v foo.v.json foo.v.2.json > result.json.html.real

diff result.json.html result.json.html.real
diff foo.instr.raw foo.instr.raw.real

rocq timelog2html -raw-instr-o foo.instr.reverse.raw.real -min-diff 0.00001 foo.v foo.v.2.json foo.v.json > /dev/null
diff foo.instr.reverse.raw foo.instr.reverse.raw.real

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
