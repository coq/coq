#!/usr/bin/env bash

set -ex

source dev/ci/exports.sh

get-artifact-coq-with-fallback

cd "$CI_INSTALL"
find lib/coq/ -name '*.vo' -print0 > vofiles
for regexp in 's/.vo//' 's:lib/coq/plugins:Coq:' 's:lib/coq/theories:Coq:' 's:/:.:g';
do
    sed -z -i "$regexp" vofiles
done
xargs -0 --arg-file=vofiles bin/coqchk -boot -silent -o -m -coqlib lib/coq/
