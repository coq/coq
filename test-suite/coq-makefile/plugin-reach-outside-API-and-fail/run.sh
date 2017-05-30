#!/usr/bin/env bash

set -e

git clean -dfx

cat > _CoqProject <<EOT
-I src/

./src/test_plugin.mllib
./src/test.ml4
./src/test.mli
EOT

mkdir src

cat > src/test_plugin.mllib <<EOT
Test
EOT

touch src/test.mli

cat > src/test.ml4 <<EOT
DECLARE PLUGIN "test"

let _ = Pre_env.empty_env
EOT

${COQBIN}coq_makefile -f _CoqProject -o Makefile

if make VERBOSE=1; then
  # make command should have failed (but didn't)
  exit 1
else
  # make command should have failed (and it indeed did)
  exit 0
fi
