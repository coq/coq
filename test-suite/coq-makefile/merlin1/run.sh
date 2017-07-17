#!/usr/bin/env bash

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make .merlin
cat > desired <<EOT
B src
S src
EOT
tail -2 .merlin > actual
exec diff -u desired actual
