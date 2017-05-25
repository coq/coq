#!/bin/sh

#set -x
set -e

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make .merlin
cat > desired <<EOT
B src
S src
EOT
tail -2 .merlin > actual
exec diff -u desired actual
