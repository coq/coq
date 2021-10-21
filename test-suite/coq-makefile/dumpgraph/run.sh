#!/usr/bin/env bash

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile

make dumpgraph dumpgraphbox

diff -u dumpgraph.expected dumpgraph
diff -u dumpgraphbox.expected dumpgraphbox
