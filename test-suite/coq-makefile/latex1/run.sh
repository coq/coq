#!/bin/bash

#set -x
set -e

if which pdflatex; then

. ../template/init.sh
	
coq_makefile -f _CoqProject -o Makefile
make
exec make all.pdf

fi
exit 0 # test skipped
