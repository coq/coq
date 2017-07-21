#!/usr/bin/env bash

if which pdflatex; then

. ../template/init.sh
	
coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
exec make all.pdf

fi
exit 0 # test skipped
