#!/usr/bin/env bash

. ../template/init.sh

rocq makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
exec make validate
