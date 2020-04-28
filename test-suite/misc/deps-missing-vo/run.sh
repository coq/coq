coq_makefile -f _CoqProject -o Makefile
COQDEP="../../../bin/coqdep -compute_missing -coqlib ../../../" make A.vo # building F.vo would require building error.v which cannot be currently built, e.g. because of errors in its source error.cpp. Also, if someone wants to quickly interactively work on F.v they can use this to not autogenerate all the .v files
