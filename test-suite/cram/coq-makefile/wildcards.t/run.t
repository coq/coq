  $ coq_makefile -f _CoqProject -o CoqMakefile
  
Check expansion by coq_makefile
  $ grep COQMF_VFILES CoqMakefile.conf
  COQMF_VFILES = $(shell echo a.v b?.v c[1-3].v x/*.v)
  
Check expansion by coqdep
  $ make -f CoqMakefile
  COQDEP VFILES
  COQC a.v
  COQC b1.v
  COQC c1.v
  COQC c2.v
  COQC x/a.v
