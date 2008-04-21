OCAMLC=ocamlc
OCAMLOPT=ocamlopt

COQSRC=..

MLDIRS=-I $(COQSRC)/config -I $(COQSRC)/lib -I $(COQSRC)/kernel -I +camlp4
BYTEFLAGS=$(MLDIRS)
OPTFLAGS=$(MLDIRS)

CHECKERNAME=coqchk

BINARIES=../bin/$(CHECKERNAME)$(EXE) ../bin/$(CHECKERNAME).opt$(EXE)

MCHECKER:=\
  $(COQSRC)/config/coq_config.cmo \
  $(COQSRC)/lib/pp_control.cmo $(COQSRC)/lib/pp.cmo $(COQSRC)/lib/compat.cmo \
  $(COQSRC)/lib/util.cmo $(COQSRC)/lib/option.cmo $(COQSRC)/lib/hashcons.cmo \
  $(COQSRC)/lib/system.cmo $(COQSRC)/lib/flags.cmo \
  $(COQSRC)/lib/predicate.cmo $(COQSRC)/lib/rtree.cmo \
  $(COQSRC)/kernel/names.cmo $(COQSRC)/kernel/univ.cmo \
  $(COQSRC)/kernel/esubst.cmo term.cmo \
  declarations.cmo environ.cmo \
  closure.cmo reduction.cmo \
  type_errors.cmo \
  modops.cmo \
  inductive.cmo typeops.cmo \
  indtypes.cmo subtyping.cmo mod_checking.cmo \
validate.cmo \
  safe_typing.cmo check.cmo \
  check_stat.cmo checker.cmo

all: $(BINARIES)

byte : ../bin/$(CHECKERNAME)$(EXE)
opt : ../bin/$(CHECKERNAME).opt$(EXE)

check.cma: $(MCHECKER)
	ocamlc $(BYTEFLAGS) -a -o $@ $(MCHECKER)

check.cmxa: $(MCHECKER:.cmo=.cmx)
	ocamlopt $(OPTFLAGS) -a -o $@ $(MCHECKER:.cmo=.cmx)

../bin/$(CHECKERNAME)$(EXE): check.cma
	ocamlc $(BYTEFLAGS) -o $@ unix.cma gramlib.cma check.cma main.ml

../bin/$(CHECKERNAME).opt$(EXE): check.cmxa
	ocamlopt $(OPTFLAGS) -o $@ unix.cmxa gramlib.cmxa check.cmxa main.ml

stats:
	@echo STRUCTURE
	@wc names.ml term.ml declarations.ml environ.ml type_errors.ml
	@echo
	@echo REDUCTION
	@-wc esubst.ml closure.ml reduction.ml
	@echo
	@echo TYPAGE
	@wc univ.ml inductive.ml indtypes.ml typeops.ml safe_typing.ml
	@echo
	@echo MODULES
	@wc modops.ml subtyping.ml
	@echo
	@echo INTERFACE
	@wc check*.ml main.ml 
	@echo
	@echo TOTAL
	@wc *.ml | tail -1

.SUFFIXES:.ml .mli .cmi .cmo .cmx

.ml.cmo:
	$(OCAMLC) -c $(BYTEFLAGS) $<

.ml.cmx:
	$(OCAMLOPT) -c $(OPTFLAGS) $<

.mli.cmi:
	$(OCAMLC) -c $(BYTEFLAGS) $<


depend::
	ocamldep $(MLDIRS) *.ml* > .depend

clean::
	rm -f *.cm* *.o *.a *~ $(BINARIES)

-include .depend
