# Main Makefile for Coq

include config/Makefile

noargument:
	@echo Please use either
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make cleanall"
	@echo or make archclean

BYTEFLAGS=$(INCLUDES) $(CAMLDEBUG)
OPTFLAGS=$(INCLUDES) $(CAMLTIMEPROF)
OCAMLDEP=ocamldep
DEPFLAGS=$(INCLUDES)

INCLUDES=-I config -I lib -I kernel -I library -I parsing -I $(CAMLP4LIB)

CAMLP4EXTEND=camlp4o $(INCLUDES) pa_extend.cmo
OCAMLC_P4O=$(OCAMLC) -pp camlp4o $(BYTEFLAGS)
OCAMLOPT_P4O=$(OCAMLOPT) -pp camlp4o $(OPTFLAGS)

# Objects files 

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=config/coq_config.cmo

LIB=lib/pp_control.cmo lib/pp.cmo lib/system.cmo lib/util.cmo \
    lib/hashcons.cmo lib/dyn.cmo

KERNEL=kernel/names.cmo kernel/generic.cmo kernel/univ.cmo kernel/term.cmo \
       kernel/sign.cmo kernel/evd.cmo kernel/constant.cmo \
       kernel/inductive.cmo kernel/sosub.cmo kernel/abstraction.cmo \
       kernel/environ.cmo kernel/instantiate.cmo \
       kernel/closure.cmo kernel/reduction.cmo \
       kernel/type_errors.cmo kernel/typeops.cmo kernel/indtypes.cmo \
       kernel/typing.cmo

LIBRARY=library/libobject.cmo library/summary.cmo

PARSING=parsing/lexer.cmo parsing/coqast.cmo parsing/pcoq.cmo parsing/ast.cmo \
	parsing/g_prim.cmo parsing/g_basevernac.cmo parsing/g_vernac.cmo \
	parsing/g_command.cmo parsing/g_tactic.cmo parsing/g_multiple_case.cmo

OBJS=$(CONFIG) $(LIB) $(KERNEL) $(LIBRARY) $(PARSING)

# Targets

world: minicoq coqtop doc dev/db_printers.cmo

# coqtop

coqtop: $(OBJS)
	ocamlmktop $(INCLUDES) -o coqtop -custom $(CLIBS) $(CAMLP4OBJS) \
	  $(OBJS) $(OSDEPLIBS)

# minicoq

MINICOQOBJS=$(CONFIG) $(LIB) $(KERNEL) \
	    parsing/lexer.cmo parsing/g_minicoq.cmo toplevel/minicoq.cmo

minicoq: $(MINICOQOBJS)
	$(OCAMLC) $(INCLUDES) -o minicoq -custom $(CLIBS) $(CAMLP4OBJS) \
	  $(MINICOQOBJS) $(OSDEPLIBS)

# Documentation

.PHONY: doc

doc: doc/coq.tex
	make -C doc coq.ps minicoq.dvi

# Literate programming (with ocamlweb)

LPLIB = lib/doc.tex $(LIB:.cmo=.mli)
LPKERNEL = kernel/doc.tex $(KERNEL:.cmo=.mli)
LPLIBRARY = library/doc.tex $(LIBRARY:.cmo=.mli)
LPFILES = doc/macros.tex doc/intro.tex $(LPLIB) $(LPKERNEL) $(LPLIBRARY)

doc/coq.tex: $(LPFILES)
	ocamlweb -o doc/coq.tex $(LPFILES)

# Emacs tags

tags:
	find . -name "*.ml*" | sort -r | xargs \
	etags "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"

# Special rules

parsing/lexer.cmo: parsing/lexer.ml
	$(OCAMLC_P4O) -c $<

beforedepend:: parsing/lexer.ml

# grammar modules with camlp4

parsing/q_coqast.cmo: parsing/q_coqast.ml4
	$(OCAMLC) $(BYTEFLAGS) -c -pp "camlp4o q_MLast.cmo -impl" -impl $<

parsing/g_prim.cmo: parsing/g_prim.ml4
	$(OCAMLC) $(BYTEFLAGS) -c -pp "camlp4o pa_extend.cmo -impl" -impl $<

GRAMMAROBJS=./lib/pp_control.cmo ./lib/pp.cmo ./lib/util.cmo ./lib/dyn.cmo \
	    ./lib/hashcons.cmo ./parsing/coqast.cmo ./parsing/lexer.cmo \
	    ./parsing/pcoq.cmo ./parsing/q_coqast.cmo ./parsing/g_prim.cmo

parsing/grammar.cma: $(GRAMMAROBJS)
	$(OCAMLC) $(BYTEFLAGS) $(GRAMMAROBJS) -linkall -a -o $@

parsing/g_%.cmo: parsing/g_%.ml4 parsing/grammar.cma
	$(OCAMLC) $(BYTEFLAGS) -c -pp "camlp4o -I parsing pa_extend.cmo grammar.cma -impl" -impl $<

beforedepend:: $(GRAMMAROBJS)

# Default rules

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .ml4

.ml.cmo:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -c $<

.mll.ml:
	ocamllex $<

.ml4.cmo:
	$(OCAMLC) $(BYTEFLAGS) -I $(CAMLP4LIB) -pp "$(CAMLP4EXTEND) -impl" -c -impl $<

.ml44.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -I $(CAMLP4LIB) -pp "$(CAMLP4EXTEND) -impl" -c -impl $<

# Cleaning

archclean::
	rm -f config/*.cmx config/*.[so]
	rm -f lib/*.cmx lib/*.[so]
	rm -f kernel/*.cmx kernel/*.[so]
	rm -f library/*.cmx library/*.[so]
	rm -f parsing/*.cmx parsing/*.[so]

cleanall:: archclean
	rm -f *~
	rm -f config/*.cm[io] config/*~
	rm -f lib/*.cm[io] lib/*~
	rm -f kernel/*.cm[io] kernel/*~
	rm -f library/*.cm[io] library/*~
	rm -f parsing/*.cm[io] parsing/*~

cleanconfig::
	rm -f config/Makefile config/coq_config.ml

# Dependencies

depend: beforedepend
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*.ml > .depend
	for f in */*.ml4; do \
	  file=`dirname $$f`/`basename $$f .ml4`; \
	  camlp4o $(INCLUDES) pa_extend.cmo q_MLast.cmo $(GRAMMAROBJS) pr_o.cmo -impl $$f > $$file.ml; \
	  ocamldep $(DEPFLAGS) $$file.ml >> .depend; \
	  rm -f $$file.ml; \
	done

include .depend
