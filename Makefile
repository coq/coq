
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

INCLUDES=-I config -I lib -I kernel -I library

# Objects files 

CONFIG=config/coq_config.cmo

LIB=lib/pp_control.cmo lib/pp.cmo lib/util.cmo lib/hashcons.cmo \
    lib/dyn.cmo

KERNEL=kernel/names.cmo kernel/generic.cmo kernel/univ.cmo kernel/term.cmo \
       kernel/sign.cmo kernel/evd.cmo kernel/constant.cmo \
       kernel/inductive.cmo kernel/sosub.cmo kernel/abstraction.cmo \
       kernel/environ.cmo kernel/instantiate.cmo \
       kernel/closure.cmo kernel/reduction.cmo \
       kernel/type_errors.cmo kernel/typeops.cmo kernel/indtypes.cmo \
       kernel/typing.cmo

LIBRARY=library/libobject.cmo library/summary.cmo

OBJS=$(CONFIG) $(LIB) $(KERNEL) $(LIBRARY)

# Targets

world: $(OBJS)
	#$(OCAMLC) -o coqtop.byte $(OBJS)
	ocamlmktop -o coqtop $(OBJS)

# Literate programming (with ocamlweb)

LPLIB = lib/doc.tex $(LIB:.cmo=.mli)
LPKERNEL = kernel/doc.tex $(KERNEL:.cmo=.mli)
LPLIBRARY = library/doc.tex $(LIBRARY:.cmo=.mli)
LPFILES = doc/macros.tex doc/intro.tex $(LPLIB) $(LPKERNEL) $(LPLIBRARY)
lp: doc/coq.ps
doc/coq.ps: doc/coq.tex
	cd doc; make coq.ps
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

# Default rules

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -c $<

# Cleaning

archclean::
	rm -f config/*.cmx config/*.[so]
	rm -f lib/*.cmx lib/*.[so]
	rm -f kernel/*.cmx kernel/*.[so]

cleanall:: archclean
	rm -f *~
	rm -f config/*.cm[io] config/*~
	rm -f lib/*.cm[io] lib/*~
	rm -f kernel/*.cm[io] kernel/*~

cleanconfig::
	rm -f config/Makefile config/coq_config.ml

# Dependencies

depend:
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*.ml > .depend

include .depend
