
###########################################################################
# Makefile for Coq
#
# This is the only Makefile. You won't find Makefiles in sub-directories
# and this is done on purpose. If you are not yet convinced of the advantages
# of a single Makefile, please read
#    http://www.pcug.org.au/~millerp/rmch/recu-make-cons-harm.html
# before complaining.
# 
# When you are working in a subdir, you can compile without moving to the
# upper directory using "make -C ..", and the output is still understood
# by Emacs' next-error.
###########################################################################

include config/Makefile

noargument:
	@echo "Please use either"
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make cleanall"
	@echo "or make archclean"

###########################################################################
# Compilation options
###########################################################################

LOCALINCLUDES=-I config -I scripts -I lib -I kernel -I library \
              -I proofs -I tactics -I pretyping -I parsing -I toplevel
INCLUDES=$(LOCALINCLUDES) -I $(CAMLP4LIB)

BYTEFLAGS=$(INCLUDES) $(CAMLDEBUG)
OPTFLAGS=$(INCLUDES) $(CAMLTIMEPROF)
OCAMLDEP=ocamldep
DEPFLAGS=$(LOCALINCLUDES)

CAMLP4EXTEND=camlp4o $(INCLUDES) pa_extend.cmo
OCAMLC_P4O=$(OCAMLC) -pp camlp4o $(BYTEFLAGS)
OCAMLOPT_P4O=$(OCAMLOPT) -pp camlp4o $(OPTFLAGS)

###########################################################################
# Objects files 
###########################################################################

STRLIB=-cclib -lstr

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=config/coq_config.cmo

LIB=lib/pp_control.cmo lib/pp.cmo lib/util.cmo \
    lib/hashcons.cmo lib/dyn.cmo lib/system.cmo lib/options.cmo \
    lib/bstack.cmo lib/edit.cmo lib/stamps.cmo lib/gset.cmo lib/gmap.cmo \
    lib/tlm.cmo lib/bij.cmo lib/gmapl.cmo lib/profile.cmo

KERNEL=kernel/names.cmo kernel/generic.cmo kernel/univ.cmo kernel/term.cmo \
       kernel/sign.cmo kernel/constant.cmo \
       kernel/inductive.cmo kernel/sosub.cmo kernel/abstraction.cmo \
       kernel/environ.cmo kernel/evd.cmo kernel/instantiate.cmo \
       kernel/closure.cmo kernel/reduction.cmo \
       kernel/type_errors.cmo kernel/typeops.cmo kernel/indtypes.cmo \
       kernel/safe_typing.cmo

LIBRARY=library/libobject.cmo library/summary.cmo library/lib.cmo \
	library/global.cmo library/states.cmo library/library.cmo \
	library/nametab.cmo library/impargs.cmo library/redinfo.cmo \
        library/indrec.cmo library/declare.cmo library/discharge.cmo \
        library/goptions.cmo

PRETYPING=pretyping/tacred.cmo pretyping/pretype_errors.cmo \
          pretyping/retyping.cmo pretyping/typing.cmo \
	  pretyping/classops.cmo pretyping/recordops.cmo \
	  pretyping/evarutil.cmo pretyping/evarconv.cmo \
          pretyping/coercion.cmo \
	  pretyping/cases.cmo pretyping/pretyping.cmo \
	  pretyping/syntax_def.cmo

PARSING=parsing/lexer.cmo parsing/coqast.cmo parsing/pcoq.cmo parsing/ast.cmo \
	parsing/g_prim.cmo parsing/g_basevernac.cmo parsing/g_vernac.cmo \
	parsing/g_command.cmo parsing/g_tactic.cmo parsing/g_cases.cmo\
        parsing/extend.cmo parsing/termast.cmo \
        parsing/esyntax.cmo parsing/printer.cmo parsing/pretty.cmo \
	parsing/astterm.cmo parsing/egrammar.cmo
ARITHSYNTAX=parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo

PROOFS=proofs/proof_trees.cmo proofs/logic.cmo \
       proofs/refiner.cmo proofs/evar_refiner.cmo proofs/tacmach.cmo \
       proofs/macros.cmo proofs/tacinterp.cmo proofs/clenv.cmo \
       proofs/pfedit.cmo

TACTICS=tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
        tactics/nbtermdn.cmo tactics/stock.cmo tactics/pattern.cmo \
	tactics/wcclausenv.cmo tactics/tacticals.cmo tactics/tactics.cmo \
        tactics/tacentries.cmo tactics/hiddentac.cmo tactics/elim.cmo

TOPLEVEL=toplevel/himsg.cmo toplevel/errors.cmo toplevel/vernacinterp.cmo \
         toplevel/metasyntax.cmo toplevel/command.cmo toplevel/class.cmo \
         toplevel/vernacentries.cmo toplevel/vernac.cmo toplevel/mltop.cmo \
	 toplevel/protectedtoplevel.cmo toplevel/toplevel.cmo \
         toplevel/usage.cmo toplevel/coqinit.cmo toplevel/coqtop.cmo

HIGHTACTICS=tactics/dhyp.cmo tactics/auto.cmo

CMA=$(CLIBS) $(CAMLP4OBJS)
CMXA=$(CMA:.cma=.cmxa)

CMO=$(CONFIG) $(LIB) $(KERNEL) $(LIBRARY) $(PRETYPING) $(PARSING) \
    $(PROOFS) $(TACTICS) $(TOPLEVEL) $(HIGHTACTICS)
CMX=$(CMO:.cmo=.cmx) $(ARITHSYNTAX:.cmo=.cmx)

###########################################################################
# Main targets (coqmktop, coqtop, coqtop.byte)
###########################################################################

COQMKTOP=scripts/coqmktop

world: $(COQMKTOP) coqtop.byte coqtop states tools

coqtop: $(COQMKTOP) $(CMX)
	$(COQMKTOP) -opt -notactics $(OPTFLAGS) -o coqtop

coqtop.byte: $(COQMKTOP) $(CMO) Makefile
	$(COQMKTOP) -top $(BYTEFLAGS) -o coqtop.byte

# coqmktop 

COQMKTOPCMO=$(CONFIG) scripts/tolink.cmo scripts/coqmktop.cmo 

$(COQMKTOP): $(COQMKTOPCMO)
	$(OCAMLC) $(BYTEFLAGS) -o $(COQMKTOP) -custom str.cma unix.cma $(COQMKTOPCMO) $(OSDEPLIBS) $(STRLIB)

scripts/tolink.ml: Makefile
	echo "let lib = \""$(LIB)"\"" > $@
	echo "let kernel = \""$(KERNEL)"\"" >> $@
	echo "let library = \""$(LIBRARY)"\"" >> $@
	echo "let pretyping = \""$(PRETYPING)"\"" >> $@
	echo "let parsing = \""$(PARSING)"\"" >> $@
	echo "let proofs = \""$(PROOFS)"\"" >> $@
	echo "let tactics = \""$(TACTICS)"\"" >> $@
	echo "let toplevel = \""$(TOPLEVEL)"\"" >> $@
	echo "let hightactics = \""$(HIGHTACTICS)"\"" >> $@

beforedepend:: scripts/tolink.ml

# we provide targets for each subdirectories

lib: $(LIB)
kernel: $(KERNEL)
library: $(LIBRARY)
proofs: $(PROOFS)
tactics: $(TACTICS)
parsing: $(PARSING)
pretyping: $(PRETYPING)
toplevel: $(TOPLEVEL)

# states

states: states/barestate.coq

SYNTAXPP=syntax/PPCommand.v syntax/PPTactic.v syntax/PPCases.v

states/barestate.coq: $(SYNTAXPP) coqtop.byte
	./coqtop.byte -q -batch -nois -I syntax -load-vernac-source syntax/MakeBare.v -outputstate states/barestate.coq

###########################################################################
# tools
###########################################################################

tools: dev/db_printers.cmo

###########################################################################
# minicoq
###########################################################################

MINICOQCMO=$(CONFIG) $(LIB) $(KERNEL) \
	   parsing/lexer.cmo parsing/g_minicoq.cmo \
	   toplevel/fhimsg.cmo toplevel/minicoq.cmo

minicoq: $(MINICOQCMO)
	$(OCAMLC) $(INCLUDES) -o minicoq -custom $(CMA) $(MINICOQCMO) \
	  $(OSDEPLIBS)

###########################################################################
# Documentation
# Literate programming (with ocamlweb)
###########################################################################

.PHONY: doc

doc: doc/coq.tex
	make -C doc coq.ps minicoq.dvi

LPLIB = lib/doc.tex $(LIB:.cmo=.mli)
LPKERNEL = kernel/doc.tex $(KERNEL:.cmo=.mli)
LPLIBRARY = library/doc.tex $(LIBRARY:.cmo=.mli)
LPPRETYPING = pretyping/doc.tex pretyping/rawterm.mli $(PRETYPING:.cmo=.mli)
LPPARSING =$(PARSING:.cmo=.mli)
LPPROOFS = proofs/doc.tex $(PROOFS:.cmo=.mli)
LPTACTICS = tactics/doc.tex $(TACTICS:.cmo=.mli)
LPTOPLEVEL = toplevel/doc.tex $(TOPLEVEL:.cmo=.mli)
LPFILES = doc/macros.tex doc/intro.tex $(LPLIB) $(LPKERNEL) $(LPLIBRARY) \
	  $(LPPRETYPING) $(LPPROOFS) $(LPTACTICS) $(LPTOPLEVEL)

doc/coq.tex: doc/preamble.tex $(LPFILES)
	cat doc/preamble.tex > doc/coq.tex
	ocamlweb --no-preamble $(LPFILES) >> doc/coq.tex
	echo "\end{document}" >> doc/coq.tex

###########################################################################
# Emacs tags
###########################################################################

tags:
	find . -name "*.ml*" | sort -r | xargs \
	etags "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"

###########################################################################
### Special rules
###########################################################################

# lexer (compiled with camlp4 to get optimized streams)

parsing/lexer.cmo: parsing/lexer.ml
	$(OCAMLC_P4O) -c $<

cleanall::
	rm -f parsing/lexer.ml

beforedepend:: parsing/lexer.ml

# grammar modules with camlp4

parsing/q_coqast.cmo: parsing/q_coqast.ml4
	$(OCAMLC) $(BYTEFLAGS) -c -pp "camlp4o q_MLast.cmo -impl" -impl $<

# the generic rules could be used for g_prim.ml4, but this implies
# circular dependencies between g_prim and grammar
parsing/g_prim.cmo: parsing/g_prim.ml4
	$(OCAMLC) $(BYTEFLAGS) -c -pp "$(CAMLP4EXTEND) -impl" -impl $<

parsing/g_prim.cmx: parsing/g_prim.ml4
	$(OCAMLOPT) $(OPTFLAGS) -c -pp "$(CAMLP4EXTEND) -impl" -impl $<

GRAMMARCMO=./lib/pp_control.cmo ./lib/pp.cmo ./lib/util.cmo ./lib/dyn.cmo \
	   ./lib/hashcons.cmo ./parsing/coqast.cmo ./parsing/lexer.cmo \
	   ./parsing/pcoq.cmo ./parsing/q_coqast.cmo ./parsing/g_prim.cmo

parsing/grammar.cma: $(GRAMMARCMO)
	$(OCAMLC) $(BYTEFLAGS) $(GRAMMARCMO) -linkall -a -o $@

CAMLP4GRAMMAR=camlp4o -I parsing pa_extend.cmo grammar.cma
OPTCAMLP4GRAMMAR=camlp4o -I parsing pa_extend.cmo grammar.cma $(OSDEPP4OPTFLAGS)

parsing/g_%.cmo: parsing/g_%.ml4 parsing/grammar.cma
	$(OCAMLC) $(BYTEFLAGS) -c -pp "$(CAMLP4GRAMMAR) -impl" -impl $<

parsing/g_%.cmx: parsing/g_%.ml4 parsing/grammar.cma
	$(OCAMLOPT) $(OPTFLAGS) -c -pp "$(OPTCAMLP4GRAMMAR) -impl" -impl $<

parsing/extend.cmo: parsing/extend.ml4 parsing/grammar.cma
	$(OCAMLC) $(BYTEFLAGS) -c -pp "$(CAMLP4GRAMMAR) -impl" -impl $<

parsing/extend.cmx: parsing/extend.ml4 parsing/grammar.cma
	$(OCAMLOPT) $(OPTFLAGS) -c -pp "$(CAMLP4GRAMMAR) -impl" -impl $<

beforedepend:: $(GRAMMARCMO)

parsing/pcoq.ml: parsing/pcoq.ml4
	$(CAMLP4EXTEND) pr_o.cmo -impl $< -o $@
parsing/extend.ml: parsing/extend.ml4 parsing/grammar.cma
	$(CAMLP4GRAMMAR) pr_o.cmo -impl $< -o $@

beforedepend:: parsing/pcoq.ml parsing/extend.ml

# toplevel/mltop.ml4 (ifdef Byte)

CAMLP4IFDEF=camlp4o pa_ifdef.cmo

toplevel/mltop.cmo: toplevel/mltop.ml4
	$(OCAMLC) $(BYTEFLAGS) -c -pp "$(CAMLP4IFDEF) -DByte -impl" -impl $<
toplevel/mltop.cmx: toplevel/mltop.ml4
	$(OCAMLOPT) $(OPTFLAGS) -c -pp "$(CAMLP4IFDEF) -impl" -impl $<

###########################################################################
# Default rules
###########################################################################

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
	$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4EXTEND) -impl" -c -impl $<

.ml4.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4EXTEND) -impl" -c -impl $<

###########################################################################
# Cleaning
###########################################################################

archclean::
	rm -f config/*.cmx config/*.[so]
	rm -f lib/*.cmx lib/*.[so]
	rm -f kernel/*.cmx kernel/*.[so]
	rm -f library/*.cmx library/*.[so]
	rm -f proofs/*.cmx proofs/*.[so]
	rm -f tactics/*.cmx tactics/*.[so]
	rm -f parsing/*.cmx parsing/*.[so]
	rm -f pretyping/*.cmx pretyping/*.[so]
	rm -f toplevel/*.cmx toplevel/*.[so]
	rm -f coqtop coqtop.byte minicoq

cleanall:: archclean
	rm -f *~
	rm -f doc/*~
	rm -f config/*.cm[io] config/*~
	rm -f lib/*.cm[io] lib/*~
	rm -f kernel/*.cm[io] kernel/*~
	rm -f library/*.cm[io] library/*~
	rm -f proofs/*.cm[io] proofs/*~
	rm -f tactics/*.cm[io] tactics/*~
	rm -f parsing/*.cm[io] parsing/*.ppo parsing/*~
	rm -f pretyping/*.cm[io] pretyping/*~
	rm -f toplevel/*.cm[io] toplevel/*~

cleanconfig::
	rm -f config/Makefile config/coq_config.ml

###########################################################################
# Dependencies
###########################################################################

alldepend: depend dependcamlp4

depend: beforedepend
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*.ml > .depend

dependcamlp4: beforedepend
	rm -f .depend.camlp4
	for f in */*.ml4; do \
	  file=`dirname $$f`/`basename $$f .ml4`; \
	  camlp4o $(INCLUDES) pa_ifdef.cmo pa_extend.cmo q_MLast.cmo $(GRAMMARCMO) pr_o.cmo -impl $$f > $$file.ml; \
	  ocamldep $(DEPFLAGS) $$file.ml >> .depend.camlp4; \
	  rm -f $$file.ml; \
	done

include .depend
include .depend.camlp4
