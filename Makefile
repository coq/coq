
###########################################################################
# Makefile for Coq
#
# To be used with GNU Make.
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
	@echo "   make clean"
	@echo "or make archclean"

###########################################################################
# Compilation options
###########################################################################

LOCALINCLUDES=-I config -I tools -I scripts -I lib -I kernel -I library \
              -I proofs -I tactics -I pretyping -I parsing -I toplevel  \
              -I contrib/omega -I contrib/ring -I contrib/xml
INCLUDES=$(LOCALINCLUDES) -I $(CAMLP4LIB)

BYTEFLAGS=$(INCLUDES) $(CAMLDEBUG)
OPTFLAGS=$(INCLUDES) $(CAMLTIMEPROF)
OCAMLDEP=ocamldep
DEPFLAGS=$(LOCALINCLUDES)

OCAMLC_P4O=$(OCAMLC) -pp $(CAMLP4O) $(BYTEFLAGS)
OCAMLOPT_P4O=$(OCAMLOPT) -pp $(CAMLP4O) $(OPTFLAGS)
CAMLP4EXTENDFLAGS=-I . pa_extend.cmo q_MLast.cmo
CAMLP4DEPS=sed -n -e 's|^(\*.*camlp4deps: "\(.*\)".*\*)$$|\1|p'

COQINCLUDES=-I states -I contrib/omega -I contrib/ring -I contrib/xml \
            -I theories/Init -I theories/Logic -I theories/Arith \
            -I theories/Bool -I theories/Zarith -I theories/Lists \
	    -I theories/Sets -I theories/Relations -I theories/Wellfounded \
	    -I theories/Reals

###########################################################################
# Objects files 
###########################################################################

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=config/coq_config.cmo

LIB=lib/pp_control.cmo lib/pp.cmo lib/util.cmo \
    lib/hashcons.cmo lib/dyn.cmo lib/system.cmo lib/options.cmo \
    lib/bstack.cmo lib/edit.cmo lib/stamps.cmo lib/gset.cmo lib/gmap.cmo \
    lib/tlm.cmo lib/bij.cmo lib/gmapl.cmo lib/profile.cmo

KERNEL=kernel/names.cmo kernel/univ.cmo kernel/term.cmo \
       kernel/sign.cmo kernel/declarations.cmo \
       kernel/environ.cmo kernel/evd.cmo kernel/instantiate.cmo \
       kernel/closure.cmo kernel/reduction.cmo kernel/inductive.cmo\
       kernel/type_errors.cmo kernel/typeops.cmo kernel/indtypes.cmo \
       kernel/cooking.cmo kernel/safe_typing.cmo

LIBRARY=library/libobject.cmo library/summary.cmo library/nametab.cmo \
	library/lib.cmo library/goptions.cmo \
	library/global.cmo library/library.cmo library/states.cmo \
	library/impargs.cmo library/indrec.cmo library/declare.cmo 

PRETYPING=pretyping/rawterm.cmo pretyping/detyping.cmo \
	  pretyping/retyping.cmo pretyping/tacred.cmo \
	  pretyping/pretype_errors.cmo pretyping/typing.cmo \
	  pretyping/classops.cmo pretyping/recordops.cmo \
	  pretyping/evarutil.cmo pretyping/evarconv.cmo \
          pretyping/coercion.cmo pretyping/cases.cmo pretyping/pretyping.cmo \
	  pretyping/syntax_def.cmo

PARSING=parsing/lexer.cmo parsing/coqast.cmo parsing/pcoq.cmo parsing/ast.cmo \
	parsing/pattern.cmo parsing/astterm.cmo parsing/termast.cmo \
	parsing/g_prim.cmo parsing/g_basevernac.cmo \
	parsing/g_vernac.cmo parsing/g_proofs.cmo parsing/g_tactic.cmo \
	parsing/g_constr.cmo parsing/g_cases.cmo \
        parsing/extend.cmo parsing/esyntax.cmo \
	parsing/printer.cmo parsing/pretty.cmo parsing/egrammar.cmo \
        parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo

# ARITHSYNTAX=parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo

PROOFS=proofs/proof_type.cmo proofs/proof_trees.cmo proofs/logic.cmo \
       proofs/refiner.cmo proofs/evar_refiner.cmo proofs/tacmach.cmo \
       proofs/macros.cmo proofs/clenv.cmo proofs/stock.cmo proofs/pfedit.cmo \
       proofs/tactic_debug.cmo proofs/tacinterp.cmo

TACTICS=tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
        tactics/nbtermdn.cmo tactics/hipattern.cmo tactics/wcclausenv.cmo \
        tactics/tacticals.cmo tactics/tactics.cmo tactics/tacentries.cmo \
        tactics/hiddentac.cmo tactics/elim.cmo

TOPLEVEL=toplevel/himsg.cmo toplevel/errors.cmo \
         toplevel/metasyntax.cmo toplevel/command.cmo toplevel/class.cmo \
         toplevel/record.cmo toplevel/discharge.cmo toplevel/vernacinterp.cmo \
         toplevel/vernacentries.cmo toplevel/vernac.cmo toplevel/mltop.cmo \
	 toplevel/protectedtoplevel.cmo toplevel/toplevel.cmo \
         toplevel/usage.cmo toplevel/coqinit.cmo toplevel/coqtop.cmo

HIGHTACTICS=tactics/dhyp.cmo tactics/auto.cmo tactics/equality.cmo \
            tactics/inv.cmo tactics/leminv.cmo tactics/eauto.cmo \
            tactics/refine.cmo

SPECTAC=tactics/tauto.ml4
USERTAC = $(SPECTAC)
ML4FILES += $(USERTAC)
USERTACCMO=$(USERTAC:.ml4=.cmo)
USERTACCMX=$(USERTAC:.ml4=.cmx)

CONTRIB=contrib/omega/omega.cmo contrib/omega/coq_omega.cmo \
        contrib/ring/quote.cmo contrib/ring/ring.cmo \
#	contrib/xml/xml.cmo \
#	contrib/xml/xmlcommand.cmo contrib/xml/xmlentries.cmo

CMA=$(CLIBS) $(CAMLP4OBJS)
CMXA=$(CMA:.cma=.cmxa)

CMO=$(CONFIG) $(LIB) $(KERNEL) $(LIBRARY) $(PRETYPING) $(PARSING) \
    $(PROOFS) $(TACTICS) $(TOPLEVEL) $(HIGHTACTICS) $(CONTRIB)
CMX=$(CMO:.cmo=.cmx)

###########################################################################
# Main targets (coqmktop, coqtop.opt, coqtop.byte)
###########################################################################

COQMKTOP=bin/coqmktop
COQC=bin/coqc
COQTOPBYTE=bin/coqtop.byte
COQTOPOPT=bin/coqtop.opt
BESTCOQTOP=bin/coqtop.$(BEST)

COQBINARIES= $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(BESTCOQTOP) 

world: $(COQBINARIES) states theories contrib tools

$(COQTOPOPT): $(COQMKTOP) $(CMX) $(USERTACCMX)
	$(COQMKTOP) -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQTOPBYTE): $(COQMKTOP) $(CMO) $(USERTACCMO)
	$(COQMKTOP) -top $(BYTEFLAGS) -o $@

# coqmktop 

COQMKTOPCMO=$(CONFIG) scripts/tolink.cmo scripts/coqmktop.cmo 

$(COQMKTOP): $(COQMKTOPCMO)
	$(OCAMLC) $(BYTEFLAGS) -o $@ -custom str.cma unix.cma \
          $(COQMKTOPCMO) $(OSDEPLIBS)

scripts/tolink.ml: Makefile
	echo "let lib = \""$(LIB)"\"" > $@
	echo "let kernel = \""$(KERNEL)"\"" >> $@
	echo "let library = \""$(LIBRARY)"\"" >> $@
	echo "let pretyping = \""$(PRETYPING)"\"" >> $@
	echo "let parsing = \""$(PARSING)"\"" >> $@
	echo "let proofs = \""$(PROOFS)"\"" >> $@
	echo "let tactics = \""$(TACTICS)"\"" >> $@
	echo "let toplevel = \""$(TOPLEVEL)"\"" >> $@
	echo "let hightactics = \""$(HIGHTACTICS)" "$(USERTACCMO)"\"" >> $@
	echo "let contrib = \""$(CONTRIB)"\"" >> $@

beforedepend:: scripts/tolink.ml

# coqc

COQCCMO=$(CONFIG) toplevel/usage.cmo scripts/coqc.cmo

$(COQC): $(COQCCMO) $(COQTOPBYTE) $(BESTCOQTOP)
	$(OCAMLC) $(BYTEFLAGS) -o $@ -custom unix.cma $(COQCCMO) $(OSDEPLIBS)

clean::
	rm -f scripts/tolink.ml

archclean::
	rm -f $(COQTOPBYTE) $(COQTOPOPT) $(BESTCOQTOP) $(COQC) $(COQMKTOP)

# we provide targets for each subdirectories

lib: $(LIB)
kernel: $(KERNEL)
library: $(LIBRARY)
proofs: $(PROOFS)
tactics: $(TACTICS)
parsing: $(PARSING)
pretyping: $(PRETYPING)
toplevel: $(TOPLEVEL)

###########################################################################
# theories and states
###########################################################################

states: states/barestate.coq states/initial.coq

SYNTAXPP=syntax/PPConstr.v syntax/PPCases.v syntax/PPTactic.v

states/barestate.coq: $(SYNTAXPP) $(BESTCOQTOP)
	$(BESTCOQTOP) -q -batch -silent -nois -I syntax -load-vernac-source syntax/MakeBare.v -outputstate states/barestate.coq

INITVO=theories/Init/Datatypes.vo         theories/Init/Peano.vo         \
       theories/Init/DatatypesSyntax.vo   theories/Init/Prelude.vo       \
       theories/Init/Logic.vo             theories/Init/Specif.vo        \
       theories/Init/LogicSyntax.vo       theories/Init/SpecifSyntax.vo  \
       theories/Init/Logic_Type.vo        theories/Init/Wf.vo            \
       theories/Init/Logic_TypeSyntax.vo

theories/Init/%.vo: theories/Init/%.v states/barestate.coq $(COQC)
	$(COQC) -bindir bin -q -I theories/Init -is states/barestate.coq $<

init: $(INITVO)

TACTICSVO=tactics/Equality.vo tactics/Tauto.vo tactics/Inv.vo \
          tactics/EAuto.vo tactics/Refine.vo

tactics/%.vo: tactics/%.v states/barestate.coq $(COQC)
	$(COQC) -bindir bin -q -I tactics -is states/barestate.coq $<

states/initial.coq: states/barestate.coq states/MakeInitial.v $(INITVO) $(TACTICSVO) $(BESTCOQTOP)
	$(BESTCOQTOP) -q -batch -silent -is states/barestate.coq -I tactics -I theories/Init -load-vernac-source states/MakeInitial.v -outputstate states/initial.coq

clean::
	rm -f states/*~ states/*.coq

LOGICVO=theories/Logic/Classical.vo          theories/Logic/Classical_Type.vo \
      theories/Logic/Classical_Pred_Set.vo   theories/Logic/Eqdep.vo          \
      theories/Logic/Classical_Pred_Type.vo  theories/Logic/Classical_Prop.vo \
      theories/Logic/Eqdep_dec.vo

ARITHVO=theories/Arith/Arith.vo         theories/Arith/Gt.vo          \
	theories/Arith/Between.vo       theories/Arith/Le.vo          \
	theories/Arith/Compare.vo       theories/Arith/Lt.vo          \
	theories/Arith/Compare_dec.vo   theories/Arith/Min.vo         \
	theories/Arith/Div2.vo          theories/Arith/Minus.vo       \
	theories/Arith/Mult.vo          theories/Arith/Even.vo        \
	theories/Arith/EqNat.vo         theories/Arith/Peano_dec.vo   \
	theories/Arith/Euclid_def.vo    theories/Arith/Plus.vo        \
	theories/Arith/Euclid_proof.vo  theories/Arith/Wf_nat.vo      \
#	theories/Arith/Div.vo 

BOOLVO=theories/Bool/Bool.vo  theories/Bool/IfProp.vo \
       theories/Bool/Zerob.vo theories/Bool/DecBool.vo theories/Bool/Sumbool.vo

ZARITHVO=theories/Zarith/Wf_Z.vo        theories/Zarith/Zsyntax.vo \
	 theories/Zarith/ZArith.vo      theories/Zarith/auxiliary.vo \
	 theories/Zarith/ZArith_dec.vo  theories/Zarith/fast_integer.vo \
	 theories/Zarith/Zmisc.vo       theories/Zarith/zarith_aux.vo

LISTSVO=theories/Lists/List.vo      \
        theories/Lists/ListSet.vo   theories/Lists/Streams.vo        \
        theories/Lists/PolyList.vo  theories/Lists/TheoryList.vo

SETSVO=theories/Sets/Classical_sets.vo     theories/Sets/Permut.vo \
 theories/Sets/Constructive_sets.vo theories/Sets/Powerset.vo \
 theories/Sets/Cpo.vo               theories/Sets/Powerset_Classical_facts.vo \
 theories/Sets/Ensembles.vo         theories/Sets/Powerset_facts.vo \
 theories/Sets/Finite_sets.vo       theories/Sets/Relations_1.vo \
 theories/Sets/Finite_sets_facts.vo theories/Sets/Relations_1_facts.vo \
 theories/Sets/Image.vo             theories/Sets/Relations_2.vo \
 theories/Sets/Infinite_sets.vo     theories/Sets/Relations_2_facts.vo \
 theories/Sets/Integers.vo          theories/Sets/Relations_3.vo \
 theories/Sets/Multiset.vo          theories/Sets/Relations_3_facts.vo \
 theories/Sets/Partial_Order.vo     theories/Sets/Uniset.vo

RELATIONSVO=theories/Relations/Newman.vo \
            theories/Relations/Operators_Properties.vo \
            theories/Relations/Relation_Definitions.vo \
            theories/Relations/Relation_Operators.vo \
            theories/Relations/Relations.vo \
            theories/Relations/Rstar.vo

WELLFOUNDEDVO=theories/Wellfounded/Disjoint_Union.vo \
	      theories/Wellfounded/Inclusion.vo \
              theories/Wellfounded/Inverse_Image.vo \
	      theories/Wellfounded/Lexicographic_Exponentiation.vo \
	      theories/Wellfounded/Transitive_Closure.vo \
	      theories/Wellfounded/Union.vo \
	      theories/Wellfounded/Wellfounded.vo \
	      theories/Wellfounded/Well_Ordering.vo \
	      theories/Wellfounded/Lexicographic_Product.vo 

REALSVO=theories/Reals/R_Ifp.vo       theories/Reals/Reals.vo \
	theories/Reals/Raxioms.vo     theories/Reals/Rfunctions.vo \
	theories/Reals/Rbase.vo       theories/Reals/Rlimit.vo \
	theories/Reals/Rbasic_fun.vo  theories/Reals/TypeSyntax.vo \
	theories/Reals/Rderiv.vo

THEORIESVO = $(LOGICVO) $(ARITHVO) $(BOOLVO) $(ZARITHVO) $(LISTSVO) \
             $(SETSVO) $(RELATIONSVO) $(WELLFOUNDEDVO) $(REALSVO)

$(THEORIESVO): states/initial.coq

theories: $(THEORIESVO)

logic: $(LOGICVO)
arith: $(ARITHVO)
bool: $(BOOLVO)
zarith: $(ZARITHVO)
lists: $(LISTSVO)
sets: $(SETSVO)
relations: $(RELATIONSVO)
wellfounded: $(WELLFOUNDEDVO)
reals: $(REALSVO)

clean::
	rm -f theories/*/*.vo theories/*/*~
	rm -f tactics/*.vo tactics/*~


###########################################################################
# contribs
###########################################################################

OMEGAVO = contrib/omega/Omega.vo       contrib/omega/Zlogarithm.vo \
          contrib/omega/OmegaSyntax.vo contrib/omega/Zpower.vo \
          contrib/omega/Zcomplements.vo

RINGVO = contrib/ring/ArithRing.vo      contrib/ring/Ring_normalize.vo \
         contrib/ring/Ring_theory.vo    contrib/ring/Ring.vo \
         contrib/ring/ZArithRing.vo     contrib/ring/Ring_abstract.vo \
         contrib/ring/Quote.vo

#XMLVO = contrib/xml/Xml.vo
XMLVO=

CONTRIBVO = $(OMEGAVO) $(RINGVO) $(XMLVO)

$(CONTRIBVO): states/initial.coq

contrib: $(CONTRIBVO)
omega: $(OMEGAVO)
ring: $(RINGVO)
xml: $(XMLVO)

clean::
	rm -f contrib/*/*~ contrib/*/*.cm[io] contrib/*/*.vo

archclean::
	rm -f contrib/*/*.cmx contrib/*/*.[so]

###########################################################################
# tools
###########################################################################

COQDEP=bin/coqdep
COQMAKEFILE=bin/coq_makefile
GALLINA=bin/gallina
COQTEX=bin/coq-tex

tools: $(COQDEP) $(COQMAKEFILE) $(GALLINA) $(COQTEX) \
       tools/coq.elc dev/top_printers.cmo

COQDEPCMO=config/coq_config.cmo tools/coqdep_lexer.cmo tools/coqdep.cmo

$(COQDEP): $(COQDEPCMO)
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ unix.cma $(COQDEPCMO) $(OSDEPLIBS)

beforedepend:: tools/coqdep_lexer.ml $(COQDEP)

GALLINACMO=tools/gallina_lexer.cmo tools/gallina.cmo

$(GALLINA): $(GALLINACMO)
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ $(GALLINACMO)

beforedepend:: tools/gallina_lexer.ml

$(COQMAKEFILE): tools/coq_makefile.ml
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ tools/coq_makefile.ml

$(COQTEX): tools/coq-tex.ml
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ str.cma tools/coq-tex.ml

clean::
	rm -f tools/coqdep_lexer.ml tools/gallina_lexer.ml

archclean::
	rm -f $(COQDEP) $(GALLINA) $(COQTEX) $(COQMAKEFILE)

###########################################################################
# minicoq
###########################################################################

MINICOQCMO=$(CONFIG) $(LIB) $(KERNEL) \
	   parsing/lexer.cmo parsing/g_minicoq.cmo \
	   toplevel/fhimsg.cmo toplevel/minicoq.cmo

MINICOQ=bin/minicoq

$(MINICOQ): $(MINICOQCMO)
	$(OCAMLC) $(INCLUDES) -o $@ -custom $(CMA) $(MINICOQCMO) $(OSDEPLIBS)

archclean::
	rm -f $(MINICOQ)

###########################################################################
# Installation
###########################################################################

install: install-$(BEST) install-binaries install-library install-manpages

install-byte:
	$(MKDIR) $(BINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(BINDIR)
	cd $(BINDIR); ln -sf coqtop.byte coqtop

install-opt:
	$(MKDIR) $(BINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(COQTOPOPT) $(BINDIR)
	cd $(BINDIR); ln -sf coqtop.opt coqtop

install-binaries:
	$(MKDIR) $(BINDIR)
	cp $(COQDEP) $(GALLINA) $(COQMAKEFILE) $(COQTEX) $(BINDIR)

ALLVO=$(INITVO) $(TACTICSVO) $(THEORIESVO) $(CONTRIBVO)

install-library:
	$(MKDIR) $(COQLIB)
	for f in $(ALLVO); do \
	  $(MKDIR) $(COQLIB)/`dirname $$f`; \
	  cp $$f $(COQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(COQLIB)/states
	cp states/*.coq $(COQLIB)/states
	$(MKDIR) $(EMACSLIB)
	cp tools/coq.el tools/coq.elc $(EMACSLIB)

MANPAGES=tools/coq-tex.1 tools/coqdep.1 tools/gallina.1

install-manpages:
	$(MKDIR) $(MANDIR)/man1
	cp $(MANPAGES) $(MANDIR)/man1

###########################################################################
# Documentation
# Literate programming (with ocamlweb)
###########################################################################

.PHONY: doc

doc: doc/coq.tex
	$(MAKE) -C doc coq.ps minicoq.dvi

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

clean::
	rm -f doc/*~ doc/coq.tex

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

parsing/lexer.cmx: parsing/lexer.ml
	$(OCAMLOPT_P4O) -c $<

clean::
	rm -f parsing/lexer.ml

beforedepend:: parsing/lexer.ml

# grammar modules with camlp4

ML4FILES += parsing/q_coqast.ml4 parsing/g_prim.ml4 parsing/pcoq.ml4

GRAMMARCMO=lib/pp_control.cmo lib/pp.cmo lib/util.cmo lib/dyn.cmo \
	   lib/hashcons.cmo parsing/coqast.cmo parsing/lexer.cmo \
	   parsing/pcoq.cmo parsing/q_coqast.cmo parsing/g_prim.cmo

parsing/grammar.cma: $(GRAMMARCMO)
	$(OCAMLC) $(BYTEFLAGS) $(GRAMMARCMO) -linkall -a -o $@

clean::
	rm -f parsing/grammar.cma

ML4FILES +=parsing/g_basevernac.ml4 parsing/g_minicoq.ml4 \
	   parsing/g_vernac.ml4 parsing/g_proofs.ml4 parsing/g_cases.ml4 \
	   parsing/g_constr.ml4 parsing/g_tactic.ml4 parsing/extend.ml4    

beforedepend:: $(GRAMMARCMO)

beforedepend:: parsing/pcoq.ml parsing/extend.ml

# toplevel/mltop.ml4 (ifdef Byte)

toplevel/mltop.cmo: toplevel/mltop.byteml
	$(OCAMLC) $(BYTEFLAGS) -c -impl toplevel/mltop.byteml -o $@

toplevel/mltop.cmx: toplevel/mltop.optml
	$(OCAMLOPT) $(OPTFLAGS) -c -impl toplevel/mltop.optml -o $@

toplevel/mltop.byteml: toplevel/mltop.ml4
	$(CAMLP4O) $(CAMLP4EXTENDFLAGS) pr_o.cmo pa_ifdef.cmo -DByte -impl toplevel/mltop.ml4 > $@ || rm -f $@

toplevel/mltop.optml: toplevel/mltop.ml4
	$(CAMLP4O) $(CAMLP4EXTENDFLAGS) pr_o.cmo pa_ifdef.cmo -impl toplevel/mltop.ml4 > $@ || rm -f $@

toplevel/mltop.ml: toplevel/mltop.ml4
	$(CAMLP4O) $(CAMLP4EXTENDFLAGS) pr_o.cmo pa_ifdef.cmo -DByte -impl toplevel/mltop.ml4 > $@ || rm -f $@

ML4FILES += toplevel/mltop.ml4

clean::
	rm -f toplevel/mltop.ml toplevel/mltop.byteml toplevel/mltop.optml

###########################################################################
# Default rules
###########################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .ml4 .v .vo .el .elc

.ml.cmo:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -c $<

.mll.ml:
	ocamllex $<

.ml4.cmo:
	$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` -impl" -c -impl $<

.ml4.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` -impl" -c -impl $<

.ml4.ml:
	$(CAMLP4O) $(CAMLP4EXTENDFLAGS) pr_o.cmo `$(CAMLP4DEPS) $<` -impl $< > $@ || rm -f $@

.v.vo:
	$(COQC) -q -$(BEST) -bindir bin $(COQINCLUDES) $<

.el.elc:
	echo "(setq load-path (cons \".\" load-path))" > $*.compile
	echo "(byte-compile-file \"$<\")" >> $*.compile
	$(EMACS) -batch -l $*.compile
	rm -f $*.compile        

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
	rm -f tools/*.cmx tools/*.[so]
	rm -f scripts/*.cmx scripts/*.[so]
	rm -f dev/*.cmx dev/*.[so]

clean:: archclean
	rm -f *~
	rm -f gmon.out core
	rm -f config/*.cm[io] config/*~
	rm -f lib/*.cm[io] lib/*~
	rm -f kernel/*.cm[io] kernel/*~
	rm -f library/*.cm[io] library/*~
	rm -f proofs/*.cm[io] proofs/*~
	rm -f tactics/*.cm[io] tactics/*~
	rm -f parsing/*.cm[io] parsing/*.ppo parsing/*~
	rm -f pretyping/*.cm[io] pretyping/*~
	rm -f toplevel/*.cm[io] toplevel/*~
	rm -f tools/*.cm[io] tools/*~
	rm -f scripts/*.cm[io] scripts/*~
	rm -f dev/*.cm[io] dev/*~

cleanconfig::
	rm -f config/Makefile config/coq_config.ml

###########################################################################
# Dependencies
###########################################################################

alldepend: depend dependcoq dependcamlp4

depend: beforedepend
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend

dependcoq: beforedepend
	$(COQDEP) $(COQINCLUDES) */*.v */*/*.v > .depend.coq

ML4FILESML = $(ML4FILES:.ml4=.ml)
dependcamlp4: beforedepend $(ML4FILESML)
	ocamldep $(DEPFLAGS) $(ML4FILESML) > .depend.camlp4
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".ml: " >> .depend.camlp4; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend.camlp4; \
	done
	rm -f toplevel/mltop.ml

clean::
	rm -f $(ML4FILESML)

include .depend
include .depend.coq
include .depend.camlp4
