#######################################################################
#  v      #   The Coq Proof Assistant  /  The Coq Development Team    #
# <O___,, #        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              #
#   \VV/  #############################################################
#    //   #      This file is distributed under the terms of the      #
#         #       GNU Lesser General Public License Version 2.1       #
#######################################################################

# $Id$ 

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
              -I contrib/omega -I contrib/romega \
	      -I contrib/ring -I contrib/xml \
	      -I contrib/extraction -I contrib/correctness \
              -I contrib/interface -I contrib/fourier \
	      -I contrib/jprover

MLINCLUDES=$(LOCALINCLUDES) -I $(MYCAMLP4LIB)

BYTEFLAGS=$(MLINCLUDES) $(CAMLDEBUG)
OPTFLAGS=$(MLINCLUDES) $(CAMLTIMEPROF)
OCAMLDEP=ocamldep
DEPFLAGS=$(LOCALINCLUDES)

OCAMLC_P4O=$(OCAMLC) -pp $(CAMLP4O) $(BYTEFLAGS)
OCAMLOPT_P4O=$(OCAMLOPT) -pp $(CAMLP4O) $(OPTFLAGS)
CAMLP4EXTENDFLAGS=-I . pa_extend.cmo pa_extend_m.cmo pa_ifdef.cmo q_MLast.cmo
CAMLP4DEPS=sed -n -e 's|^(\*.*camlp4deps: "\(.*\)".*\*)$$|\1|p'

COQINCLUDES=          # coqtop includes itself the needed paths
GLOB=   # is "-dump-glob file" when making the doc

BOOTCOQTOP=$(BESTCOQTOP) -boot -$(BEST) $(COQINCLUDES) $(GLOB)

###########################################################################
# Objects files 
###########################################################################

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=config/coq_config.cmo

LIBREP=lib/pp_control.cmo lib/pp.cmo lib/util.cmo \
    lib/hashcons.cmo lib/dyn.cmo lib/system.cmo lib/options.cmo \
    lib/bstack.cmo lib/edit.cmo lib/gset.cmo lib/gmap.cmo \
    lib/tlm.cmo lib/bij.cmo lib/gmapl.cmo lib/profile.cmo lib/explore.cmo \
    lib/predicate.cmo lib/rtree.cmo  # Rem: Cygwin already uses variable LIB 

KERNEL=kernel/names.cmo kernel/univ.cmo \
       kernel/esubst.cmo kernel/term.cmo kernel/sign.cmo \
       kernel/declarations.cmo kernel/environ.cmo kernel/closure.cmo \
       kernel/conv_oracle.cmo kernel/reduction.cmo kernel/entries.cmo \
       kernel/modops.cmo \
       kernel/type_errors.cmo kernel/inductive.cmo kernel/typeops.cmo \
       kernel/indtypes.cmo kernel/cooking.cmo kernel/term_typing.cmo \
       kernel/subtyping.cmo kernel/mod_typing.cmo kernel/safe_typing.cmo

LIBRARY=library/libnames.cmo library/nameops.cmo library/libobject.cmo \
	library/summary.cmo \
        library/nametab.cmo library/global.cmo library/lib.cmo \
	library/declaremods.cmo library/library.cmo library/states.cmo \
	library/impargs.cmo library/declare.cmo library/goptions.cmo 

PRETYPING=pretyping/termops.cmo \
          pretyping/evd.cmo pretyping/instantiate.cmo \
          pretyping/reductionops.cmo pretyping/inductiveops.cmo \
          pretyping/rawterm.cmo pretyping/detyping.cmo pretyping/retyping.cmo \
	  pretyping/cbv.cmo pretyping/tacred.cmo \
	  pretyping/pretype_errors.cmo pretyping/typing.cmo \
	  pretyping/classops.cmo pretyping/recordops.cmo pretyping/indrec.cmo \
	  pretyping/evarutil.cmo pretyping/evarconv.cmo \
          pretyping/coercion.cmo pretyping/cases.cmo pretyping/pretyping.cmo \
	  pretyping/syntax_def.cmo pretyping/pattern.cmo 

PARSING=parsing/lexer.cmo parsing/coqast.cmo \
        parsing/genarg.cmo proofs/tacexpr.cmo parsing/ast.cmo \
        parsing/termast.cmo parsing/astterm.cmo \
	parsing/extend.cmo parsing/esyntax.cmo \
        parsing/ppconstr.cmo parsing/printer.cmo parsing/pptactic.cmo \
	parsing/coqlib.cmo parsing/prettyp.cmo parsing/search.cmo

HIGHPARSING= parsing/g_prim.cmo parsing/g_basevernac.cmo \
	parsing/g_vernac.cmo parsing/g_proofs.cmo parsing/g_tactic.cmo \
	parsing/g_ltac.cmo parsing/g_constr.cmo parsing/g_cases.cmo \
	parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo

ARITHSYNTAX=parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo

PROOFS=proofs/proof_type.cmo proofs/proof_trees.cmo proofs/logic.cmo \
       proofs/refiner.cmo proofs/evar_refiner.cmo proofs/tacmach.cmo \
       proofs/clenv.cmo proofs/pfedit.cmo \
       proofs/tactic_debug.cmo

TACTICS=tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
        tactics/nbtermdn.cmo tactics/hipattern.cmo tactics/wcclausenv.cmo \
        tactics/tacticals.cmo tactics/tactics.cmo \
        tactics/hiddentac.cmo tactics/elim.cmo \
	tactics/dhyp.cmo tactics/auto.cmo tactics/tacinterp.cmo

TOPLEVEL=toplevel/himsg.cmo toplevel/cerrors.cmo toplevel/class.cmo \
	 toplevel/command.cmo toplevel/record.cmo toplevel/recordobj.cmo \
         toplevel/discharge.cmo toplevel/vernacexpr.cmo \
         toplevel/vernacinterp.cmo toplevel/mltop.cmo \
         parsing/pcoq.cmo parsing/egrammar.cmo toplevel/metasyntax.cmo \
         toplevel/vernacentries.cmo toplevel/vernac.cmo \
	 toplevel/line_oriented_parser.cmo toplevel/protectedtoplevel.cmo \
         toplevel/toplevel.cmo toplevel/usage.cmo \
	 toplevel/coqinit.cmo toplevel/coqtop.cmo

HIGHTACTICS=tactics/setoid_replace.cmo tactics/equality.cmo \
            tactics/contradiction.cmo tactics/inv.cmo tactics/leminv.cmo \
            tactics/autorewrite.cmo tactics/refine.cmo \
	    tactics/extraargs.cmo tactics/extratactics.cmo tactics/eauto.cmo

QUOTIFY=parsing/qast.cmo parsing/q_prim.cmo parsing/q_tactic.cmo

parsing/q_prim.ml4: parsing/g_prim.ml4
	camlp4o -I parsing grammar.cma pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -o parsing/q_prim.ml4 -impl parsing/g_prim.ml4

parsing/q_tactic.ml4: parsing/g_tactic.ml4
	camlp4o -I parsing grammar.cma pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -o parsing/q_tactic.ml4 -impl parsing/g_tactic.ml4

parsing/q_ltac.ml4: parsing/g_ltac.ml4
	camlp4o -I parsing grammar.cma pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -o parsing/q_ltac.ml4 -impl parsing/g_ltac.ml4

SPECTAC= tactics/tauto.ml4 tactics/eqdecide.ml4
USERTAC = $(SPECTAC)
ML4FILES += $(USERTAC) tactics/extraargs.ml4 tactics/extratactics.ml4 \
	tactics/eauto.ml4 

USERTACCMO=$(USERTAC:.ml4=.cmo)
USERTACCMX=$(USERTAC:.ml4=.cmx)

INTERFACE=contrib/interface/vtp.cmo \
	contrib/interface/ctast.cmo contrib/interface/xlate.cmo \
	contrib/interface/paths.cmo contrib/interface/translate.cmo \
	contrib/interface/pbp.cmo \
	contrib/interface/dad.cmo \
	contrib/interface/history.cmo \
	contrib/interface/name_to_ast.cmo contrib/interface/debug_tac.cmo \
	contrib/interface/showproof_ct.cmo contrib/interface/showproof.cmo \
	contrib/interface/blast.cmo contrib/interface/centaur.cmo

ML4FILES += contrib/interface/debug_tac.ml4 contrib/interface/centaur.ml4

PARSERREQUIRES=config/coq_config.cmo lib/pp_control.cmo lib/pp.cmo \
	lib/util.cmo lib/dyn.cmo lib/gmap.cmo lib/gmapl.cmo \
        lib/predicate.cmo lib/hashcons.cmo lib/profile.cmo \
        lib/system.cmo lib/bstack.cmo lib/edit.cmo lib/options.cmo \
	lib/rtree.cmo lib/gset.cmo lib/tlm.cmo \
        kernel/names.cmo kernel/univ.cmo kernel/esubst.cmo \
        kernel/term.cmo kernel/sign.cmo kernel/declarations.cmo \
	kernel/environ.cmo \
	kernel/closure.cmo kernel/conv_oracle.cmo kernel/reduction.cmo \
	kernel/type_errors.cmo kernel/inductive.cmo kernel/typeops.cmo \
	kernel/indtypes.cmo kernel/cooking.cmo kernel/safe_typing.cmo \
	library/libnames.cmo library/nameops.cmo library/libobject.cmo \
	library/summary.cmo library/nametab.cmo library/lib.cmo \
	library/global.cmo library/library.cmo lib/options.cmo \
	library/impargs.cmo library/goptions.cmo \
	pretyping/evd.cmo pretyping/instantiate.cmo \
        pretyping/termops.cmo \
        pretyping/reductionops.cmo pretyping/retyping.cmo library/declare.cmo \
        pretyping/cbv.cmo pretyping/tacred.cmo pretyping/classops.cmo \
        pretyping/rawterm.cmo \
        pretyping/pattern.cmo pretyping/pretype_errors.cmo \
	pretyping/evarutil.cmo pretyping/recordops.cmo pretyping/evarconv.cmo \
	pretyping/coercion.cmo pretyping/inductiveops.cmo pretyping/cases.cmo \
        pretyping/indrec.cmo \
	pretyping/pretyping.cmo pretyping/syntax_def.cmo \
	parsing/lexer.cmo parsing/coqast.cmo parsing/genarg.cmo \
	proofs/tacexpr.cmo toplevel/vernacexpr.cmo \
	parsing/pcoq.cmo parsing/ast.cmo \
	parsing/g_prim.cmo parsing/g_basevernac.cmo \
	parsing/extend.cmo \
	parsing/coqlib.cmo pretyping/detyping.cmo \
	parsing/termast.cmo parsing/astterm.cmo \
	parsing/egrammar.cmo parsing/esyntax.cmo toplevel/metasyntax.cmo \
	parsing/ppconstr.cmo parsing/printer.cmo parsing/pptactic.cmo \
	lib/stamps.cmo pretyping/typing.cmo \
	proofs/proof_trees.cmo proofs/logic.cmo proofs/refiner.cmo \
	proofs/evar_refiner.cmo proofs/tacmach.cmo toplevel/himsg.cmo \
	parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo \
	toplevel/class.cmo toplevel/recordobj.cmo toplevel/cerrors.cmo \
	parsing/g_vernac.cmo parsing/g_proofs.cmo parsing/g_tactic.cmo \
	parsing/g_ltac.cmo parsing/g_constr.cmo parsing/g_cases.cmo \
	proofs/tactic_debug.cmo \
	proofs/pfedit.cmo proofs/clenv.cmo tactics/wcclausenv.cmo \
	tactics/tacticals.cmo tactics/hipattern.cmo \
	tactics/tactics.cmo tactics/hiddentac.cmo \
	tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
	tactics/nbtermdn.cmo tactics/dhyp.cmo tactics/elim.cmo \
	tactics/auto.cmo tactics/tacinterp.cmo tactics/extraargs.cmo \
	$(CMO) # Solution de facilit�...

ML4FILES += contrib/correctness/psyntax.ml4 contrib/omega/g_omega.ml4 \
         contrib/romega/g_romega.ml4 contrib/ring/g_quote.ml4 \
	 contrib/ring/g_ring.ml4 \
         contrib/field/field.ml4 contrib/fourier/g_fourier.ml4 \
	 contrib/extraction/g_extraction.ml4 contrib/xml/xmlentries.ml4

OMEGACMO=contrib/omega/omega.cmo contrib/omega/coq_omega.cmo \
         contrib/omega/g_omega.cmo 

ROMEGACMO=contrib/romega/const_omega.cmo contrib/romega/refl_omega.cmo \
         contrib/romega/g_romega.cmo 

RINGCMO=contrib/ring/quote.cmo contrib/ring/g_quote.cmo \
	contrib/ring/ring.cmo contrib/ring/g_ring.cmo 

FIELDCMO=contrib/field/field.cmo 

XMLCMO=contrib/xml/xml.cmo \
       contrib/xml/xmlcommand.cmo contrib/xml/xmlentries.cmo 	

FOURIERCMO=contrib/fourier/fourier.cmo contrib/fourier/fourierR.cmo \
        contrib/fourier/g_fourier.cmo

EXTRACTIONCMO=contrib/extraction/table.cmo\
	      contrib/extraction/mlutil.cmo\
	      contrib/extraction/ocaml.cmo \
	      contrib/extraction/haskell.cmo \
	      contrib/extraction/extraction.cmo \
              contrib/extraction/common.cmo \
	      contrib/extraction/extract_env.cmo \
	      contrib/extraction/g_extraction.cmo

CORRECTNESSCMO=contrib/correctness/pmisc.cmo				\
	contrib/correctness/peffect.cmo contrib/correctness/prename.cmo	\
	contrib/correctness/perror.cmo contrib/correctness/penv.cmo	\
	contrib/correctness/putil.cmo contrib/correctness/pdb.cmo	\
	contrib/correctness/pcic.cmo contrib/correctness/pmonad.cmo	\
	contrib/correctness/pcicenv.cmo					\
	contrib/correctness/pred.cmo contrib/correctness/ptyping.cmo	\
	contrib/correctness/pwp.cmo contrib/correctness/pmlize.cmo	\
	contrib/correctness/ptactic.cmo	contrib/correctness/psyntax.cmo

JPROVERCMO=contrib/jprover/opname.cmo \
           contrib/jprover/jterm.cmo contrib/jprover/jlogic.cmo \
           contrib/jprover/jtunify.cmo contrib/jprover/jall.cmo \
           contrib/jprover/jprover.cmo

ML4FILES += contrib/jprover/jprover.ml4

CONTRIB=$(OMEGACMO) $(ROMEGACMO) $(RINGCMO) $(FIELDCMO) \
	$(FOURIERCMO) 

#later 	$(EXTRACTIONCMO) $(CORRECTNESSCMO) $(JPROVERCMO)
#later :) $(XMLCMO)
#$(OMEGACMO) $(RINGCMO)

CMA=$(CLIBS) $(CAMLP4OBJS)
CMXA=$(CMA:.cma=.cmxa)

CMO=$(CONFIG) $(LIBREP) $(KERNEL) $(LIBRARY) $(PRETYPING)  \
    $(PROOFS) $(TACTICS) $(PARSING) $(TOPLEVEL) $(HIGHPARSING) $(HIGHTACTICS) $(CONTRIB)
CMX=$(CMO:.cmo=.cmx)

###########################################################################
# Main targets (coqmktop, coqtop.opt, coqtop.byte)
###########################################################################

COQMKTOP=bin/coqmktop$(EXE)
COQC=bin/coqc$(EXE)
COQTOPBYTE=bin/coqtop.byte$(EXE)
COQTOPOPT=bin/coqtop.opt$(EXE)
BESTCOQTOP=bin/coqtop.$(BEST)$(EXE)
COQTOP=bin/coqtop$(EXE)
COQINTERFACE=bin/coq-interface$(EXE) bin/parser$(EXE)

COQBINARIES= $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(BESTCOQTOP) $(COQTOP) \
             $(COQINTERFACE) 

coqbinaries:: ${COQBINARIES}

world: coqbinaries states theories contrib tools

$(COQTOPOPT): $(COQMKTOP) $(CMX) $(USERTACCMX)
	$(COQMKTOP) -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQTOPBYTE): $(COQMKTOP) $(CMO) $(USERTACCMO)
	$(COQMKTOP) -top $(LOCALINCLUDES) $(CAMLDEBUG) -o $@

$(COQTOP):
	cd bin; ln -sf coqtop.$(BEST)$(EXE) coqtop$(EXE)

# coqmktop 

COQMKTOPCMO=$(CONFIG) scripts/tolink.cmo scripts/coqmktop.cmo 

$(COQMKTOP): $(COQMKTOPCMO)
	$(OCAMLC) $(BYTEFLAGS) -o $@ -custom str.cma unix.cma \
          $(COQMKTOPCMO) $(OSDEPLIBS)

scripts/tolink.ml: Makefile
	echo "let lib = \""$(LIBREP)"\"" > $@
	echo "let kernel = \""$(KERNEL)"\"" >> $@
	echo "let library = \""$(LIBRARY)"\"" >> $@
	echo "let pretyping = \""$(PRETYPING)"\"" >> $@
	echo "let parsing = \""$(PARSING)"\"" >> $@
	echo "let proofs = \""$(PROOFS)"\"" >> $@
	echo "let tactics = \""$(TACTICS)"\"" >> $@
	echo "let toplevel = \""$(TOPLEVEL)"\"" >> $@
	echo "let highparsing = \""$(HIGHPARSING)"\"" >> $@
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
	rm -f $(COQTOP)

# we provide targets for each subdirectory

lib: $(LIBREP)
kernel: $(KERNEL)
library: $(LIBRARY)
proofs: $(PROOFS)
tactics: $(TACTICS)
parsing: $(PARSING)
pretyping: $(PRETYPING)
highparsing: $(HIGHPARSING)
toplevel: $(TOPLEVEL)
hightactics: $(HIGHTACTICS)

# special binaries for debugging

bin/coq-interface$(EXE): $(COQMKTOP) $(CMO) $(USERTACCMO) $(INTERFACE)
	$(COQMKTOP) -top $(BYTEFLAGS) -o $@ $(INTERFACE)

bin/parser$(EXE): contrib/interface/ctast.cmo contrib/interface/parse.cmo contrib/interface/line_parser.cmo $(PARSERREQUIRES) contrib/interface/xlate.cmo contrib/interface/vtp.cmo
	$(OCAMLC) -cclib -lunix -custom $(MLINCLUDES) -o $@ $(CMA) \
	$(PARSERREQUIRES) \
	ctast.cmo line_parser.cmo vtp.cmo xlate.cmo parse.cmo

clean::
	rm -f bin/parser$(EXE) bin/coq-interface$(EXE)

###########################################################################
# tests
###########################################################################

check:: $(BESTCOQTOP)
	cd test-suite; ./check -$(BEST)

###########################################################################
# theories and states
###########################################################################

states:: states/barestate.coq states/initial.coq

SYNTAXPP=syntax/PPConstr.v syntax/PPCases.v

states/barestate.coq: $(SYNTAXPP) $(BESTCOQTOP)
	$(BESTCOQTOP) -boot -batch -silent -nois -I syntax -load-vernac-source syntax/MakeBare.v -outputstate states/barestate.coq

#       theories/Init/DatatypesHints.vo   theories/Init/PeanoHints.vo \
#       theories/Init/LogicHints.vo       theories/Init/SpecifHints.vo \
#       theories/Init/Logic_TypeHints.vo \

INITVO=theories/Init/Datatypes.vo         theories/Init/Peano.vo         \
       theories/Init/DatatypesSyntax.vo   theories/Init/Prelude.vo       \
       theories/Init/Logic.vo             theories/Init/Specif.vo        \
       theories/Init/LogicSyntax.vo       theories/Init/SpecifSyntax.vo  \
       theories/Init/Logic_Type.vo        theories/Init/Wf.vo            \
       theories/Init/Logic_TypeSyntax.vo

theories/Init/%.vo: theories/Init/%.v states/barestate.coq $(COQC)
	$(BOOTCOQTOP) -is states/barestate.coq -compile $*

init: $(INITVO)

EXTRACTIONVO=

TACTICSVO=$(EXTRACTIONVO)

tactics/%.vo: tactics/%.v states/barestate.coq $(COQC)
	$(BOOTCOQTOP) -is states/barestate.coq -compile $*

contrib/extraction/%.vo: contrib/extraction/%.v states/barestate.coq $(COQC)
	$(BOOTCOQTOP) -is states/barestate.coq -compile $*

states/initial.coq: states/barestate.coq states/MakeInitial.v $(INITVO) $(TACTICSVO) $(BESTCOQTOP)
	$(BOOTCOQTOP) -batch -silent -is states/barestate.coq -load-vernac-source states/MakeInitial.v -outputstate states/initial.coq

clean::
	rm -f states/*.coq

LOGICVO=theories/Logic/Hurkens.vo          theories/Logic/ProofIrrelevance.vo\
      theories/Logic/Classical.vo          theories/Logic/Classical_Type.vo \
      theories/Logic/Classical_Pred_Set.vo   theories/Logic/Eqdep.vo          \
      theories/Logic/Classical_Pred_Type.vo  theories/Logic/Classical_Prop.vo \
      theories/Logic/Berardi.vo       	     theories/Logic/Eqdep_dec.vo \
      theories/Logic/Decidable.vo            theories/Logic/JMeq.vo

ARITHVO=theories/Arith/ArithSyntax.vo \
	theories/Arith/Arith.vo         theories/Arith/Gt.vo          \
	theories/Arith/Between.vo       theories/Arith/Le.vo          \
	theories/Arith/Compare.vo       theories/Arith/Lt.vo          \
	theories/Arith/Compare_dec.vo   theories/Arith/Min.vo         \
	theories/Arith/Div2.vo          theories/Arith/Minus.vo       \
	theories/Arith/Mult.vo          theories/Arith/Even.vo        \
	theories/Arith/EqNat.vo         theories/Arith/Peano_dec.vo   \
	theories/Arith/Euclid.vo        theories/Arith/Plus.vo        \
	theories/Arith/Wf_nat.vo  	theories/Arith/Max.vo	      \
#	theories/Arith/Div.vo 

SORTINGVO=theories/Sorting/Heap.vo \
	theories/Sorting/Permutation.vo \
	theories/Sorting/Sorting.vo
 
BOOLVO=theories/Bool/Bool.vo  		theories/Bool/IfProp.vo \
       theories/Bool/Zerob.vo 		theories/Bool/DecBool.vo \
	theories/Bool/Sumbool.vo 	theories/Bool/BoolEq.vo

ZARITHVO=theories/ZArith/Wf_Z.vo        theories/ZArith/Zsyntax.vo \
	 theories/ZArith/ZArith.vo      theories/ZArith/auxiliary.vo \
	 theories/ZArith/ZArith_dec.vo  theories/ZArith/fast_integer.vo \
	 theories/ZArith/Zmisc.vo       theories/ZArith/zarith_aux.vo \
	 theories/ZArith/Zhints.vo	theories/ZArith/Zlogarithm.vo \
	 theories/ZArith/Zpower.vo 	theories/ZArith/Zcomplements.vo \
	 theories/ZArith/Zdiv.vo

LISTSVO=theories/Lists/List.vo      theories/Lists/PolyListSyntax.vo \
        theories/Lists/ListSet.vo   theories/Lists/Streams.vo \
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

INTMAPVO=theories/IntMap/Adalloc.vo    theories/IntMap/Mapcanon.vo \
theories/IntMap/Addec.vo      theories/IntMap/Mapcard.vo \
theories/IntMap/Addr.vo       theories/IntMap/Mapc.vo \
theories/IntMap/Adist.vo      theories/IntMap/Mapfold.vo \
theories/IntMap/Allmaps.vo    theories/IntMap/Mapiter.vo \
theories/IntMap/Fset.vo       theories/IntMap/Maplists.vo \
theories/IntMap/Lsort.vo      theories/IntMap/Mapsubset.vo \
theories/IntMap/Mapaxioms.vo  theories/IntMap/Map.vo \


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

REALSVO=theories/Reals/TypeSyntax.vo \
	theories/Reals/Rdefinitions.vo theories/Reals/Rsyntax.vo \
	theories/Reals/Raxioms.vo      theories/Reals/Rbase.vo \
	theories/Reals/DiscrR.vo       theories/Reals/R_Ifp.vo \
	theories/Reals/Rbasic_fun.vo   theories/Reals/R_sqr.vo \
	theories/Reals/SplitAbsolu.vo  theories/Reals/SplitRmult.vo \
	theories/Reals/Rfunctions.vo   theories/Reals/Rlimit.vo \
	theories/Reals/Rderiv.vo       theories/Reals/Rseries.vo \
	theories/Reals/Rtrigo_fun.vo   theories/Reals/Rsigma.vo \
	theories/Reals/Rtrigo.vo       theories/Reals/Ranalysis.vo \
	theories/Reals/Rgeom.vo        theories/Reals/Reals.vo 

SETOIDSVO=theories/Setoids/Setoid.vo

THEORIESVO = $(LOGICVO) $(ARITHVO) $(BOOLVO) $(ZARITHVO) $(LISTSVO) \
             $(SETSVO) $(INTMAPVO) $(RELATIONSVO) $(WELLFOUNDEDVO) \
	     $(REALSVO) $(SETOIDSVO) $(SORTINGVO)

$(THEORIESVO): states/initial.coq

theories: $(THEORIESVO)

logic: $(LOGICVO)
arith: $(ARITHVO)
bool: $(BOOLVO)
zarith: $(ZARITHVO)
lists: $(LISTSVO)
sets: $(SETSVO)
intmap: $(INTMAPVO)
relations: $(RELATIONSVO)
wellfounded: $(WELLFOUNDEDVO)
reals: $(REALSVO)
sorting: $(SORTINGVO)

# globalizations (for coqdoc)

glob.dump::
	rm -f glob.dump
	rm -f theories/*/*.vo
	make GLOB="-dump-glob glob.dump" world

clean::
	rm -f theories/*/*.vo
	rm -f tactics/*.vo


###########################################################################
# contribs
###########################################################################

CORRECTNESSVO=contrib/correctness/Arrays.vo				\
	contrib/correctness/Correctness.vo				\
	contrib/correctness/Exchange.vo					\
	contrib/correctness/ArrayPermut.vo				\
	contrib/correctness/ProgBool.vo contrib/correctness/ProgInt.vo	\
	contrib/correctness/ProgWf.vo contrib/correctness/Sorted.vo	\
	contrib/correctness/Tuples.vo
#	contrib/correctness/ProgramsExtraction.vo			

OMEGAVO = contrib/omega/Omega.vo

ROMEGAVO = contrib/romega/ReflOmegaCore.vo contrib/romega/ROmega.vo 

RINGVO = contrib/ring/ArithRing.vo      contrib/ring/Ring_normalize.vo \
         contrib/ring/Ring_theory.vo    contrib/ring/Ring.vo \
         contrib/ring/ZArithRing.vo     contrib/ring/Ring_abstract.vo \
         contrib/ring/Quote.vo		contrib/ring/Setoid_ring_normalize.vo \
	 contrib/ring/Setoid_ring.vo	contrib/ring/Setoid_ring_theory.vo

FIELDVO = contrib/field/Field_Compl.vo     contrib/field/Field_Theory.vo \
          contrib/field/Field_Tactic.vo    contrib/field/Field.vo

XMLVO = Xml.vo

INTERFACEV0 = contrib/interface/Centaur.vo contrib/interface/vernacrc

FOURIERVO = contrib/fourier/Fourier_util.vo    contrib/fourier/Fourier.vo

JPROVERVO = 

contrib/interface/Centaur.vo: contrib/interface/Centaur.v $(INTERFACE)
	$(BESTCOQTOP) -boot -byte  $(COQINCLUDES) -compile $*

contrib/interface/AddDad.vo: contrib/interface/AddDad.v $(INTERFACE) states/initial.coq
	$(BESTCOQTOP) -boot -byte  $(COQINCLUDES) -compile $*

CONTRIBVO = $(OMEGAVO) $(ROMEGAVO) $(RINGVO) $(FIELDVO) $(XMLVO) \
	    $(CORRECTNESSVO) $(FOURIERVO) \
	    $(JPROVERVO) $(INTERFACEV0)

$(CONTRIBVO): states/initial.coq

contrib: $(CONTRIBVO) $(CONTRIBCMO)
omega: $(OMEGAVO) $(OMEGACMO) $(ROMEGAVO) $(ROMEGACMO)
ring: $(RINGVO) $(RINGCMO)
# xml_ instead of xml to avoid conflict with "make xml"
xml_: $(XMLVO) $(XMLCMO)
extraction: $(EXTRACTIONCMO) $(EXTRACTIONVO)
correctness: $(CORRECTNESSCMO) $(CORRECTNESSVO)
field: $(FIELDVO) $(FIELDCMO)
fourier: $(FOURIERVO) $(FOURIERCMO)
jprover: $(JPROVERVO) $(JPROVERCMO)

ALLVO = $(INITVO) $(THEORIESVO) $(CONTRIBVO) $(EXTRACTIONVO)

clean::
	rm -f contrib/*/*.cm[io] contrib/*/*.vo

archclean::
	rm -f contrib/*/*.cmx contrib/*/*.[so]

###########################################################################
# tools
###########################################################################

COQDEP=bin/coqdep$(EXE)
COQMAKEFILE=bin/coq_makefile$(EXE)
GALLINA=bin/gallina$(EXE)
COQTEX=bin/coq-tex$(EXE)
COQVO2XML=bin/coq_vo2xml$(EXE)
RUNCOQVO2XML=coq_vo2xml$(EXE)   # Uses the one in PATH and not the one in bin

tools:: $(COQDEP) $(COQMAKEFILE) $(GALLINA) $(COQTEX) $(COQVO2XML) dev/top_printers.cmo

COQDEPCMO=config/coq_config.cmo tools/coqdep_lexer.cmo tools/coqdep.cmo

$(COQDEP): $(COQDEPCMO)
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ unix.cma $(COQDEPCMO) $(OSDEPLIBS)

beforedepend:: tools/coqdep_lexer.ml $(COQDEP)

GALLINACMO=tools/gallina_lexer.cmo tools/gallina.cmo

$(GALLINA): $(GALLINACMO)
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ $(GALLINACMO)

beforedepend:: tools/gallina_lexer.ml

$(COQMAKEFILE): tools/coq_makefile.cmo
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ tools/coq_makefile.cmo

$(COQTEX): tools/coq-tex.cmo
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ str.cma tools/coq-tex.cmo

COQVO2XMLCMO=$(CONFIG) toplevel/usage.cmo tools/coq_vo2xml.cmo

$(COQVO2XML): $(COQVO2XMLCMO)
	$(OCAMLC) $(BYTEFLAGS) -custom -o $@ unix.cma $(COQVO2XMLCMO)

clean::
	rm -f tools/coqdep_lexer.ml tools/gallina_lexer.ml

archclean::
	rm -f $(COQDEP) $(GALLINA) $(COQTEX) $(COQMAKEFILE) $(COQVO2XML)

###########################################################################
# minicoq
###########################################################################

MINICOQCMO=$(CONFIG) $(LIBREP) $(KERNEL) \
	   parsing/lexer.cmo parsing/g_minicoq.cmo \
	   toplevel/fhimsg.cmo toplevel/minicoq.cmo

MINICOQ=bin/minicoq$(EXE)

$(MINICOQ): $(MINICOQCMO)
	$(OCAMLC) $(BYTEFLAGS) -o $@ -custom $(CMA) $(MINICOQCMO) $(OSDEPLIBS)

archclean::
	rm -f $(MINICOQ)

###########################################################################
# XML
###########################################################################

# Warning: coq_vo2xml in PATH and not the one in bin is used

.PHONY: xml
xml: .xml_time_stamp
.xml_time_stamp: $(INITVO) $(TACTICSVO) $(THEORIESVO) $(CONTRIBVO)
	$(RUNCOQVO2XML) -boot -byte $(COQINCLUDES) $(?:%.o=%)
	touch .xml_time_stamp

###########################################################################
# Installation
###########################################################################

COQINSTALLPREFIX=
  # Can be changed for a local installation (to make packages).
  # You must put a "/" at the end (Cygnus for win32 does not like "//").

FULLBINDIR=$(COQINSTALLPREFIX)$(BINDIR)
FULLCOQLIB=$(COQINSTALLPREFIX)$(COQLIB)
FULLMANDIR=$(COQINSTALLPREFIX)$(MANDIR)
FULLEMACSLIB=$(COQINSTALLPREFIX)$(EMACSLIB)

install: install-$(BEST) install-binaries install-library install-manpages

install-byte:
	$(MKDIR) $(FULLBINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqtop.byte$(EXE) coqtop$(EXE)

install-opt:
	$(MKDIR) $(FULLBINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(COQTOPOPT) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqtop.opt$(EXE) coqtop$(EXE)

install-binaries:
	$(MKDIR) $(FULLBINDIR)
	cp $(COQDEP) $(GALLINA) $(COQMAKEFILE) $(COQTEX) $(COQINTERFACE) $(COQVO2XML) $(FULLBINDIR)

LIBFILES=$(INITVO) $(TACTICSVO) $(THEORIESVO) $(CONTRIBVO)

install-library:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(LIBFILES); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states
	cp states/*.coq $(FULLCOQLIB)/states
	$(MKDIR) $(FULLEMACSLIB)
	cp tools/coq.el tools/coq-inferior.el $(FULLEMACSLIB)

MANPAGES=man/coq-tex.1 man/coqdep.1 man/gallina.1 \
	man/coqc.1 man/coqtop.1 man/coqtop.byte.1 man/coqtop.opt.1 \
	man/coq_makefile.1 man/coqmktop.1 \
	man/coq-interface.1 man/parser.1 man/coq_vo2xml.1

install-manpages:
	$(MKDIR) $(FULLMANDIR)/man1
	cp $(MANPAGES) $(FULLMANDIR)/man1

###########################################################################
# Documentation
# Literate programming (with ocamlweb)
###########################################################################

.PHONY: doc

doc: doc/coq.tex
	$(MAKE) -C doc coq.ps minicoq.dvi

LPLIB = lib/doc.tex $(LIBREP:.cmo=.mli)
LPKERNEL = kernel/doc.tex $(KERNEL:.cmo=.mli)
LPLIBRARY = library/doc.tex $(LIBRARY:.cmo=.mli)
LPPRETYPING = pretyping/doc.tex pretyping/rawterm.mli $(PRETYPING:.cmo=.mli)
LPPARSING =$(PARSING:.cmo=.mli) $(HIGHPARSING:.cmo=.mli)
LPPROOFS = proofs/doc.tex $(PROOFS:.cmo=.mli)
LPTACTICS = tactics/doc.tex $(TACTICS:.cmo=.mli) $(HIGHTACTICS:.cmo=.mli)
LPTOPLEVEL = toplevel/doc.tex $(TOPLEVEL:.cmo=.mli)
LPFILES = doc/macros.tex doc/intro.tex $(LPLIB) $(LPKERNEL) $(LPLIBRARY) \
	  $(LPPRETYPING) $(LPPROOFS) $(LPTACTICS) $(LPTOPLEVEL)

doc/coq.tex: $(LPFILES)
	ocamlweb -p "\usepackage{epsfig}" $(LPFILES) -o doc/coq.tex
#	ocamlweb $(LPFILES) -o doc/coq.tex

clean::
	rm -f doc/coq.tex

###########################################################################
# Emacs tags
###########################################################################

tags:
	find . -name "*.ml[,i,4]" | sort -r | xargs \
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

# grammar modules with camlp4

ML4FILES += parsing/lexer.ml4 parsing/q_util.ml4 parsing/q_coqast.ml4 \
            parsing/g_prim.ml4 parsing/pcoq.ml4

CAMLP4EXTENSIONS= parsing/tacextend.cmo parsing/vernacextend.cmo 

GRAMMARCMO=lib/pp_control.cmo lib/pp.cmo lib/util.cmo \
	   lib/dyn.cmo lib/options.cmo \
	   lib/hashcons.cmo lib/predicate.cmo lib/rtree.cmo \
	   $(KERNEL) \
	   library/libnames.cmo \
	   library/summary.cmo library/nameops.cmo \
	   library/nametab.cmo \
	   library/libobject.cmo library/lib.cmo library/goptions.cmo \
	   pretyping/rawterm.cmo pretyping/evd.cmo \
	   parsing/coqast.cmo parsing/genarg.cmo \
	   proofs/tacexpr.cmo proofs/proof_type.cmo parsing/ast.cmo \
           parsing/lexer.cmo parsing/q_util.cmo parsing/extend.cmo \
           toplevel/vernacexpr.cmo parsing/pcoq.cmo parsing/q_coqast.cmo \
           parsing/egrammar.cmo parsing/g_prim.cmo $(CAMLP4EXTENSIONS)

parsing/grammar.cma: $(GRAMMARCMO)
	$(OCAMLC) $(BYTEFLAGS) $(GRAMMARCMO) -linkall -a -o $@

clean::
	rm -f parsing/grammar.cma

ML4FILES +=parsing/g_basevernac.ml4 parsing/g_minicoq.ml4 \
	   parsing/g_vernac.ml4 parsing/g_proofs.ml4 parsing/g_cases.ml4 \
	   parsing/g_constr.ml4 parsing/g_tactic.ml4 parsing/g_ltac.ml4 \
	   parsing/tacextend.ml4 parsing/vernacextend.ml4

# beforedepend:: $(GRAMMARCMO)

# beforedepend:: parsing/pcoq.ml parsing/extend.ml

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
	rm -f toplevel/mltop.byteml toplevel/mltop.optml

# files compiled with -rectypes

kernel/term.cmo: kernel/term.ml
	$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

kernel/term.cmx: kernel/term.ml
	$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

library/nametab.cmo: library/nametab.ml
	$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

library/nametab.cmx: library/nametab.ml
	$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

# files compiled with camlp4 because of streams syntax

ML4FILES += lib/pp.ml4 			\
	 contrib/xml/xml.ml4		\
	 contrib/xml/xmlcommand.ml4	\
	 contrib/interface/line_parser.ml4	\
	 tools/coq_makefile.ml4		\
	 tools/coq-tex.ml4



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

.ml4.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` -impl" -c -impl $<

.ml4.cmo:
	$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` -impl" -c -impl $<

.v.vo:
	$(BOOTCOQTOP) -compile $*

.el.elc:
	echo "(setq load-path (cons \".\" load-path))" > $*.compile
	echo "(byte-compile-file \"$<\")" >> $*.compile
	- $(EMACS) -batch -l $*.compile
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
	rm -f *~ */*~ */*/*~
	rm -f gmon.out core
	rm -f config/*.cm[io]
	rm -f lib/*.cm[io]
	rm -f kernel/*.cm[io]
	rm -f library/*.cm[io]
	rm -f proofs/*.cm[io]
	rm -f tactics/*.cm[io]
	rm -f parsing/*.cm[io] parsing/*.ppo
	rm -f pretyping/*.cm[io]
	rm -f toplevel/*.cm[io]
	rm -f tools/*.cm[io]
	rm -f scripts/*.cm[io]
	rm -f dev/*.cm[io]
	rm -f */*.pp[iox] contrib/*/*.pp[iox]

cleanconfig::
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-v7

###########################################################################
# Dependencies
###########################################################################

alldepend: depend dependcoq 

dependcoq: beforedepend
	$(COQDEP) $(COQINCLUDES) $(ALLVO:.vo=.v) > .depend.coq

# Computing the dependencies in camlp4 files is tricky.
# We proceed in several steps:

ML4FILESML = $(ML4FILES:.ml4=.ml)

ml4filesml:
	$(MAKE) -f Makefile.dep $(ML4FILESML)

depend: beforedepend
# 1. We express dependencies of the .ml files w.r.t their grammars
	rm -f .depend.camlp4
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".ml: " >> .depend.camlp4; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend.camlp4; \
	done
# 2. Then we are able to produce the .ml files using Makefile.dep
	$(MAKE) -f Makefile.dep $(ML4FILESML)
# 3. We compute the dependencies inside the .ml files using ocamldep
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
# 4. We express dependencies of .cmo and .cmx files w.r.t their grammars
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".cmo: " >> .depend; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend; \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".cmx: " >> .depend; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend; \
	done
# 5. Finally, we erase the generated .ml files
	rm -f $(ML4FILESML)
# 6. Since .depend contains correct dependencies .depend.devel can be deleted
# (see dev/Makefile.dir for details about this file)
	if [ -e makefile ]; then >.depend.devel; else rm -f .depend.devel; fi

ml4clean::
	rm -f $(ML4FILESML)

clean::
	rm -f $(ML4FILESML)

include .depend
include .depend.coq


# this sets up developper supporting stuff
devel:	
	touch .depend.devel
	$(MAKE) -f dev/Makefile.devel setup-devel
	$(MAKE) dev/top_printers.cmo
