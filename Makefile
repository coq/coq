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
              -I proofs -I tactics -I pretyping \
              -I interp -I toplevel -I parsing -I ide/utils \
	      -I ide -I translate \
              -I contrib/omega -I contrib/romega \
	      -I contrib/ring -I contrib/xml \
	      -I contrib/extraction -I contrib/correctness \
              -I contrib/interface -I contrib/fourier \
	      -I contrib/jprover -I contrib/cc -I contrib/linear \
	      -I contrib/funind -I contrib/first-order

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
COQ_XML=	# is "-xml" when building XML library
COQOPTS=$(COQINCLUDES) $(GLOB) $(COQ_XML)

BOOTCOQTOP=$(BESTCOQTOP) -boot $(COQOPTS)

###########################################################################
# Objects files 
###########################################################################

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=\
  config/coq_config.cmo

LIBREP=\
  lib/pp_control.cmo lib/pp.cmo lib/util.cmo lib/bignat.cmo \
  lib/hashcons.cmo lib/dyn.cmo lib/system.cmo lib/options.cmo \
  lib/bstack.cmo lib/edit.cmo lib/gset.cmo lib/gmap.cmo \
  lib/tlm.cmo lib/gmapl.cmo lib/profile.cmo lib/explore.cmo \
  lib/predicate.cmo lib/rtree.cmo lib/heap.cmo
# Rem: Cygwin already uses variable LIB 

KERNEL=\
  kernel/names.cmo kernel/univ.cmo \
  kernel/esubst.cmo kernel/term.cmo kernel/sign.cmo \
  kernel/declarations.cmo kernel/environ.cmo kernel/closure.cmo \
  kernel/conv_oracle.cmo kernel/reduction.cmo kernel/entries.cmo \
  kernel/modops.cmo \
  kernel/type_errors.cmo kernel/inductive.cmo kernel/typeops.cmo \
  kernel/indtypes.cmo kernel/cooking.cmo kernel/term_typing.cmo \
  kernel/subtyping.cmo kernel/mod_typing.cmo kernel/safe_typing.cmo

LIBRARY=\
  library/nameops.cmo library/libnames.cmo library/libobject.cmo \
  library/summary.cmo \
  library/nametab.cmo library/global.cmo library/lib.cmo \
  library/declaremods.cmo library/library.cmo library/states.cmo \
  library/impargs.cmo library/decl_kinds.cmo \
  library/dischargedhypsmap.cmo library/declare.cmo library/goptions.cmo 

PRETYPING=\
  pretyping/termops.cmo pretyping/evd.cmo pretyping/instantiate.cmo \
  pretyping/reductionops.cmo pretyping/inductiveops.cmo \
  pretyping/rawterm.cmo pretyping/pattern.cmo \
  pretyping/detyping.cmo pretyping/retyping.cmo \
  pretyping/cbv.cmo pretyping/tacred.cmo \
  pretyping/pretype_errors.cmo pretyping/typing.cmo \
  pretyping/classops.cmo pretyping/recordops.cmo pretyping/indrec.cmo \
  pretyping/evarutil.cmo pretyping/evarconv.cmo \
  pretyping/coercion.cmo pretyping/cases.cmo pretyping/pretyping.cmo \
  pretyping/matching.cmo

INTERP=\
  interp/topconstr.cmo interp/ppextend.cmo interp/symbols.cmo \
  interp/genarg.cmo interp/syntax_def.cmo interp/reserve.cmo \
  interp/constrintern.cmo \
  interp/modintern.cmo interp/constrextern.cmo interp/coqlib.cmo

PARSING=\
  parsing/lexer.cmo parsing/coqast.cmo parsing/ast.cmo \
  parsing/termast.cmo parsing/extend.cmo parsing/esyntax.cmo \
  parsing/pcoq.cmo parsing/egrammar.cmo \
  parsing/ppconstr.cmo translate/ppconstrnew.cmo parsing/printer.cmo \
  parsing/pptactic.cmo translate/pptacticnew.cmo \
  parsing/printmod.cmo parsing/prettyp.cmo parsing/search.cmo

HIGHPARSING=\
  parsing/g_prim.cmo parsing/g_proofs.cmo parsing/g_basevernac.cmo \
  parsing/g_vernac.cmo parsing/g_tactic.cmo \
  parsing/g_ltac.cmo parsing/g_constr.cmo parsing/g_cases.cmo \
  parsing/g_module.cmo \
  parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo

HIGHPARSINGNEW=\
  parsing/g_primnew.cmo parsing/g_constrnew.cmo parsing/g_tacticnew.cmo \
  parsing/g_ltacnew.cmo parsing/g_vernacnew.cmo parsing/g_proofsnew.cmo \
  parsing/g_natsyntaxnew.cmo parsing/g_zsyntaxnew.cmo parsing/g_rsyntaxnew.cmo

ARITHSYNTAX=\
  parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo

PROOFS=\
  proofs/tacexpr.cmo proofs/proof_type.cmo \
  proofs/proof_trees.cmo proofs/logic.cmo \
  proofs/refiner.cmo proofs/evar_refiner.cmo proofs/tacmach.cmo \
  proofs/clenv.cmo proofs/pfedit.cmo proofs/tactic_debug.cmo

TACTICS=\
  tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
  tactics/nbtermdn.cmo tactics/wcclausenv.cmo \
  tactics/tacticals.cmo tactics/hipattern.cmo tactics/tactics.cmo \
  tactics/hiddentac.cmo tactics/elim.cmo \
  tactics/dhyp.cmo tactics/auto.cmo tactics/tacinterp.cmo

TOPLEVEL=\
  toplevel/himsg.cmo toplevel/cerrors.cmo toplevel/class.cmo \
  toplevel/vernacexpr.cmo  toplevel/metasyntax.cmo \
  toplevel/command.cmo toplevel/record.cmo toplevel/recordobj.cmo \
  toplevel/discharge.cmo translate/ppvernacnew.cmo \
  toplevel/vernacinterp.cmo toplevel/mltop.cmo \
  toplevel/vernacentries.cmo toplevel/vernac.cmo \
  toplevel/line_oriented_parser.cmo toplevel/protectedtoplevel.cmo \
  toplevel/toplevel.cmo toplevel/usage.cmo \
  toplevel/coqinit.cmo toplevel/coqtop.cmo

HIGHTACTICS=\
  tactics/setoid_replace.cmo tactics/equality.cmo \
  tactics/contradiction.cmo tactics/inv.cmo tactics/leminv.cmo \
  tactics/autorewrite.cmo tactics/refine.cmo \
  tactics/extraargs.cmo tactics/extratactics.cmo tactics/eauto.cmo

QUOTIFY=\
  parsing/qast.cmo parsing/q_prim.cmo parsing/q_tactic.cmo

parsing/q_prim.ml4: parsing/g_prim.ml4
	camlp4o -I parsing grammar.cma pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -o parsing/q_prim.ml4 -impl parsing/g_prim.ml4

parsing/q_tactic.ml4: parsing/g_tactic.ml4
	camlp4o -I parsing grammar.cma pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -o parsing/q_tactic.ml4 -impl parsing/g_tactic.ml4

parsing/q_ltac.ml4: parsing/g_ltac.ml4
	camlp4o -I parsing grammar.cma pa_ifdef.cmo pa_extend.cmo pr_o.cmo pr_extend.cmo -quotify -DQuotify -o parsing/q_ltac.ml4 -impl parsing/g_ltac.ml4

SPECTAC= tactics/tauto.ml4 tactics/newtauto.ml4 tactics/eqdecide.ml4
USERTAC = $(SPECTAC)
ML4FILES += $(USERTAC) tactics/extraargs.ml4 tactics/extratactics.ml4 \
	tactics/eauto.ml4 

USERTACCMO=$(USERTAC:.ml4=.cmo)
USERTACCMX=$(USERTAC:.ml4=.cmx)

INTERFACE=\
  contrib/interface/vtp.cmo contrib/interface/xlate.cmo \
  contrib/interface/paths.cmo contrib/interface/translate.cmo \
  contrib/interface/pbp.cmo \
  contrib/interface/dad.cmo \
  contrib/interface/history.cmo \
  contrib/interface/name_to_ast.cmo contrib/interface/debug_tac.cmo \
  contrib/interface/showproof_ct.cmo contrib/interface/showproof.cmo \
  contrib/interface/blast.cmo contrib/interface/centaur.cmo
INTERFACECMX=$(INTERFACE:.cmo=.cmx)

ML4FILES += contrib/interface/debug_tac.ml4 contrib/interface/centaur.ml4

PARSERREQUIRES=$(CMO) # Solution de facilité...
PARSERREQUIRESCMX=$(PARSERREQUIRES:.cmo=.cmx)

ML4FILES += contrib/correctness/psyntax.ml4 contrib/omega/g_omega.ml4 \
  contrib/romega/g_romega.ml4 contrib/ring/g_quote.ml4 \
  contrib/ring/g_ring.ml4 \
  contrib/field/field.ml4 contrib/fourier/g_fourier.ml4 \
  contrib/extraction/g_extraction.ml4 contrib/xml/xmlentries.ml4

OMEGACMO=\
  contrib/omega/omega.cmo contrib/omega/coq_omega.cmo \
  contrib/omega/g_omega.cmo 

ROMEGACMO=\
  contrib/romega/const_omega.cmo contrib/romega/refl_omega.cmo \
  contrib/romega/g_romega.cmo 

RINGCMO=\
  contrib/ring/quote.cmo contrib/ring/g_quote.cmo \
  contrib/ring/ring.cmo contrib/ring/g_ring.cmo 

FIELDCMO=\
  contrib/field/field.cmo 

XMLCMO=\
  contrib/xml/unshare.cmo contrib/xml/xml.cmo contrib/xml/acic.cmo \
  contrib/xml/doubleTypeInference.cmo \
  contrib/xml/cic2acic.cmo contrib/xml/acic2Xml.cmo \
  contrib/xml/proof2aproof.cmo contrib/xml/proofTree2Xml.cmo \
  contrib/xml/xmlcommand.cmo contrib/xml/xmlentries.cmo 	

FOURIERCMO=\
  contrib/fourier/fourier.cmo contrib/fourier/fourierR.cmo \
  contrib/fourier/g_fourier.cmo

EXTRACTIONCMO=\
  contrib/extraction/table.cmo\
  contrib/extraction/mlutil.cmo\
  contrib/extraction/modutil.cmo \
  contrib/extraction/ocaml.cmo \
  contrib/extraction/haskell.cmo \
  contrib/extraction/scheme.cmo \
  contrib/extraction/extraction.cmo \
  contrib/extraction/common.cmo \
  contrib/extraction/extract_env.cmo \
  contrib/extraction/g_extraction.cmo

CORRECTNESSCMO=\
  contrib/correctness/pmisc.cmo					  \
  contrib/correctness/peffect.cmo contrib/correctness/prename.cmo \
  contrib/correctness/perror.cmo contrib/correctness/penv.cmo  	  \
  contrib/correctness/putil.cmo contrib/correctness/pdb.cmo	  \
  contrib/correctness/pcic.cmo contrib/correctness/pmonad.cmo     \
  contrib/correctness/pcicenv.cmo  				  \
  contrib/correctness/pred.cmo contrib/correctness/ptyping.cmo	  \
  contrib/correctness/pwp.cmo contrib/correctness/pmlize.cmo	  \
  contrib/correctness/ptactic.cmo  contrib/correctness/psyntax.cmo

JPROVERCMO=\
  contrib/jprover/opname.cmo \
  contrib/jprover/jterm.cmo contrib/jprover/jlogic.cmo \
  contrib/jprover/jtunify.cmo contrib/jprover/jall.cmo \
  contrib/jprover/jprover.cmo

FUNINDCMO=\
  contrib/funind/tacinvutils.cmo contrib/funind/tacinv.cmo 

FOCMO=\
  contrib/first-order/formula.cmo contrib/first-order/sequent.cmo \
  contrib/first-order/unify.cmo contrib/first-order/rules.cmo \
  contrib/first-order/ground.cmo

CCCMO=contrib/cc/ccalgo.cmo contrib/cc/ccproof.cmo contrib/cc/cctac.cmo  

LINEARCMO=\
  contrib/linear/dpctypes.cmo \
  contrib/linear/general.cmo \
  contrib/linear/graph.cmo \
  contrib/linear/subst.cmo \
  contrib/linear/unif.cmo \
  contrib/linear/lk_proofs.cmo \
  contrib/linear/ccidpc.cmo \
  contrib/linear/kwc.cmo \
  contrib/linear/prove.cmo \
  contrib/linear/dpc.cmo

ML4FILES += contrib/jprover/jprover.ml4 contrib/cc/cctac.ml4 \
  contrib/linear/ccidpc.ml4 contrib/linear/dpc.ml4 contrib/funind/tacinv.ml4 \
  contrib/first-order/ground.ml4

CONTRIB=$(OMEGACMO) $(ROMEGACMO) $(RINGCMO) $(FIELDCMO) \
	$(FOURIERCMO) $(EXTRACTIONCMO) $(JPROVERCMO) $(XMLCMO) \
	$(CORRECTNESSCMO) $(CCCMO) $(LINEARCMO) $(FUNINDCMO) $(FOCMO)

CMA=$(CLIBS) $(CAMLP4OBJS)
CMXA=$(CMA:.cma=.cmxa)

CMO=$(CONFIG) $(LIBREP) $(KERNEL) $(LIBRARY) $(PRETYPING) \
    $(INTERP) $(PARSING) $(PROOFS) $(TACTICS) $(TOPLEVEL) \
    $(HIGHPARSING) $(HIGHTACTICS) $(CONTRIB)
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
COQINTERFACE=bin/coq-interface$(EXE) bin/coq-interface.opt$(EXE) bin/parser$(EXE)

COQBINARIES= $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(BESTCOQTOP) $(COQTOP) \
             $(COQINTERFACE) 

coqbinaries:: ${COQBINARIES}

world: coqbinaries states theories contrib tools coqide

coqlight: coqbinaries states theories-light tools

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
	echo "let proofs = \""$(PROOFS)"\"" >> $@
	echo "let tactics = \""$(TACTICS)"\"" >> $@
	echo "let interp = \""$(INTERP)"\"" >> $@
	echo "let parsing = \""$(PARSING)"\"" >> $@
	echo "let toplevel = \""$(TOPLEVEL)"\"" >> $@
	echo "let highparsing = \""$(HIGHPARSING)"\"" >> $@
	echo "let highparsingnew = \""$(HIGHPARSINGNEW)"\"" >> $@
	echo "let hightactics = \""$(HIGHTACTICS)" "$(USERTACCMO)"\"" >> $@
	echo "let contrib = \""$(CONTRIB)"\"" >> $@
	echo "let ide = \""$(COQIDECMO)"\"" >> $@

beforedepend:: scripts/tolink.ml

# Coq IDE

COQIDEBYTE=bin/coqide.byte$(EXE)
COQIDEOPT=bin/coqide.opt$(EXE)
COQIDE=bin/coqide$(EXE)

COQIDECMO=ide/utils/okey.cmo ide/utils/uoptions.cmo \
	  ide/utils/configwin_keys.cmo ide/utils/configwin_types.cmo \
	  ide/utils/configwin_messages.cmo ide/utils/configwin_ihm.cmo \
	  ide/utils/configwin.cmo \
	  ide/utils/editable_cells.cmo ide/config_parser.cmo \
	  ide/config_lexer.cmo ide/utf8_convert.cmo ide/preferences.cmo \
	  ide/ideutils.cmo ide/blaster_window.cmo ide/undo.cmo \
	  ide/find_phrase.cmo \
          ide/highlight.cmo ide/coq.cmo ide/coq_commands.cmo \
	  ide/coq_tactics.cmo  ide/command_windows.cmo ide/coqide.cmo

COQIDECMX=$(COQIDECMO:.cmo=.cmx)
COQIDEFLAGS=-thread -I +lablgtk2
beforedepend:: ide/config_lexer.ml ide/find_phrase.ml ide/highlight.ml
beforedepend:: ide/config_parser.mli ide/config_parser.ml
beforedepend:: ide/utf8_convert.ml

FULLIDELIB=$(FULLCOQLIB)/ide

COQIDEVO=ide/utf8.vo

$(COQIDEVO): states/initial.coq

IDEFILES=$(COQIDEVO) ide/coq.png ide/.coqide-gtk2rc ide/FAQ

coqide: $(IDEFILES) coqide-$(HASCOQIDE)
coqide-no:
coqide-byte: $(COQIDEBYTE) $(COQIDE)
coqide-opt:  $(COQIDEBYTE) $(COQIDEOPT) $(COQIDE)

ide: coqide-$(HASCOQIDE) states

clean-ide: 
	rm -f ide/utf8.vo $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi) $(COQIDEBYTE) $(COQIDEOPT)

$(COQIDEOPT): $(COQMKTOP) $(CMX) $(USERTACCMX) $(COQIDECMX)
	$(COQMKTOP) -ide -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQIDEBYTE): $(COQMKTOP) $(CMO) $(USERTACCMO) $(COQIDECMO)
	$(COQMKTOP) -g -ide -top $(LOCALINCLUDES) $(CAMLDEBUG) -o $@

$(COQIDE):
	cd bin; ln -sf coqide.$(HASCOQIDE)$(EXE) coqide$(EXE)

ide/%.cmo: ide/%.ml
	$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/%.cmi: ide/%.mli
	$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/%.cmx: ide/%.ml
	$(OCAMLOPT) $(COQIDEFLAGS) $(OPTFLAGS) -c $<

ide/utils/%.cmo: ide/%.ml
	$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/utils/%.cmi: ide/%.mli
	$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/utils/%.cmx: ide/%.ml
	$(OCAMLOPT) $(COQIDEFLAGS) $(OPTFLAGS) -c $<
clean::
	rm -f ide/extract_index.ml ide/find_phrase.ml ide/highlight.ml
	rm -f ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f $(COQIDEBYTE) $(COQIDEOPT)

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
interp: $(INTERP)
parsing: $(PARSING)
pretyping: $(PRETYPING)
highparsing: $(HIGHPARSING)
toplevel: $(TOPLEVEL)
hightactics: $(HIGHTACTICS)

# special binaries for debugging

bin/coq-interface$(EXE): $(COQMKTOP) $(CMO) $(USERTACCMO) $(INTERFACE)
	$(COQMKTOP) -top $(BYTEFLAGS) -o $@ $(INTERFACE)

bin/coq-interface.opt$(EXE): $(COQMKTOP) $(CMX) $(USERTACCMX) $(INTERFACECMX)
	$(COQMKTOP) -opt $(OPTFLAGS) -o $@ $(INTERFACECMX)

bin/parser$(EXE): contrib/interface/parse.cmx contrib/interface/line_parser.cmx $(PARSERREQUIRESCMX) contrib/interface/xlate.cmx contrib/interface/vtp.cmx
	$(OCAMLOPT) -cclib -lunix $(OPTFLAGS) -o $@ $(CMXA) \
	$(PARSERREQUIRESCMX) \
	line_parser.cmx vtp.cmx xlate.cmx parse.cmx

clean::
	rm -f bin/parser$(EXE) bin/coq-interface$(EXE) bin/coq-interface.opt$(EXE)

###########################################################################
# tests
###########################################################################

check:: world $(COQINTERFACE)
	cd test-suite; \
	env COQBIN=../bin COQLIB=.. ./check -$(BEST) | tee check.log
	if grep -F 'Error!' test-suite/check.log ; then false; fi

###########################################################################
# theories and states
###########################################################################

states:: states/barestate.coq states/initial.coq

SYNTAXPP=syntax/PPConstr.v syntax/PPCases.v

states/barestate.coq: $(SYNTAXPP) $(BESTCOQTOP)
	$(BESTCOQTOP) -boot -batch -silent -nois -I syntax -load-vernac-source syntax/MakeBare.v -outputstate $@

#       theories/Init/DatatypesHints.vo   theories/Init/PeanoHints.vo \
#       theories/Init/LogicHints.vo       theories/Init/SpecifHints.vo \
#       theories/Init/Logic_TypeHints.vo \

INITVO=theories/Init/Notations.vo \
       theories/Init/Datatypes.vo         theories/Init/DatatypesSyntax.vo \
       theories/Init/Peano.vo             theories/Init/PeanoSyntax.vo   \
       theories/Init/Logic.vo             theories/Init/Specif.vo        \
       theories/Init/LogicSyntax.vo       theories/Init/SpecifSyntax.vo  \
       theories/Init/Logic_Type.vo        theories/Init/Wf.vo            \
       theories/Init/Logic_TypeSyntax.vo  theories/Init/Prelude.vo


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
      theories/Logic/ClassicalFacts.vo       theories/Logic/ChoiceFacts.vo \
      theories/Logic/Berardi.vo       	     theories/Logic/Eqdep_dec.vo \
      theories/Logic/Decidable.vo            theories/Logic/JMeq.vo

ARITHVO=theories/Arith/Arith.vo         theories/Arith/Gt.vo          \
	theories/Arith/Between.vo       theories/Arith/Le.vo          \
	theories/Arith/Compare.vo       theories/Arith/Lt.vo          \
	theories/Arith/Compare_dec.vo   theories/Arith/Min.vo         \
	theories/Arith/Div2.vo          theories/Arith/Minus.vo       \
	theories/Arith/Mult.vo          theories/Arith/Even.vo        \
	theories/Arith/EqNat.vo         theories/Arith/Peano_dec.vo   \
	theories/Arith/Euclid.vo        theories/Arith/Plus.vo        \
	theories/Arith/Wf_nat.vo  	theories/Arith/Max.vo	      \
	theories/Arith/Bool_nat.vo	theories/Arith/Factorial.vo   \
#	theories/Arith/Div.vo 

SORTINGVO=theories/Sorting/Heap.vo \
	theories/Sorting/Permutation.vo \
	theories/Sorting/Sorting.vo
 
BOOLVO=theories/Bool/Bool.vo  		theories/Bool/IfProp.vo \
       theories/Bool/Zerob.vo 		theories/Bool/DecBool.vo \
	theories/Bool/Sumbool.vo 	theories/Bool/BoolEq.vo \
	theories/Bool/Bvector.vo

ZARITHVO=theories/ZArith/Wf_Z.vo        theories/ZArith/Zsyntax.vo \
	 theories/ZArith/ZArith.vo      theories/ZArith/auxiliary.vo \
	 theories/ZArith/ZArith_dec.vo  theories/ZArith/fast_integer.vo \
	 theories/ZArith/Zmisc.vo       theories/ZArith/zarith_aux.vo \
	 theories/ZArith/Zhints.vo	theories/ZArith/Zlogarithm.vo \
	 theories/ZArith/Zpower.vo 	theories/ZArith/Zcomplements.vo \
	 theories/ZArith/Zdiv.vo	theories/ZArith/Zsqrt.vo \
	 theories/ZArith/Zwf.vo		theories/ZArith/ZArith_base.vo \
	 theories/ZArith/Zbool.vo	theories/ZArith/Zbinary.vo

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

REALSBASEVO=theories/Reals/TypeSyntax.vo \
	theories/Reals/Rdefinitions.vo theories/Reals/Rsyntax.vo \
	theories/Reals/Raxioms.vo      theories/Reals/RIneq.vo \
	theories/Reals/DiscrR.vo       theories/Reals/Rbase.vo \

REALS_basic= 

REALS_all=theories/Reals/R_Ifp.vo \
	theories/Reals/Rbasic_fun.vo   theories/Reals/R_sqr.vo \
	theories/Reals/SplitAbsolu.vo  theories/Reals/SplitRmult.vo \
	theories/Reals/ArithProp.vo    theories/Reals/Rfunctions.vo \
	theories/Reals/Rseries.vo      theories/Reals/SeqProp.vo \
	theories/Reals/Rcomplete.vo     theories/Reals/PartSum.vo \
	theories/Reals/AltSeries.vo    theories/Reals/Binomial.vo \
	theories/Reals/Rsigma.vo       theories/Reals/Rprod.vo \
	theories/Reals/Cauchy_prod.vo  theories/Reals/Alembert.vo \
	theories/Reals/SeqSeries.vo    theories/Reals/Rtrigo_fun.vo \
	theories/Reals/Rtrigo_def.vo   theories/Reals/Rtrigo_alt.vo \
	theories/Reals/Cos_rel.vo      theories/Reals/Cos_plus.vo \
	theories/Reals/Rtrigo.vo       theories/Reals/Rlimit.vo \
	theories/Reals/Rderiv.vo       theories/Reals/RList.vo \
	theories/Reals/Ranalysis1.vo   theories/Reals/Ranalysis2.vo \
	theories/Reals/Ranalysis3.vo   theories/Reals/Rtopology.vo \
	theories/Reals/MVT.vo          theories/Reals/PSeries_reg.vo \
	theories/Reals/Exp_prop.vo     theories/Reals/Rtrigo_reg.vo \
	theories/Reals/Rsqrt_def.vo    theories/Reals/R_sqrt.vo \
	theories/Reals/Rtrigo_calc.vo  theories/Reals/Rgeom.vo \
	theories/Reals/Sqrt_reg.vo     theories/Reals/Ranalysis4.vo \
	theories/Reals/Rpower.vo       theories/Reals/Ranalysis.vo \
	theories/Reals/NewtonInt.vo    theories/Reals/RiemannInt_SF.vo \
	theories/Reals/RiemannInt.vo   theories/Reals/Integration.vo \
	theories/Reals/Reals.vo

REALSVO=$(REALSBASEVO) $(REALS_$(REALS))

ALLREALS=$(REALSBASEVO) $(REALS_all)

SETOIDSVO=theories/Setoids/Setoid.vo

THEORIESVO = $(LOGICVO) $(ARITHVO) $(BOOLVO) $(ZARITHVO) $(LISTSVO) \
             $(SETSVO) $(INTMAPVO) $(RELATIONSVO) $(WELLFOUNDEDVO) \
	     $(REALSVO) $(SETOIDSVO) $(SORTINGVO)

THEORIESLIGHTVO = $(LOGICVO) $(ARITHVO)

$(THEORIESVO): states/initial.coq
$(THEORIESLIGHTVO): states/initial.coq

theories: $(THEORIESVO)
theories-light: $(THEORIESLIGHTVO)

logic: $(LOGICVO)
arith: $(ARITHVO)
bool: $(BOOLVO)
zarith: $(ZARITHVO)
lists: $(LISTSVO)
sets: $(SETSVO)
intmap: $(INTMAPVO)
relations: $(RELATIONSVO)
wellfounded: $(WELLFOUNDEDVO)
# reals
reals: $(REALSVO)
allreals: $(ALLREALS)
install-allreals::
	for f in $(ALLREALS); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
setoids: $(SETOIDSVO)
sorting: $(SORTINGVO)

noreal: logic arith bool zarith lists sets intmap relations wellfounded \
	setoids sorting

# globalizations (for coqdoc)

glob.dump::
	rm -f glob.dump
	rm -f theories/*/*.vo
	$(MAKE) GLOB="-dump-glob glob.dump" world

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
	contrib/correctness/Sorted.vo	contrib/correctness/Tuples.vo
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

XMLVO = 

INTERFACEV0 = contrib/interface/Centaur.vo

INTERFACERC = contrib/interface/vernacrc

FOURIERVO = contrib/fourier/Fourier_util.vo    contrib/fourier/Fourier.vo

FUNINDVO = 

JPROVERVO = 

CCVO = contrib/cc/CC.vo

contrib/interface/Centaur.vo: contrib/interface/Centaur.v $(INTERFACE)
	$(BESTCOQTOP) -boot -byte  $(COQOPTS) -compile $*

contrib/interface/AddDad.vo: contrib/interface/AddDad.v $(INTERFACE) states/initial.coq
	$(BESTCOQTOP) -boot -byte  $(COQOPTS) -compile $*

CONTRIBVO = $(OMEGAVO) $(ROMEGAVO) $(RINGVO) $(FIELDVO) $(XMLVO) \
	    $(CORRECTNESSVO) $(FOURIERVO) \
	    $(JPROVERVO) $(INTERFACEV0) $(CCVO) $(FUNINDVO)

$(CONTRIBVO): states/initial.coq

contrib: $(CONTRIBVO) $(CONTRIBCMO) $(INTERFACERC)
omega: $(OMEGAVO) $(OMEGACMO) $(ROMEGAVO) $(ROMEGACMO)
ring: $(RINGVO) $(RINGCMO)
# xml_ instead of xml to avoid conflict with "make xml"
xml_: $(XMLVO) $(XMLCMO)
extraction: $(EXTRACTIONCMO) $(EXTRACTIONVO)
correctness: $(CORRECTNESSCMO) $(CORRECTNESSVO)
field: $(FIELDVO) $(FIELDCMO)
fourier: $(FOURIERVO) $(FOURIERCMO)
jprover: $(JPROVERVO) $(JPROVERCMO)
funind: $(FUNINDCMO) $(FUNINDVO)
cc: $(CCVO) $(CCCMO)

ALLVO = $(INITVO) $(THEORIESVO) $(CONTRIBVO) $(EXTRACTIONVO)

clean::
	rm -f contrib/*/*.cm[io] contrib/*/*.vo user-contrib/*.cm[io]

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

install-coqlight: install-$(BEST) install-binaries install-library-light

install-byte:
	$(MKDIR) $(FULLBINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqtop.byte$(EXE) coqtop$(EXE)

install-opt:
	$(MKDIR) $(FULLBINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(COQTOPOPT) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqtop.opt$(EXE) coqtop$(EXE)

install-binaries: install-ide-$(HASCOQIDE)
	$(MKDIR) $(FULLBINDIR)
	cp $(COQDEP) $(GALLINA) $(COQMAKEFILE) $(COQTEX) $(COQINTERFACE) $(COQVO2XML) $(FULLBINDIR)

install-ide-no:

install-ide-byte: 
	cp $(COQIDEBYTE) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqide.byte$(EXE) coqide$(EXE)

install-ide-opt:
	cp $(COQIDEBYTE) $(COQIDEOPT) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqide.opt$(EXE) coqide$(EXE)

LIBFILES=$(INITVO) $(TACTICSVO) $(THEORIESVO) $(CONTRIBVO)
LIBFILESLIGHT=$(INITVO) $(THEORIESLIGHTVO)

install-library:
	$(MKDIR) $(FULLCOQLIB)
	$(MKDIR) $(FULLCOQLIB)/tactics
	for f in $(LIBFILES); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states
	cp states/*.coq $(FULLCOQLIB)/states
	$(MKDIR) $(FULLEMACSLIB)
	cp tools/coq.el tools/coq-inferior.el $(FULLEMACSLIB)
	$(MKDIR) $(FULLIDELIB)
	cp $(IDEFILES) $(FULLIDELIB)

install-library-light:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(LIBFILESLIGHT); do \
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
LPINTERP = $(INTERP:.cmo=.mli)
LPPARSING = $(PARSING:.cmo=.mli) $(HIGHPARSING:.cmo=.mli)
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

# NB: the -maxdepth 3 is for excluding files from contrib/extraction/test

tags:
	find . -maxdepth 3 -regex ".*\.ml[i4]?" | sort -r | xargs \
	etags --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"

otags: 
	find . -maxdepth 3 -name "*.ml" -o -name "*.mli" \
	| sort -r | xargs otags
	find . -maxdepth 3 -name "*.ml4" | sort -r | xargs \
	etags --append --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
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

GRAMMARNEEDEDCMO=\
  lib/pp_control.cmo lib/pp.cmo lib/util.cmo lib/bignat.cmo \
  lib/dyn.cmo lib/options.cmo \
  lib/hashcons.cmo lib/predicate.cmo lib/rtree.cmo \
  kernel/names.cmo kernel/univ.cmo kernel/esubst.cmo kernel/term.cmo \
  kernel/sign.cmo kernel/declarations.cmo kernel/environ.cmo\
  library/nameops.cmo library/libnames.cmo library/summary.cmo \
  library/nametab.cmo library/libobject.cmo library/lib.cmo \
  library/goptions.cmo library/decl_kinds.cmo \
  pretyping/rawterm.cmo pretyping/pattern.cmo pretyping/evd.cmo \
  interp/topconstr.cmo interp/genarg.cmo \
  interp/ppextend.cmo parsing/coqast.cmo parsing/ast.cmo \
  proofs/tacexpr.cmo parsing/ast.cmo \
  parsing/lexer.cmo parsing/q_util.cmo parsing/extend.cmo \
  toplevel/vernacexpr.cmo parsing/pcoq.cmo parsing/q_coqast.cmo \
  parsing/egrammar.cmo 

CAMLP4EXTENSIONSCMO=\
  parsing/argextend.cmo parsing/tacextend.cmo parsing/vernacextend.cmo 

GRAMMARSCMO=\
  parsing/g_prim.cmo parsing/g_tactic.cmo \
  parsing/g_ltac.cmo parsing/g_constr.cmo

GRAMMARCMO=$(GRAMMARNEEDEDCMO) $(CAMLP4EXTENSIONSCMO) $(GRAMMARSCMO)

parsing/grammar.cma: $(GRAMMARCMO)
	$(OCAMLC) $(BYTEFLAGS) $(GRAMMARCMO) -linkall -a -o $@

clean::
	rm -f parsing/grammar.cma

ML4FILES +=parsing/g_basevernac.ml4 parsing/g_minicoq.ml4 \
	   parsing/g_vernac.ml4 parsing/g_proofs.ml4 \
	   parsing/g_cases.ml4 \
	   parsing/g_constr.ml4 parsing/g_module.ml4 \
	   parsing/g_tactic.ml4 parsing/g_ltac.ml4 \
	   parsing/argextend.ml4 parsing/tacextend.ml4 \
	   parsing/vernacextend.ml4 \
           parsing/g_primnew.ml4 \
           parsing/g_vernacnew.ml4 parsing/g_proofsnew.ml4 \
	   parsing/g_constrnew.ml4 \
	   parsing/g_tacticnew.ml4 parsing/g_ltacnew.ml4 \

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

proofs/tacexpr.cmo: proofs/tacexpr.ml
	$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

proofs/tacexpr.cmx: proofs/tacexpr.ml
	$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

# files compiled with camlp4 because of streams syntax

ML4FILES += lib/pp.ml4 			\
	 contrib/xml/xml.ml4		\
	 contrib/xml/acic2Xml.ml4	\
	 contrib/xml/proofTree2Xml.ml4	\
	 contrib/interface/line_parser.ml4	\
	 tools/coq_makefile.ml4		\
	 tools/coq-tex.ml4

# Add pr_o.cmo to circumvent a useless-warning bug when preprocessed with
# ast-based camlp4

parsing/lexer.cmx: parsing/lexer.ml4
	$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` pr_o.cmo -impl" -c -impl $<

parsing/lexer.cmo: parsing/lexer.ml4
	$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` pr_o.cmo -impl" -c -impl $<



###########################################################################
# Default rules
###########################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly .ml4 .v .vo .el .elc

.ml.cmo:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	ocamlyacc $<

.mly.mli:
	ocamlyacc $<

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
	rm -f interp/*.cmx interp/*.[so]
	rm -f parsing/*.cmx parsing/*.[so]
	rm -f pretyping/*.cmx pretyping/*.[so]
	rm -f toplevel/*.cmx toplevel/*.[so]
	rm -f ide/*.cmx ide/*.[so]
	rm -f ide/utils/*.cmx ide/utils/*.[so]
	rm -f translate/*.cmx translate/*.[so]
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
	rm -f interp/*.cm[io]
	rm -f parsing/*.cm[io] parsing/*.ppo
	rm -f pretyping/*.cm[io]
	rm -f toplevel/*.cm[io]
	rm -f ide/*.cm[io]
	rm -f ide/utils/*.cm[io]
	rm -f translate/*.cm[io]
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

dependcoq:: beforedepend
	$(COQDEP) -R theories Coq -R contrib Coq $(COQINCLUDES) $(ALLREALS:.vo=.v) $(ALLVO:.vo=.v) > .depend.coq

# Build dependencies ignoring failures in building ml files from ml4 files
# This is useful to rebuild dependencies when they are strongly corrupted:
# by making scratchdepend, one gets dependencies OK for .ml files and
# .ml4 files not using fancy parsers. This is sufficient to get beforedepend
# and depend targets successfully built
scratchdepend:: dependp4
	-$(MAKE) -k -f Makefile.dep $(ML4FILESML)
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
	$(MAKE) depend


# Computing the dependencies in camlp4 files is tricky.
# We proceed in several steps:

ML4FILESML = $(ML4FILES:.ml4=.ml)

# Expresses dependencies of the .ml4 files w.r.t their grammars
dependp4::
	rm -f .depend.camlp4
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".ml: " >> .depend.camlp4; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend.camlp4; \
	done

# Produce the .ml files using Makefile.dep
ml4filesml:: .depend.camlp4
	$(MAKE) -f Makefile.dep $(ML4FILESML)

depend: beforedepend dependp4 ml4filesml
# 1. We express dependencies of the .ml files w.r.t their grammars
# 2. Then we are able to produce the .ml files using Makefile.dep
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


############################################################################
# Entries for new syntax
############################################################################

# 1. Translate the old syntax files and build new syntax theories hierarchy
translation::
	@$(MAKE) COQ_XML=-ftranslate world
	@$(MAKE) movenew

translation2::
	@$(MAKE) COQ_XML=-ftranslate2 world
	@$(MAKE) movenew

movenew::
	-mv *.v8 theories/Init/
	for i in theories/*/*.v8 contrib/*/*.v8; do \
	  if expr $$i : '.*/\*\.v8' > /dev/null ; then continue ; fi ; \
	  j=new`dirname $$i`/`basename $$i .v8`.v ; \
	  mkdir -p `dirname $$j` ; \
	  mv -u -f $$i $$j ; \
	done

# 2. Build new syntax images and compile theories
newworld:: $(COQTOPNEW) newinit newtheories newcontrib

newinit:: $(INITVO:%.vo=new%.vo)
newtheories:: $(THEORIESVO:%.vo=new%.vo)
newcontrib:: $(CONTRIBVO:%.vo=new%.vo) $(CONTRIBCMO)


COQTOPNEW=bin/coqtopnew.$(BEST)$(EXE)

NEWCMX=$(HIGHPARSINGNEW:.cmo=.cmx)
NEWOPTS=-boot $(GLOB) -v8 -R newtheories Coq -R newcontrib Coq
NEWCOQBARE=$(COQTOPNEW) $(NEWOPTS) -nois
NEWCOQ=$(COQTOPNEW) $(NEWOPTS) -is states/initialnew.coq

bin/coqtopnew.opt$(EXE): $(COQMKTOP) $(CMX) $(USERTACCMX) $(NEWCMX)
	$(COQMKTOP) -opt $(OPTFLAGS) $(NEWCMX) -o $@

bin/coqtopnew.byte$(EXE): $(COQMKTOP) $(CMO) $(USERTACCMO) $(HIGHPARSINGNEW)
	$(COQMKTOP) -top $(OPTFLAGS) $(HIGHPARSINGNEW) -o $@

newtheories/Init/%.vo: $(COQTOPNEW) newtheories/Init/%.v
	$(NEWCOQBARE) -compile $*

states/initialnew.coq: states/MakeInitialNew.v $(INITVO:%.vo=new%.vo)
	$(NEWCOQBARE) -batch -silent -load-vernac-source states/MakeInitialNew.v -outputstate states/initialnew.coq

newcontrib/%.vo: newcontrib/%.v states/initialnew.coq
	$(NEWCOQ) -compile $*
newtheories/%.vo: newtheories/%.v states/initialnew.coq
	$(NEWCOQ) -compile $*

# Dependencies
.depend.newcoq: .depend.coq Makefile
	sed -e "s|theories/\([^ ]*\.v\)|newtheories/\1|g" -e "s|contrib/\([^ ]*\.v\)|newcontrib/\1|g" .depend.coq > .depend.newcoq

include .depend.newcoq

clean::
	rm -f bin/coqtopnew.byte$(EXE) bin/coqtopnew.opt$(EXE)
	rm -fr *.v8 newtheories newcontrib
