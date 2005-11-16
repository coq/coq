########################################################################
#  v      #   The Coq Proof Assistant  /  The Coq Development Team     #
# <O___,, # CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud #
#   \VV/  ##############################################################
#    //   #      This file is distributed under the terms of the       #
#         #       GNU Lesser General Public License Version 2.1        #
########################################################################

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
	@echo
	@echo "For make to be verbose, add VERBOSE=1"

# build and install the three subsystems: coq, coqide, pcoq
world: coq coqide pcoq
world8: coq8 coqide pcoq
world7: coq7 coqide pcoq

install: install-coq install-coqide install-pcoq
install8: install-coq8 install-coqide install-pcoq
install7: install-coq7 install-coqide install-pcoq
#install-manpages: install-coq-manpages install-pcoq-manpages

###########################################################################
# Compilation options
###########################################################################

# The SHOW and HIDE variables control whether make will echo complete commands 
# or only abbreviated versions. 
# Quiet mode is ON by default except if VERBOSE=1 option is given to make

ifeq ($(VERBOSE),1)
 SHOW = @true ""
 HIDE = 
else 
 SHOW = @echo ""
 HIDE = @
endif

LOCALINCLUDES=-I config -I tools -I tools/coqdoc \
	      -I scripts -I lib -I kernel -I library \
              -I proofs -I tactics -I pretyping \
              -I interp -I toplevel -I parsing -I ide/utils \
	      -I ide -I translate \
              -I contrib/omega -I contrib/romega \
	      -I contrib/ring -I contrib/xml \
	      -I contrib/extraction \
              -I contrib/interface -I contrib/fourier \
	      -I contrib/jprover -I contrib/cc \
	      -I contrib/funind -I contrib/first-order \
              -I contrib/field

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
GLOB=           # is "-dump-glob file" when making the doc
COQ_XML=	# is "-xml" when building XML library
COQOPTS=$(GLOB) $(COQ_XML)
TRANSLATE=-translate -strict-implicit

BOOTCOQTOP=$(BESTCOQTOP) -boot $(COQOPTS)

###########################################################################
# Objects files 
###########################################################################

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=\
  config/coq_config.cmo

LIBREP=\
  lib/pp_control.cmo lib/pp.cmo lib/compat.cmo lib/util.cmo lib/bignat.cmo \
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
  library/summary.cmo library/nametab.cmo library/global.cmo library/lib.cmo \
  library/declaremods.cmo library/library.cmo library/states.cmo \
  library/decl_kinds.cmo library/dischargedhypsmap.cmo library/goptions.cmo 

PRETYPING=\
  pretyping/termops.cmo pretyping/evd.cmo pretyping/instantiate.cmo \
  pretyping/reductionops.cmo pretyping/inductiveops.cmo \
  pretyping/rawterm.cmo pretyping/pattern.cmo \
  pretyping/detyping.cmo pretyping/retyping.cmo \
  pretyping/cbv.cmo pretyping/pretype_errors.cmo pretyping/typing.cmo \
  pretyping/tacred.cmo \
  pretyping/classops.cmo pretyping/recordops.cmo pretyping/indrec.cmo \
  pretyping/evarutil.cmo pretyping/evarconv.cmo \
  pretyping/coercion.cmo pretyping/cases.cmo pretyping/pretyping.cmo \
  pretyping/matching.cmo

INTERP=\
  parsing/lexer.cmo interp/topconstr.cmo interp/ppextend.cmo interp/symbols.cmo \
  interp/genarg.cmo interp/syntax_def.cmo interp/reserve.cmo \
  library/impargs.cmo interp/constrintern.cmo \
  interp/modintern.cmo interp/constrextern.cmo interp/coqlib.cmo \
  library/declare.cmo

PARSING=\
  parsing/coqast.cmo parsing/ast.cmo \
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
  parsing/g_ltacnew.cmo parsing/g_vernacnew.cmo parsing/g_proofsnew.cmo

ARITHSYNTAX=\
  parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo

PROOFS=\
  proofs/tacexpr.cmo proofs/proof_type.cmo \
  proofs/proof_trees.cmo proofs/logic.cmo \
  proofs/refiner.cmo proofs/evar_refiner.cmo proofs/tacmach.cmo \
  proofs/clenv.cmo proofs/pfedit.cmo proofs/tactic_debug.cmo

TACTICS=\
  tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
  tactics/nbtermdn.cmo tactics/tacticals.cmo \
  tactics/hipattern.cmo tactics/tactics.cmo \
  tactics/hiddentac.cmo tactics/elim.cmo \
  tactics/dhyp.cmo tactics/auto.cmo \
  tactics/setoid_replace.cmo tactics/equality.cmo \
  tactics/contradiction.cmo tactics/inv.cmo tactics/leminv.cmo \
  tactics/tacinterp.cmo \

TOPLEVEL=\
  toplevel/himsg.cmo toplevel/cerrors.cmo toplevel/class.cmo \
  toplevel/vernacexpr.cmo  toplevel/metasyntax.cmo \
  toplevel/command.cmo \
  toplevel/record.cmo toplevel/recordobj.cmo \
  toplevel/discharge.cmo translate/ppvernacnew.cmo \
  toplevel/vernacinterp.cmo toplevel/mltop.cmo \
  toplevel/vernacentries.cmo toplevel/vernac.cmo \
  toplevel/line_oriented_parser.cmo toplevel/protectedtoplevel.cmo \
  toplevel/toplevel.cmo toplevel/usage.cmo \
  toplevel/coqinit.cmo toplevel/coqtop.cmo

HIGHTACTICS=\
  tactics/autorewrite.cmo tactics/refine.cmo \
  tactics/extraargs.cmo tactics/extratactics.cmo tactics/eauto.cmo

SPECTAC= tactics/tauto.ml4 tactics/eqdecide.ml4
USERTAC = $(SPECTAC)
ML4FILES += $(USERTAC) tactics/extraargs.ml4 tactics/extratactics.ml4 \
	tactics/eauto.ml4 

USERTACCMO=$(USERTAC:.ml4=.cmo)
USERTACCMX=$(USERTAC:.ml4=.cmx)

ML4FILES +=\
  contrib/omega/g_omega.ml4 \
  contrib/romega/g_romega.ml4 contrib/ring/g_quote.ml4 \
  contrib/ring/g_ring.ml4 \
  contrib/field/field.ml4 contrib/fourier/g_fourier.ml4 \
  contrib/extraction/g_extraction.ml4 contrib/xml/xmlentries.ml4

OMEGACMO=\
  contrib/omega/omega.cmo contrib/omega/coq_omega.cmo \
  contrib/omega/g_omega.cmo 

ROMEGACMO=\
  contrib/romega/omega2.cmo contrib/romega/const_omega.cmo \
  contrib/romega/refl_omega.cmo contrib/romega/g_romega.cmo

RINGCMO=\
  contrib/ring/quote.cmo contrib/ring/g_quote.cmo \
  contrib/ring/ring.cmo contrib/ring/g_ring.cmo 

FIELDCMO=\
  contrib/field/field.cmo 

XMLCMO=\
  contrib/xml/unshare.cmo contrib/xml/xml.cmo contrib/xml/acic.cmo \
  contrib/xml/doubleTypeInference.cmo \
  contrib/xml/cic2acic.cmo contrib/xml/acic2Xml.cmo \
  contrib/xml/proof2aproof.cmo \
  contrib/xml/xmlcommand.cmo contrib/xml/proofTree2Xml.cmo \
	contrib/xml/xmlentries.cmo 	

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

JPROVERCMO=\
  contrib/jprover/opname.cmo \
  contrib/jprover/jterm.cmo contrib/jprover/jlogic.cmo \
  contrib/jprover/jtunify.cmo contrib/jprover/jall.cmo \
  contrib/jprover/jprover.cmo

FUNINDCMO=\
  contrib/funind/tacinvutils.cmo contrib/funind/tacinv.cmo 

FOCMO=\
  contrib/first-order/formula.cmo contrib/first-order/unify.cmo \
  contrib/first-order/sequent.cmo contrib/first-order/rules.cmo \
  contrib/first-order/instances.cmo contrib/first-order/ground.cmo \
  contrib/first-order/g_ground.cmo

CCCMO=contrib/cc/ccalgo.cmo contrib/cc/ccproof.cmo contrib/cc/cctac.cmo  

ML4FILES += contrib/jprover/jprover.ml4 contrib/cc/cctac.ml4 \
  contrib/funind/tacinv.ml4 contrib/first-order/g_ground.ml4

CONTRIB=$(OMEGACMO) $(ROMEGACMO) $(RINGCMO) $(FIELDCMO) \
	$(FOURIERCMO) $(EXTRACTIONCMO) $(JPROVERCMO) $(XMLCMO) \
	$(CCCMO) $(FUNINDCMO) $(FOCMO)

CMA=$(CLIBS) $(CAMLP4OBJS)
CMXA=$(CMA:.cma=.cmxa)

# Beware that highparsingnew.cma should appear before hightactics.cma
# respecting this order is useful for developers that want to load or link
# the libraries directly
CMO=$(CONFIG) lib/lib.cma kernel/kernel.cma library/library.cma \
    pretyping/pretyping.cma interp/interp.cma parsing/parsing.cma \
    proofs/proofs.cma tactics/tactics.cma toplevel/toplevel.cma \
    parsing/highparsing.cma parsing/highparsingnew.cma tactics/hightactics.cma \
    contrib/contrib.cma
CMOCMXA=$(CMO:.cma=.cmxa)
CMX=$(CMOCMXA:.cmo=.cmx)

###########################################################################
# Main targets (coqmktop, coqtop.opt, coqtop.byte)
###########################################################################

COQMKTOP=bin/coqmktop$(EXE) 
COQC=bin/coqc$(EXE)
COQTOPBYTE=bin/coqtop.byte$(EXE)
COQTOPOPT=bin/coqtop.opt$(EXE)
BESTCOQTOP=bin/coqtop.$(BEST)$(EXE)
COQTOP=bin/coqtop$(EXE)

COQBINARIES= $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(BESTCOQTOP) $(COQTOP)

coqbinaries:: ${COQBINARIES}

coq: coqlib tools coqbinaries coqlib7
coq8: coqlib tools coqbinaries
coq7: coqlib7 tools coqbinaries

coqlib:: newtheories newcontrib

coqlib7: theories7 contrib7

coqlight: theories-light tools coqbinaries

states7:: states7/initial.coq

states:: states/initial.coq

$(COQTOPOPT): $(COQMKTOP) $(CMX) $(USERTACCMX)
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQTOPBYTE): $(COQMKTOP) $(CMO) $(USERTACCMO)
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -top $(BYTEFLAGS) -o $@

$(COQTOP):
	cd bin; ln -sf coqtop.$(BEST)$(EXE) coqtop$(EXE)

# coqmktop 

COQMKTOPCMO=$(CONFIG) scripts/tolink.cmo scripts/coqmktop.cmo 

$(COQMKTOP): $(COQMKTOPCMO)
	$(SHOW)'OCAMLC -o $@'	
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -o $@ -custom str.cma unix.cma \
          $(COQMKTOPCMO) $(OSDEPLIBS)

scripts/tolink.ml: Makefile
	$(SHOW)"ECHO... >" $@
	$(HIDE)echo "let lib = \""$(LIBREP)"\"" > $@
	$(HIDE)echo "let kernel = \""$(KERNEL)"\"" >> $@
	$(HIDE)echo "let library = \""$(LIBRARY)"\"" >> $@
	$(HIDE)echo "let pretyping = \""$(PRETYPING)"\"" >> $@
	$(HIDE)echo "let proofs = \""$(PROOFS)"\"" >> $@
	$(HIDE)echo "let tactics = \""$(TACTICS)"\"" >> $@
	$(HIDE)echo "let interp = \""$(INTERP)"\"" >> $@
	$(HIDE)echo "let parsing = \""$(PARSING)"\"" >> $@
	$(HIDE)echo "let toplevel = \""$(TOPLEVEL)"\"" >> $@
	$(HIDE)echo "let highparsing = \""$(HIGHPARSING)"\"" >> $@
	$(HIDE)echo "let highparsingnew = \""$(HIGHPARSINGNEW)"\"" >> $@
	$(HIDE)echo "let hightactics = \""$(HIGHTACTICS)" "$(USERTACCMO)"\"" >> $@
	$(HIDE)echo "let contrib = \""$(CONTRIB)"\"" >> $@
	$(HIDE)echo "let ide = \""$(COQIDECMO)"\"" >> $@

beforedepend:: scripts/tolink.ml

# coqc

COQCCMO=$(CONFIG) toplevel/usage.cmo scripts/coqc.cmo

$(COQC): $(COQCCMO) $(COQTOPBYTE) $(BESTCOQTOP)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -o $@ -custom unix.cma $(COQCCMO) $(OSDEPLIBS)

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
highparsingnew: $(HIGHPARSINGNEW)
toplevel: $(TOPLEVEL)
hightactics: $(HIGHTACTICS)

# target for libraries

lib/lib.cma: $(LIBREP)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(LIBREP)

lib/lib.cmxa: $(LIBREP:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(LIBREP:.cmo=.cmx)

kernel/kernel.cma: $(KERNEL)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(KERNEL)

kernel/kernel.cmxa: $(KERNEL:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(KERNEL:.cmo=.cmx)

library/library.cma: $(LIBRARY)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(LIBRARY)

library/library.cmxa: $(LIBRARY:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(LIBRARY:.cmo=.cmx)

pretyping/pretyping.cma: $(PRETYPING)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(PRETYPING)

pretyping/pretyping.cmxa: $(PRETYPING:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(PRETYPING:.cmo=.cmx)

interp/interp.cma: $(INTERP)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(INTERP)

interp/interp.cmxa: $(INTERP:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(INTERP:.cmo=.cmx)

parsing/parsing.cma: $(PARSING)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(PARSING)

parsing/parsing.cmxa: $(PARSING:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(PARSING:.cmo=.cmx)

proofs/proofs.cma: $(PROOFS)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(PROOFS)

proofs/proofs.cmxa: $(PROOFS:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(PROOFS:.cmo=.cmx)

tactics/tactics.cma: $(TACTICS)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(TACTICS)

tactics/tactics.cmxa: $(TACTICS:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(TACTICS:.cmo=.cmx)

toplevel/toplevel.cma: $(TOPLEVEL)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(TOPLEVEL)

toplevel/toplevel.cmxa: $(TOPLEVEL:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(TOPLEVEL:.cmo=.cmx)

parsing/highparsing.cma: $(HIGHPARSING)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(HIGHPARSING)

parsing/highparsing.cmxa: $(HIGHPARSING:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(HIGHPARSING:.cmo=.cmx)

tactics/hightactics.cma: $(HIGHTACTICS) $(USERTACCMO)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(HIGHTACTICS) $(USERTACCMO)

tactics/hightactics.cmxa: $(HIGHTACTICS:.cmo=.cmx) $(USERTACCMO:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(HIGHTACTICS:.cmo=.cmx) \
		$(USERTACCMO:.cmo=.cmx)

contrib/contrib.cma: $(CONTRIB)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(CONTRIB)

contrib/contrib.cmxa: $(CONTRIB:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(CONTRIB:.cmo=.cmx)

parsing/highparsingnew.cma: $(HIGHPARSINGNEW)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(HIGHPARSINGNEW)

parsing/highparsingnew.cmxa: $(HIGHPARSINGNEW:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(HIGHPARSINGNEW:.cmo=.cmx)

###########################################################################
# CoqIde special targets
###########################################################################

# target to build CoqIde
coqide:: coqide-files coqide-binaries states

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

COQIDEVO=ide/utf8.vo

$(COQIDEVO): states/initial.coq 
	$(BOOTCOQTOP) -compile $*

IDEFILES=$(COQIDEVO) ide/utf8.v ide/coq.png ide/.coqide-gtk2rc

coqide-binaries: coqide-$(HASCOQIDE)
coqide-no:
coqide-byte: $(COQIDEBYTE) $(COQIDE)
coqide-opt:  $(COQIDEBYTE) $(COQIDEOPT) $(COQIDE)
coqide-files: $(IDEFILES)

clean-ide: 
	rm -f $(COQIDEVO) $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi) $(COQIDEBYTE) $(COQIDEOPT) $(COQIDE) 
	rm -f ide/extract_index.ml ide/find_phrase.ml ide/highlight.ml
	rm -f ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f ide/utf8_convert.ml

$(COQIDEOPT): $(COQMKTOP) $(CMX) $(USERTACCMX) ide/ide.cmxa
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -ide -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQIDEBYTE): $(COQMKTOP) $(CMO) $(USERTACCMO) ide/ide.cma
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -ide -top $(BYTEFLAGS) -o $@

$(COQIDE):
	cd bin; ln -sf coqide.$(HASCOQIDE)$(EXE) coqide$(EXE)

ide/%.cmo: ide/%.ml
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/%.cmi: ide/%.mli
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/%.cmx: ide/%.ml
	$(SHOW)'OCAMLOPT  $<'	
	$(HIDE)$(OCAMLOPT) $(COQIDEFLAGS) $(OPTFLAGS) -c $<

ide/utils/%.cmo: ide/utils/%.ml
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/utils/%.cmi: ide/utils/%.mli
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/utils/%.cmx: ide/utils/%.ml
	$(SHOW)'OCAMLOPT  $<'	
	$(HIDE)$(OCAMLOPT) $(COQIDEFLAGS) $(OPTFLAGS) -c $<

# Special target to select between whether lablgtk >= 2.6.0 or not
ide/undo.cmi: ide/undo.mli
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(COQIDEFLAGS) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) $(CAMLP4COMPAT) -intf" -c -intf $<

clean::
	rm -f ide/extract_index.ml ide/find_phrase.ml ide/highlight.ml
	rm -f ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f ide/utf8_convert.ml
	rm -f $(COQIDEVO) $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi)
	rm -f $(COQIDEBYTE) $(COQIDEOPT) $(COQIDE)

ide/ide.cma: $(COQIDECMO)
	$(SHOW)'OCAMLC -a -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -a -o $@ $(COQIDECMO)

ide/ide.cmxa: $(COQIDECMO:.cmo=.cmx)
	$(SHOW)'OCAMLOPT -a -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -a -o $@ $(COQIDECMO:.cmo=.cmx)

# install targets

FULLIDELIB=$(FULLCOQLIB)/ide

install-coqide:: install-ide-$(HASCOQIDE) install-ide-files install-ide-info

install-ide-no:

install-ide-byte: 
	$(MKDIR) $(FULLBINDIR)
	cp $(COQIDEBYTE) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqide.byte$(EXE) coqide$(EXE)

install-ide-opt:
	$(MKDIR) $(FULLBINDIR)
	cp $(COQIDEBYTE) $(COQIDEOPT) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqide.opt$(EXE) coqide$(EXE)

install-ide-files:
	$(MKDIR) $(FULLIDELIB)
	cp $(IDEFILES) $(FULLIDELIB)

install-ide-info:
	$(MKDIR) $(FULLIDELIB)
	cp ide/FAQ $(FULLIDELIB)

###########################################################################
# Pcoq: special binaries for debugging (coq-interface, parser)
###########################################################################

# target to build Pcoq
pcoq: pcoq-binaries pcoq-files

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
PARSERREQUIRESCMX=$(CMX)

ifeq ($(BEST),opt)
  COQINTERFACE=bin/coq-interface$(EXE) bin/coq-interface.opt$(EXE) bin/parser$(EXE) bin/parser.opt$(EXE)
else
  COQINTERFACE=bin/coq-interface$(EXE) bin/parser$(EXE)
endif

pcoq-binaries:: $(COQINTERFACE) 

bin/coq-interface$(EXE): $(COQMKTOP) $(CMO) $(USERTACCMO) $(INTERFACE)
	$(SHOW)'COQMKTOP -o $@'
	$(HIDE)$(COQMKTOP) -top $(BYTEFLAGS) -o $@ $(INTERFACE)

bin/coq-interface.opt$(EXE): $(COQMKTOP) $(CMX) $(USERTACCMX) $(INTERFACECMX)
	$(SHOW)'COQMKTOP -o $@'
	$(HIDE)$(COQMKTOP) -opt $(OPTFLAGS) -o $@ $(INTERFACECMX)

PARSERCODE=contrib/interface/line_parser.cmo contrib/interface/vtp.cmo \
           contrib/interface/xlate.cmo contrib/interface/parse.cmo
PARSERCMO=$(PARSERREQUIRES) $(PARSERCODE)
PARSERCMX= $(PARSERREQUIRESCMX) $(PARSERCODE:.cmo=.cmx)

bin/parser$(EXE): $(PARSERCMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) -linkall -custom -cclib -lunix $(OPTFLAGS) -o $@ \
	  dynlink.cma $(CMA) $(PARSERCMO)

bin/parser.opt$(EXE): $(PARSERCMX)
	$(SHOW)'OCAMLOPT -o $@'
	$(HIDE)$(OCAMLOPT) -linkall -cclib -lunix $(OPTFLAGS) -o $@ \
	  $(CMXA) $(PARSERCMX)

INTERFACEVO=

INTERFACERC= contrib/interface/vernacrc

pcoq-files:: $(INTERFACEVO) $(INTERFACERC)

# Centaur grammar rules now in centaur.ml4
contrib7/interface/Centaur.vo: contrib7/interface/Centaur.v $(INTERFACE)
	$(BESTCOQTOP) $(TRANSLATE) -boot -byte $(COQOPTS) -compile $*

# Move the grammar rules to dad.ml ?
contrib7/interface/AddDad.vo: contrib7/interface/AddDad.v $(INTERFACE) states7/initial.coq
	$(BESTCOQTOP) $(TRANSLATE) -boot -byte  $(COQOPTS) -compile $*

clean::
	rm -f bin/parser$(EXE) bin/coq-interface$(EXE) bin/coq-interface.opt$(EXE)

# install targets
install-pcoq:: install-pcoq-binaries install-pcoq-files install-pcoq-manpages

install-pcoq-binaries::
	$(MKDIR) $(FULLBINDIR)
	cp $(COQINTERFACE) $(FULLBINDIR)

install-pcoq-files::
	$(MKDIR) $(FULLCOQLIB)/contrib/interface
	cp $(INTERFACERC) $(FULLCOQLIB)/contrib/interface

PCOQMANPAGES=man/coq-interface.1 man/parser.1

install-pcoq-manpages:
	$(MKDIR) $(FULLMANDIR)/man1
	cp $(PCOQMANPAGES) $(FULLMANDIR)/man1

###########################################################################
# tests
###########################################################################

check:: world pcoq
	cd test-suite; \
	env COQBIN=../bin COQLIB=.. ./check -$(BEST) | tee check.log
	if grep -F 'Error!' test-suite/check.log ; then false; fi

###########################################################################
# theories and contrib files
###########################################################################

INITVO=\
 theories/Init/Notations.vo \
 theories/Init/Datatypes.vo         theories/Init/Peano.vo     \
 theories/Init/Logic.vo             theories/Init/Specif.vo    \
 theories/Init/Logic_Type.vo        theories/Init/Wf.vo      \
 theories/Init/Prelude.vo

init: $(INITVO)

LOGICVO=\
 theories/Logic/Hurkens.vo          	theories/Logic/ProofIrrelevance.vo\
 theories/Logic/Classical.vo          	theories/Logic/Classical_Type.vo \
 theories/Logic/Classical_Pred_Set.vo   theories/Logic/Eqdep.vo          \
 theories/Logic/Classical_Pred_Type.vo  theories/Logic/Classical_Prop.vo \
 theories/Logic/ClassicalFacts.vo       theories/Logic/ChoiceFacts.vo \
 theories/Logic/Berardi.vo       	theories/Logic/Eqdep_dec.vo \
 theories/Logic/Decidable.vo            theories/Logic/JMeq.vo \
 theories/Logic/ClassicalDescription.vo theories/Logic/ClassicalChoice.vo \
 theories/Logic/RelationalChoice.vo     theories/Logic/Diaconescu.vo

ARITHVO=\
 theories/Arith/Arith.vo        theories/Arith/Gt.vo          \
 theories/Arith/Between.vo      theories/Arith/Le.vo          \
 theories/Arith/Compare.vo      theories/Arith/Lt.vo          \
 theories/Arith/Compare_dec.vo  theories/Arith/Min.vo         \
 theories/Arith/Div2.vo         theories/Arith/Minus.vo       \
 theories/Arith/Mult.vo         theories/Arith/Even.vo        \
 theories/Arith/EqNat.vo        theories/Arith/Peano_dec.vo   \
 theories/Arith/Euclid.vo       theories/Arith/Plus.vo        \
 theories/Arith/Wf_nat.vo  	theories/Arith/Max.vo	      \
 theories/Arith/Bool_nat.vo	theories/Arith/Factorial.vo   \
# theories/Arith/Div.vo 

SORTINGVO=\
 theories/Sorting/Heap.vo	theories/Sorting/Permutation.vo \
 theories/Sorting/Sorting.vo
 
BOOLVO=\
 theories/Bool/Bool.vo  	theories/Bool/IfProp.vo \
 theories/Bool/Zerob.vo 	theories/Bool/DecBool.vo \
 theories/Bool/Sumbool.vo 	theories/Bool/BoolEq.vo \
 theories/Bool/Bvector.vo

NARITHVO=\
 theories/NArith/BinPos.vo	theories/NArith/Pnat.vo \
 theories/NArith/BinNat.vo	theories/NArith/NArith.vo

ZARITHVO=\
 theories/ZArith/BinInt.vo      theories/ZArith/Wf_Z.vo \
 theories/ZArith/ZArith.vo      theories/ZArith/ZArith_dec.vo \
 theories/ZArith/auxiliary.vo   theories/ZArith/Zmisc.vo \
 theories/ZArith/Zcompare.vo    theories/ZArith/Znat.vo \
 theories/ZArith/Zorder.vo      theories/ZArith/Zabs.vo \
 theories/ZArith/Zmin.vo        theories/ZArith/Zeven.vo \
 theories/ZArith/Zhints.vo	theories/ZArith/Zlogarithm.vo \
 theories/ZArith/Zpower.vo 	theories/ZArith/Zcomplements.vo \
 theories/ZArith/Zdiv.vo	theories/ZArith/Zsqrt.vo \
 theories/ZArith/Zwf.vo		theories/ZArith/ZArith_base.vo \
 theories/ZArith/Zbool.vo	theories/ZArith/Zbinary.vo \
 theories/ZArith/Znumtheory.vo

LISTSVO=\
 theories/Lists/MonoList.vo \
 theories/Lists/ListSet.vo   	theories/Lists/Streams.vo \
 theories/Lists/TheoryList.vo   theories/Lists/List.vo

SETSVO=\
 theories/Sets/Classical_sets.vo    theories/Sets/Permut.vo \
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

INTMAPVO=\
 theories/IntMap/Adalloc.vo    theories/IntMap/Mapcanon.vo \
 theories/IntMap/Addec.vo      theories/IntMap/Mapcard.vo \
 theories/IntMap/Addr.vo       theories/IntMap/Mapc.vo \
 theories/IntMap/Adist.vo      theories/IntMap/Mapfold.vo \
 theories/IntMap/Allmaps.vo    theories/IntMap/Mapiter.vo \
 theories/IntMap/Fset.vo       theories/IntMap/Maplists.vo \
 theories/IntMap/Lsort.vo      theories/IntMap/Mapsubset.vo \
 theories/IntMap/Mapaxioms.vo  theories/IntMap/Map.vo \

RELATIONSVO=\
 theories/Relations/Newman.vo \
 theories/Relations/Operators_Properties.vo \
 theories/Relations/Relation_Definitions.vo \
 theories/Relations/Relation_Operators.vo \
 theories/Relations/Relations.vo \
 theories/Relations/Rstar.vo

WELLFOUNDEDVO=\
 theories/Wellfounded/Disjoint_Union.vo \
 theories/Wellfounded/Inclusion.vo \
 theories/Wellfounded/Inverse_Image.vo \
 theories/Wellfounded/Lexicographic_Exponentiation.vo \
 theories/Wellfounded/Transitive_Closure.vo \
 theories/Wellfounded/Union.vo \
 theories/Wellfounded/Wellfounded.vo \
 theories/Wellfounded/Well_Ordering.vo \
 theories/Wellfounded/Lexicographic_Product.vo 

REALSBASEVO=\
 theories/Reals/Rdefinitions.vo \
 theories/Reals/Raxioms.vo      theories/Reals/RIneq.vo \
 theories/Reals/DiscrR.vo       theories/Reals/Rbase.vo \

REALS_basic= 

REALS_all=\
 theories/Reals/R_Ifp.vo \
 theories/Reals/Rbasic_fun.vo   theories/Reals/R_sqr.vo \
 theories/Reals/SplitAbsolu.vo  theories/Reals/SplitRmult.vo \
 theories/Reals/ArithProp.vo    theories/Reals/Rfunctions.vo \
 theories/Reals/Rseries.vo      theories/Reals/SeqProp.vo \
 theories/Reals/Rcomplete.vo    theories/Reals/PartSum.vo \
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
ALLOLDREALS=$(REALSBASEVO:theories%.vo:theories7%.vo) $(REALS_all:theories%.vo:theories7%.vo)

SETOIDSVO=theories/Setoids/Setoid.vo

THEORIESVO =\
  $(INITVO) $(LOGICVO) $(ARITHVO) $(BOOLVO) $(NARITHVO) $(ZARITHVO) \
  $(LISTSVO) $(SETSVO) $(INTMAPVO) $(RELATIONSVO) $(WELLFOUNDEDVO) \
  $(REALSVO) $(SETOIDSVO) $(SORTINGVO)

NEWTHEORIESLIGHTVO = $(INITVO) $(LOGICVO) $(ARITHVO)
OLDTHEORIESLIGHTVO = $(NEWTHEORIESLIGHTVO:theories%.vo:theories7%.vo)

theories: $(THEORIESVO)
theories-light: $(NEWTHEORIESLIGHTVO)

logic: $(LOGICVO)
arith: $(ARITHVO)
bool: $(BOOLVO)
narith: $(NARITHVO)
zarith: $(ZARITHVO)
lists: $(LISTVO) $(LISTSVO)
sets: $(SETSVO)
intmap: $(INTMAPVO)
relations: $(RELATIONSVO)
wellfounded: $(WELLFOUNDEDVO)
# reals
reals: $(REALSVO)
allreals: $(ALLREALS)
setoids: $(SETOIDSVO)
sorting: $(SORTINGVO)

noreal: logic arith bool zarith lists sets intmap relations wellfounded \
	setoids sorting

###########################################################################
# contribs (interface not included)
###########################################################################

OMEGAVO=\
 contrib/omega/OmegaLemmas.vo contrib/omega/Omega.vo

ROMEGAVO=\
 contrib/romega/ReflOmegaCore.vo contrib/romega/ROmega.vo 

RINGVO=\
 contrib/ring/ArithRing.vo      contrib/ring/Ring_normalize.vo \
 contrib/ring/Ring_theory.vo    contrib/ring/Ring.vo \
 contrib/ring/NArithRing.vo     \
 contrib/ring/ZArithRing.vo     contrib/ring/Ring_abstract.vo \
 contrib/ring/Quote.vo		contrib/ring/Setoid_ring_normalize.vo \
 contrib/ring/Setoid_ring.vo	contrib/ring/Setoid_ring_theory.vo

FIELDVO=\
 contrib/field/Field_Compl.vo     contrib/field/Field_Theory.vo \
 contrib/field/Field_Tactic.vo    contrib/field/Field.vo

XMLVO= 

FOURIERVO=\
 contrib/fourier/Fourier_util.vo    contrib/fourier/Fourier.vo

FUNINDVO= 

JPROVERVO= 

CCVO=\
 contrib/cc/CCSolve.vo

CONTRIBVO = $(OMEGAVO) $(ROMEGAVO) $(RINGVO) $(FIELDVO) $(XMLVO) \
	    $(FOURIERVO) $(JPROVERVO) $(CCVO) $(FUNINDVO)

$(CONTRIBVO): states/initial.coq

contrib: $(CONTRIBVO) $(CONTRIBCMO)
omega: $(OMEGAVO) $(OMEGACMO) $(ROMEGAVO) $(ROMEGACMO)
ring: $(RINGVO) $(RINGCMO)
xml: $(XMLVO) $(XMLCMO)
extraction: $(EXTRACTIONCMO)
field: $(FIELDVO) $(FIELDCMO)
fourier: $(FOURIERVO) $(FOURIERCMO)
jprover: $(JPROVERVO) $(JPROVERCMO)
funind: $(FUNINDCMO) $(FUNINDVO)
cc: $(CCVO) $(CCCMO)

NEWINITVO=$(INITVO)
NEWTHEORIESVO=$(THEORIESVO)
NEWCONTRIBVO=$(CONTRIBVO)

OBSOLETETHEORIESVO=\
 theories7/Lists/PolyList.vo theories7/Lists/PolyListSyntax.vo \
 theories7/ZArith/Zsyntax.vo \
 theories7/ZArith/zarith_aux.vo	theories7/ZArith/fast_integer.vo \
 theories7/Reals/Rsyntax.vo

OLDINITVO=$(INITVO:theories%.vo=theories7%.vo)
OLDTHEORIESVO=$(THEORIESVO:theories%.vo=theories7%.vo) $(OBSOLETETHEORIESVO)
OLDCONTRIBVO=$(CONTRIBVO:contrib%.vo=contrib7%.vo)

$(OLDCONTRIBVO): states7/initial.coq

NEWINITV=$(INITVO:%.vo=%.v)
NEWTHEORIESV=$(THEORIESVO:%.vo=%.v)
NEWCONTRIBV=$(CONTRIBVO:%.vo=%.v)

# Made *.vo and new*.v targets explicit, otherwise "make" 
# either removes them after use or don't do them (e.g. List.vo)
newinit:: $(NEWINITV) $(NEWINITVO)
newtheories:: $(NEWTHEORIESV) $(NEWTHEORIESVO)
newcontrib:: $(NEWCONTRIBV) $(NEWCONTRIBVO) $(CONTRIBCMO)

theories7:: $(OLDTHEORIESVO)
contrib7:: $(OLDCONTRIBVO) 

translation:: $(NEWTHEORIESV) $(NEWCONTRIBV)

ALLNEWVO = $(INITVO) $(THEORIESVO) $(CONTRIBVO)
ALLOLDVO = $(OLDINITVO) $(OLDTHEORIESVO) $(OLDCONTRIBVO)

###########################################################################
# rules to make theories, contrib and states
###########################################################################

SYNTAXPP=syntax/PPConstr.v syntax/PPCases.v

states7/barestate.coq: $(SYNTAXPP) $(BESTCOQTOP)
	$(BESTCOQTOP) -v7 -boot -batch -silent -nois -I syntax -load-vernac-source syntax/MakeBare.v -outputstate $@

states7/initial.coq: states7/barestate.coq states7/MakeInitial.v $(OLDINITVO) $(BESTCOQTOP)
	$(BOOTCOQTOP) -v7 -batch -silent -is states7/barestate.coq -load-vernac-source states7/MakeInitial.v -outputstate states7/initial.coq

states/initial.coq: states/MakeInitial.v $(NEWINITVO)
	$(BOOTCOQTOP) -batch -silent -nois -load-vernac-source states/MakeInitial.v -outputstate states/initial.coq

theories7/Init/%.vo: $(BESTCOQTOP) theories7/Init/%.v
	$(BOOTCOQTOP) $(TRANSLATE) -nois -compile theories7/Init/$*

theories7/%.vo: theories7/%.v states7/initial.coq
	$(BOOTCOQTOP) $(TRANSLATE) -compile theories7/$*

contrib7/%.vo: contrib7/%.v states7/initial.coq
	$(BOOTCOQTOP) $(TRANSLATE) -compile contrib7/$*

theories/Init/%.vo: $(BESTCOQTOP) theories/Init/%.v
	$(BOOTCOQTOP) -nois -compile theories/Init/$*

theories/%.vo: theories/%.v states/initial.coq
	$(BOOTCOQTOP) -compile theories/$*

contrib/%.vo: contrib/%.v
	$(BOOTCOQTOP) -compile contrib/$*

contrib/extraction/%.vo: contrib/extraction/%.v states/barestate.coq $(COQC)
	$(BOOTCOQTOP) -is states/barestate.coq -compile $*

contrib7/extraction/%.vo: contrib7/extraction/%.v states/barestate.coq $(COQC)
	$(BOOTCOQTOP) $(TRANSLATE) -is states7/barestate.coq -compile $*

clean::
	rm -f states/*.coq states7/*.coq
	rm -f theories/*/*.vo theories7/*/*.vo
	rm -f contrib/*/*.cm[io] contrib/*.cma contrib/*/*.vo contrib7/*/*.vo 

archclean::
	rm -f contrib/*/*.cmx contrib/*.cmxa contrib/*.a contrib/*/*.[so]

# globalizations (for coqdoc)

glob.dump::
	rm -f glob.dump
	rm -f theories/*/*.vo
	$(MAKE) GLOB="-dump-glob glob.dump" world

###########################################################################
# tools
###########################################################################

COQDEP=bin/coqdep$(EXE)
COQMAKEFILE=bin/coq_makefile$(EXE)
GALLINA=bin/gallina$(EXE)
COQTEX=bin/coq-tex$(EXE)
COQWC=bin/coqwc$(EXE)
COQDOC=bin/coqdoc$(EXE)

TOOLS=$(COQDEP) $(COQMAKEFILE) $(GALLINA) $(COQTEX) \
      $(COQWC) $(COQDOC)

tools:: $(TOOLS) dev/top_printers.cmo

COQDEPCMO=config/coq_config.cmo tools/coqdep_lexer.cmo tools/coqdep.cmo

$(COQDEP): $(COQDEPCMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ unix.cma $(COQDEPCMO) $(OSDEPLIBS)

beforedepend:: tools/coqdep_lexer.ml $(COQDEP)

GALLINACMO=tools/gallina_lexer.cmo tools/gallina.cmo

$(GALLINA): $(GALLINACMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ $(GALLINACMO)

beforedepend:: tools/gallina_lexer.ml

$(COQMAKEFILE): tools/coq_makefile.cmo
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ tools/coq_makefile.cmo

$(COQTEX): tools/coq-tex.cmo
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ str.cma tools/coq-tex.cmo

beforedepend:: tools/coqwc.ml

$(COQWC): tools/coqwc.cmo
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ tools/coqwc.cmo

beforedepend:: tools/coqdoc/pretty.ml tools/coqdoc/index.ml

COQDOCCMO=$(CONFIG) tools/coqdoc/alpha.cmo tools/coqdoc/index.cmo \
          tools/coqdoc/output.cmo tools/coqdoc/pretty.cmo \
	  tools/coqdoc/main.cmo

$(COQDOC): $(COQDOCCMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ str.cma unix.cma $(COQDOCCMO)

clean::
	rm -f tools/coqdep_lexer.ml tools/gallina_lexer.ml
	rm -f tools/coqwc.ml
	rm -f tools/coqdoc/pretty.ml tools/coqdoc/index.ml

archclean::
	rm -f $(TOOLS)

###########################################################################
# minicoq
###########################################################################

MINICOQCMO=$(CONFIG) $(LIBREP) $(KERNEL) \
	   parsing/lexer.cmo parsing/g_minicoq.cmo \
	   toplevel/fhimsg.cmo toplevel/minicoq.cmo

MINICOQ=bin/minicoq$(EXE)

$(MINICOQ): $(MINICOQCMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -o $@ -custom $(CMA) $(MINICOQCMO) $(OSDEPLIBS)

archclean::
	rm -f $(MINICOQ)

###########################################################################
# Installation
###########################################################################

#COQINSTALLPREFIX=
# Can be changed for a local installation (to make packages).
# You must NOT put a "/" at the end (Cygnus for win32 does not like "//").

FULLBINDIR=$(COQINSTALLPREFIX)$(BINDIR)
FULLCOQLIB=$(COQINSTALLPREFIX)$(COQLIB)
FULLMANDIR=$(COQINSTALLPREFIX)$(MANDIR)
FULLEMACSLIB=$(COQINSTALLPREFIX)$(EMACSLIB)
FULLCOQDOCDIR=$(COQINSTALLPREFIX)$(COQDOCDIR)

install-coq: install-binaries install-library install-coq-info
install-coq8: install-binaries install-library8 install-coq-info
install-coq7: install-binaries install-library7 install-coq-info
install-coqlight: install-binaries install-library-light

install-binaries:: install-$(BEST) install-tools

install-byte::
	$(MKDIR) $(FULLBINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqtop.byte$(EXE) coqtop$(EXE)

install-opt::
	$(MKDIR) $(FULLBINDIR)
	cp $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(COQTOPOPT) $(FULLBINDIR)
	cd $(FULLBINDIR); ln -sf coqtop.opt$(EXE) coqtop$(EXE)

install-tools::
	$(MKDIR) $(FULLBINDIR)
	cp $(TOOLS) $(FULLBINDIR)

LIBFILES=$(OLDTHEORIESVO) $(OLDCONTRIBVO)
LIBFILESLIGHT=$(OLDTHEORIESLIGHTVO)

NEWLIBFILES=$(NEWTHEORIESVO) $(NEWCONTRIBVO)
NEWLIBFILESLIGHT=$(NEWTHEORIESLIGHTVO)

install-library: install-library7 install-library8

install-library8:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(NEWLIBFILES); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states
	cp states/*.coq $(FULLCOQLIB)/states

install-library7:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(LIBFILES); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states7
	cp states7/*.coq $(FULLCOQLIB)/states7

install-library-light:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(LIBFILESLIGHT) $(NEWLIBFILESLIGHT); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states
	cp states/*.coq $(FULLCOQLIB)/states
	$(MKDIR) $(FULLCOQLIB)/states7
	cp states7/*.coq $(FULLCOQLIB)/states7

install-allreals::
	for f in $(ALLREALS); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done

install-coq-info: install-coq-manpages install-emacs install-latex

MANPAGES=man/coq-tex.1 man/coqdep.1 man/gallina.1 \
	man/coqc.1 man/coqtop.1 man/coqtop.byte.1 man/coqtop.opt.1 \
	man/coqwc.1 man/coqdoc.1 \
	man/coq_makefile.1 man/coqmktop.1

install-coq-manpages:
	$(MKDIR) $(FULLMANDIR)/man1
	cp $(MANPAGES) $(FULLMANDIR)/man1

install-emacs:
	$(MKDIR) $(FULLEMACSLIB)
	cp tools/coq.el tools/coq-inferior.el $(FULLEMACSLIB)

# command to update TeX' kpathsea database
#UPDATETEX = $(MKTEXLSR) /usr/share/texmf /var/spool/texmf $(BASETEXDIR) > /dev/null

install-latex:
	$(MKDIR) $(FULLCOQDOCDIR)
	cp tools/coqdoc/coqdoc.sty $(FULLCOQDOCDIR)	
#	-$(UPDATETEX)

###########################################################################
# Documentation
# Literate programming (with ocamlweb)
###########################################################################

.PHONY: doc

doc: doc/coq.tex
	$(MAKE) -C doc coq.ps minicoq.dvi

doc/coq.tex:
	ocamlweb -p "\usepackage{epsfig}" \
	doc/macros.tex doc/intro.tex \
	lib/{doc.tex,*.mli} kernel/{doc.tex,*.mli} library/{doc.tex,*.mli} \
	pretyping/{doc.tex,*.mli} interp/{doc.tex,*.mli} \
	parsing/{doc.tex,*.mli} proofs/{doc.tex,tacexpr.ml,*.mli} \
	tactics/{doc.tex,*.mli} toplevel/{doc.tex,vernacexpr.ml,*.mli} \
	-o doc/coq.tex

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
  lib/pp_control.cmo lib/pp.cmo lib/compat.cmo lib/util.cmo lib/bignat.cmo \
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
  parsing/g_ltac.cmo parsing/g_constr.cmo \
  parsing/g_primnew.cmo parsing/g_tacticnew.cmo \
  parsing/g_ltacnew.cmo parsing/g_constrnew.cmo 

GRAMMARCMO=$(GRAMMARNEEDEDCMO) $(CAMLP4EXTENSIONSCMO) $(GRAMMARSCMO)

parsing/grammar.cma: $(GRAMMARCMO)
	$(SHOW)'OCAMLC -a $@'   
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) $(GRAMMARCMO) -linkall -a -o $@

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
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -c -impl $< -o $@

toplevel/mltop.cmx: toplevel/mltop.optml
	$(SHOW)'OCAMLOPT  $<'	
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -c -impl $< -o $@

toplevel/mltop.byteml: toplevel/mltop.ml4
	$(SHOW)'CAMLP4O   $<'	
	$(HIDE)$(CAMLP4O) $(CAMLP4EXTENDFLAGS) pr_o.cmo -DByte -impl $< > $@ || rm -f $@

toplevel/mltop.optml: toplevel/mltop.ml4
	$(SHOW)'CAMLP4O   $<'	
	$(HIDE)$(CAMLP4O) $(CAMLP4EXTENDFLAGS) pr_o.cmo -impl $< > $@ || rm -f $@

ML4FILES += toplevel/mltop.ml4

clean::
	rm -f toplevel/mltop.byteml toplevel/mltop.optml

# files compiled with -rectypes

kernel/term.cmo: kernel/term.ml
	$(SHOW)'OCAMLC    -rectypes $<' 
	$(HIDE)$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

kernel/term.cmx: kernel/term.ml
	$(SHOW)'OCAMLOPT  -rectypes $<'
	$(HIDE)$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

library/nametab.cmo: library/nametab.ml
	$(SHOW)'OCAMLC    -rectypes $<'
	$(HIDE)$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

library/nametab.cmx: library/nametab.ml
	$(SHOW)'OCAMLOPT  -rectypes $<'
	$(HIDE)$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

proofs/tacexpr.cmo: proofs/tacexpr.ml
	$(SHOW)'OCAMLC    -rectypes $<'
	$(HIDE)$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

proofs/tacexpr.cmx: proofs/tacexpr.ml
	$(SHOW)'OCAMLOPT  -rectypes $<'
	$(HIDE)$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

# files compiled with camlp4 because of macros

lib/compat.cmo: lib/compat.ml4
	$(SHOW)'OCAMLC4  $<' 
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) -impl" -c -impl $<

lib/compat.cmx: lib/compat.ml4
	$(SHOW)'OCAMLOPT  $<' 
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) -impl" -c -impl $<

# files compiled with camlp4 because of streams syntax

ML4FILES += lib/pp.ml4 			\
         lib/compat.ml4 	       	\
	 contrib/xml/xml.ml4		\
	 contrib/xml/acic2Xml.ml4	\
	 contrib/xml/proofTree2Xml.ml4	\
	 contrib/interface/line_parser.ml4	\
	 tools/coq_makefile.ml4		\
	 tools/coq-tex.ml4

# Add pr_o.cmo to circumvent a useless-warning bug when preprocessed with
# ast-based camlp4

#parsing/lexer.cmx: parsing/lexer.ml4
#	$(SHOW)'OCAMLOPT4 $<'
#	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` pr_o.cmo -impl" -c -impl $<

#parsing/lexer.cmo: parsing/lexer.ml4
#	$(SHOW)'OCAMLC4   $<'
#	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` pr_o.cmo -impl" -c -impl $<



###########################################################################
# Default rules
###########################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly .ml4 .v .vo .el .elc

.ml.cmo:
	$(SHOW)'OCAMLC    $<'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -c $<

.mli.cmi:
	$(SHOW)'OCAMLC    $<'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -c $<

.ml.cmx:
	$(SHOW)'OCAMLOPT  $<'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -c $<

.mll.ml:
	$(SHOW)'OCAMLLEX  $<'
	$(HIDE)ocamllex $<

.mly.ml:
	$(SHOW)'OCAMLYACC $<'
	$(HIDE)ocamlyacc $<

.mly.mli:
	$(SHOW)'OCAMLYACC $<'
	$(HIDE)ocamlyacc $<

.ml4.cmx:
	$(SHOW)'OCAMLOPT4 $<'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` $(CAMLP4COMPAT) -impl" -c -impl $<

.ml4.cmo:
	$(SHOW)'OCAMLC4   $<'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` $(CAMLP4COMPAT) -impl" -c -impl $<

#.v.vo:
#	$(BOOTCOQTOP) -compile $*

.el.elc:
	echo "(setq load-path (cons \".\" load-path))" > $*.compile
	echo "(byte-compile-file \"$<\")" >> $*.compile
	- $(EMACS) -batch -l $*.compile
	rm -f $*.compile        

###########################################################################
# Cleaning
###########################################################################

archclean::
	rm -f config/*.cmx* config/*.[soa]
	rm -f lib/*.cmx* lib/*.[soa]
	rm -f kernel/*.cmx* kernel/*.[soa]
	rm -f library/*.cmx* library/*.[soa]
	rm -f proofs/*.cmx* proofs/*.[soa]
	rm -f tactics/*.cmx* tactics/*.[soa]
	rm -f interp/*.cmx* interp/*.[soa]
	rm -f parsing/*.cmx* parsing/*.[soa]
	rm -f pretyping/*.cmx* pretyping/*.[soa]
	rm -f toplevel/*.cmx* toplevel/*.[soa]
	rm -f ide/*.cmx* ide/*.[soa]
	rm -f ide/utils/*.cmx* ide/utils/*.[soa]
	rm -f translate/*.cmx* translate/*.[soa]
	rm -f tools/*.cmx* tools/*.[soa]
	rm -f tools/*/*.cmx* tools/*/*.[soa]
	rm -f scripts/*.cmx* scripts/*.[soa]
	rm -f dev/*.cmx* dev/*.[soa]

clean:: archclean
	rm -f *~ */*~ */*/*~
	rm -f gmon.out core
	rm -f config/*.cm[ioa]
	rm -f lib/*.cm[ioa]
	rm -f kernel/*.cm[ioa]
	rm -f library/*.cm[ioa]
	rm -f proofs/*.cm[ioa]
	rm -f tactics/*.cm[ioa]
	rm -f interp/*.cm[ioa]
	rm -f parsing/*.cm[ioa] parsing/*.ppo
	rm -f pretyping/*.cm[ioa]
	rm -f toplevel/*.cm[ioa]
	rm -f ide/*.cm[ioa]
	rm -f ide/utils/*.cm[ioa]
	rm -f translate/*.cm[ioa]
	rm -f tools/*.cm[ioa]
	rm -f tools/*/*.cm[ioa]
	rm -f scripts/*.cm[ioa]
	rm -f dev/*.cm[ioa]
	rm -f */*.pp[iox] contrib/*/*.pp[iox]

cleanconfig::
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-v7

###########################################################################
# Dependencies
###########################################################################

alldepend: depend dependcoq 

dependcoq:: beforedepend
	$(COQDEP) -coqlib . -R theories Coq -R contrib Coq $(COQINCLUDES) \
	 $(ALLREALS:.vo=.v) $(ALLNEWVO:.vo=.v) > .depend.coq
	$(COQDEP) -coqlib . -R theories7 Coq -R contrib7 Coq $(COQINCLUDES) \
	 $(ALLOLDREALS:.vo=.v) $(ALLOLDVO:.vo=.v) > .depend.coq7

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

# this sets up developper supporting stuff
devel:	
	touch .depend.devel
	$(MAKE) -f dev/Makefile.devel setup-devel
	$(MAKE) dev/top_printers.cmo

include .depend
include .depend.coq
include .depend.coq7

clean::
	rm -fr *.v8 syntax/*.v8 ide/*.v8 theories7/*/*.v8 contrib7/*/*.v8
	find . -name "\.#*" -exec rm -f {} \;
	find . -name "*~" -exec rm -f {} \;

###########################################################################
