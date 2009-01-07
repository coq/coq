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

.PHONY: NOARG

NOARG: world

help:
	@echo "Please use either"
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make clean"
	@echo "or make archclean"
	@echo
	@echo "For make to be verbose, add VERBOSE=1"


# build and install the three subsystems: coq, coqide, pcoq
world: depend dependcoq
	$(MAKE) worldnodep

worldnodep: revision coq coqide pcoq

install: install-coq install-coqide install-pcoq
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
	      -I scripts -I lib -I kernel -I kernel/byterun -I library \
              -I proofs -I tactics -I pretyping \
              -I interp -I toplevel -I parsing -I ide/utils -I ide \
              -I contrib/omega -I contrib/romega \
	      -I contrib/ring -I contrib/dp -I contrib/setoid_ring \
              -I contrib/xml -I contrib/extraction \
              -I contrib/interface -I contrib/fourier \
	      -I contrib/jprover -I contrib/cc \
	      -I contrib/funind -I contrib/first-order \
              -I contrib/field -I contrib/subtac -I contrib/rtauto \
              -I contrib/recdef

MLINCLUDES=$(LOCALINCLUDES) -I $(MYCAMLP4LIB) $(COQIDEINCLUDES)

OCAMLC += $(CAMLFLAGS)
OCAMLOPT += $(CAMLFLAGS)

BYTEFLAGS=$(MLINCLUDES) $(CAMLDEBUG) $(USERFLAGS)
OPTFLAGS=$(MLINCLUDES) $(CAMLTIMEPROF) $(INLINEFLAG) $(USERFLAGS)
DEPFLAGS= -slash $(LOCALINCLUDES)

OCAMLC_P4O=$(OCAMLC) -pp $(CAMLP4O) $(BYTEFLAGS)
OCAMLOPT_P4O=$(OCAMLOPT) -pp $(CAMLP4O) $(OPTFLAGS)
CAMLP4EXTENSIONS=-I . pa_extend.cmo pa_extend_m.cmo q_MLast.cmo pa_macro.cmo
CAMLP4OPTIONS=$(CAMLP4COMPAT) -D$(CAMLVERSION)
CAMLP4DEPS=sed -n -e 's|^(\*.*camlp4deps: "\(.*\)".*\*)|\1|p'

COQINCLUDES=          # coqtop includes itself the needed paths
GLOB=           # is "-dump-glob file" when making the doc
COQ_XML=	# is "-xml" when building XML library
VM=          # is "-no-vm" to not use the vm"
UNBOXEDVALUES=  # is "-unboxed-values" to use unboxed values
COQOPTS=$(GLOB) $(COQ_XML) $(VM) $(UNBOXEDVALUES)
TIME=           # is "'time -p'" to get compilation time of .v 

BOOTCOQTOP= $(TIME) $(BESTCOQTOP) -boot $(COQOPTS) 

###########################################################################
# Objects files 
###########################################################################

LIBCOQRUN=kernel/byterun/libcoqrun.a

CLIBS=unix.cma

CAMLP4OBJS=gramlib.cma

CONFIG=\
  config/coq_config.cmo

LIBREP=\
  lib/pp_control.cmo lib/pp.cmo lib/compat.cmo lib/util.cmo lib/bigint.cmo \
  lib/hashcons.cmo lib/dyn.cmo lib/system.cmo lib/options.cmo \
  lib/bstack.cmo lib/edit.cmo lib/gset.cmo lib/gmap.cmo \
  lib/tlm.cmo lib/gmapl.cmo lib/profile.cmo lib/explore.cmo \
  lib/predicate.cmo lib/rtree.cmo lib/heap.cmo
# Rem: Cygwin already uses variable LIB 

BYTERUN=\
  kernel/byterun/coq_fix_code.o kernel/byterun/coq_memory.o \
  kernel/byterun/coq_values.o kernel/byterun/coq_interp.o 

KERNEL=\
  kernel/names.cmo kernel/univ.cmo \
  kernel/esubst.cmo kernel/term.cmo kernel/mod_subst.cmo kernel/sign.cmo \
  kernel/cbytecodes.cmo kernel/copcodes.cmo \
  kernel/cemitcodes.cmo kernel/vm.cmo \
  kernel/declarations.cmo kernel/pre_env.cmo \
  kernel/cbytegen.cmo  kernel/environ.cmo  \
  kernel/csymtable.cmo kernel/conv_oracle.cmo \
  kernel/closure.cmo kernel/reduction.cmo kernel/type_errors.cmo \
  kernel/entries.cmo kernel/modops.cmo \
  kernel/inductive.cmo kernel/vconv.cmo kernel/typeops.cmo \
  kernel/indtypes.cmo kernel/cooking.cmo kernel/term_typing.cmo \
  kernel/subtyping.cmo kernel/mod_typing.cmo kernel/safe_typing.cmo

LIBRARY=\
  library/nameops.cmo library/libnames.cmo library/libobject.cmo \
  library/summary.cmo library/nametab.cmo library/global.cmo library/lib.cmo \
  library/declaremods.cmo library/library.cmo library/states.cmo \
  library/decl_kinds.cmo library/dischargedhypsmap.cmo library/goptions.cmo

PRETYPING=\
  pretyping/termops.cmo pretyping/evd.cmo \
  pretyping/reductionops.cmo pretyping/vnorm.cmo pretyping/inductiveops.cmo \
  pretyping/retyping.cmo pretyping/cbv.cmo \
  pretyping/pretype_errors.cmo pretyping/recordops.cmo pretyping/typing.cmo \
  pretyping/tacred.cmo \
  pretyping/evarutil.cmo pretyping/unification.cmo pretyping/evarconv.cmo \
  pretyping/classops.cmo pretyping/coercion.cmo pretyping/clenv.cmo \
  pretyping/rawterm.cmo pretyping/pattern.cmo \
  pretyping/detyping.cmo  pretyping/indrec.cmo\
  pretyping/cases.cmo pretyping/pretyping.cmo pretyping/matching.cmo

INTERP=\
  parsing/lexer.cmo interp/topconstr.cmo interp/ppextend.cmo \
  interp/notation.cmo \
  interp/genarg.cmo interp/syntax_def.cmo interp/reserve.cmo \
  library/impargs.cmo interp/constrintern.cmo \
  interp/modintern.cmo interp/constrextern.cmo interp/coqlib.cmo \
  toplevel/discharge.cmo library/declare.cmo

PROOFS=\
  proofs/tacexpr.cmo proofs/proof_type.cmo proofs/redexpr.cmo \
  proofs/proof_trees.cmo proofs/logic.cmo \
  proofs/refiner.cmo proofs/evar_refiner.cmo proofs/tacmach.cmo \
  proofs/pfedit.cmo proofs/tactic_debug.cmo \
  proofs/clenvtac.cmo proofs/decl_mode.cmo

PARSING=\
  parsing/extend.cmo \
  parsing/pcoq.cmo parsing/egrammar.cmo parsing/g_xml.cmo \
  parsing/ppconstr.cmo parsing/printer.cmo \
  parsing/pptactic.cmo parsing/ppdecl_proof.cmo parsing/tactic_printer.cmo \
  parsing/printmod.cmo parsing/prettyp.cmo parsing/search.cmo 

HIGHPARSING=\
  parsing/g_constr.cmo parsing/g_vernac.cmo parsing/g_prim.cmo \
  parsing/g_proofs.cmo parsing/g_tactic.cmo parsing/g_ltac.cmo \
  parsing/g_natsyntax.cmo parsing/g_zsyntax.cmo parsing/g_rsyntax.cmo \
  parsing/g_ascii_syntax.cmo parsing/g_string_syntax.cmo \
  parsing/g_decl_mode.cmo

TACTICS=\
  tactics/dn.cmo tactics/termdn.cmo tactics/btermdn.cmo \
  tactics/nbtermdn.cmo tactics/tacticals.cmo \
  tactics/hipattern.cmo tactics/tactics.cmo \
  tactics/evar_tactics.cmo \
  tactics/hiddentac.cmo tactics/elim.cmo \
  tactics/dhyp.cmo tactics/auto.cmo \
  tactics/setoid_replace.cmo tactics/equality.cmo \
  tactics/contradiction.cmo tactics/inv.cmo tactics/leminv.cmo \
  tactics/tacinterp.cmo tactics/autorewrite.cmo \
  tactics/decl_interp.cmo tactics/decl_proof_instr.cmo

TOPLEVEL=\
  toplevel/himsg.cmo toplevel/cerrors.cmo toplevel/class.cmo \
  toplevel/vernacexpr.cmo toplevel/metasyntax.cmo \
  toplevel/command.cmo toplevel/record.cmo \
  parsing/ppvernac.cmo \
  toplevel/vernacinterp.cmo toplevel/mltop.cmo \
  toplevel/vernacentries.cmo toplevel/whelp.cmo toplevel/vernac.cmo \
  toplevel/line_oriented_parser.cmo toplevel/protectedtoplevel.cmo \
  toplevel/toplevel.cmo toplevel/usage.cmo \
  toplevel/coqinit.cmo toplevel/coqtop.cmo

HIGHTACTICS=\
  tactics/refine.cmo tactics/extraargs.cmo \
  tactics/extratactics.cmo tactics/eauto.cmo

SPECTAC= tactics/tauto.ml4 tactics/eqdecide.ml4
USERTAC = $(SPECTAC)
ML4FILES += $(USERTAC) tactics/extraargs.ml4 tactics/extratactics.ml4 \
	tactics/eauto.ml4 toplevel/whelp.ml4 tactics/hipattern.ml4

USERTACCMO=$(USERTAC:.ml4=.cmo)
USERTACCMX=$(USERTAC:.ml4=.cmx)

ML4FILES +=\
  contrib/omega/g_omega.ml4 \
  contrib/romega/g_romega.ml4 contrib/ring/g_quote.ml4 \
  contrib/ring/g_ring.ml4 contrib/dp/g_dp.ml4 \
  contrib/setoid_ring/newring.ml4  \
  contrib/field/field.ml4 contrib/fourier/g_fourier.ml4 \
  contrib/extraction/g_extraction.ml4 contrib/xml/xmlentries.ml4

OMEGACMO=\
  contrib/omega/omega.cmo contrib/omega/coq_omega.cmo \
  contrib/omega/g_omega.cmo 

ROMEGACMO=\
  contrib/romega/const_omega.cmo \
  contrib/romega/refl_omega.cmo contrib/romega/g_romega.cmo

RINGCMO=\
  contrib/ring/quote.cmo contrib/ring/g_quote.cmo \
  contrib/ring/ring.cmo contrib/ring/g_ring.cmo 

NEWRINGCMO=\
  contrib/setoid_ring/newring.cmo

DPCMO=contrib/dp/dp_why.cmo contrib/dp/dp.cmo contrib/dp/g_dp.cmo

FIELDCMO=\
  contrib/field/field.cmo 

XMLCMO=\
  contrib/xml/unshare.cmo contrib/xml/xml.cmo contrib/xml/acic.cmo \
  contrib/xml/doubleTypeInference.cmo \
  contrib/xml/cic2acic.cmo contrib/xml/acic2Xml.cmo \
  contrib/xml/proof2aproof.cmo \
  contrib/xml/xmlcommand.cmo contrib/xml/proofTree2Xml.cmo \
  contrib/xml/xmlentries.cmo 	contrib/xml/cic2Xml.cmo

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
  contrib/funind/tacinvutils.cmo contrib/funind/tacinv.cmo \
  contrib/funind/indfun_common.cmo contrib/funind/rawtermops.cmo \
  contrib/funind/rawterm_to_relation.cmo \
  contrib/funind/functional_principles_proofs.cmo \
  contrib/funind/functional_principles_types.cmo \
  contrib/funind/invfun.cmo contrib/funind/indfun.cmo \
  contrib/funind/merge.cmo contrib/funind/indfun_main.cmo

RECDEFCMO=\
  contrib/recdef/recdef.cmo

FOCMO=\
  contrib/first-order/formula.cmo contrib/first-order/unify.cmo \
  contrib/first-order/sequent.cmo contrib/first-order/rules.cmo \
  contrib/first-order/instances.cmo contrib/first-order/ground.cmo \
  contrib/first-order/g_ground.cmo

CCCMO=contrib/cc/ccalgo.cmo contrib/cc/ccproof.cmo contrib/cc/cctac.cmo \
  contrib/cc/g_congruence.cmo 

SUBTACCMO=contrib/subtac/subtac_utils.cmo contrib/subtac/eterm.cmo \
  contrib/subtac/g_eterm.cmo \
  contrib/subtac/subtac_errors.cmo contrib/subtac/subtac_coercion.cmo \
  contrib/subtac/subtac_obligations.cmo contrib/subtac/subtac_cases.cmo \
  contrib/subtac/subtac_pretyping_F.cmo contrib/subtac/subtac_pretyping.cmo \
  contrib/subtac/subtac_command.cmo contrib/subtac/subtac.cmo \
  contrib/subtac/g_subtac.cmo


RTAUTOCMO=contrib/rtauto/proof_search.cmo contrib/rtauto/refl_tauto.cmo \
	contrib/rtauto/g_rtauto.cmo

ML4FILES += contrib/jprover/jprover.ml4 contrib/cc/g_congruence.ml4 \
	contrib/funind/tacinv.ml4 contrib/first-order/g_ground.ml4 \
	contrib/subtac/g_subtac.ml4 contrib/subtac/g_eterm.ml4 \
	contrib/rtauto/g_rtauto.ml4 contrib/recdef/recdef.ml4 \
	contrib/funind/indfun_main.ml4 


CONTRIB=$(OMEGACMO) $(ROMEGACMO) $(RINGCMO) $(NEWRINGCMO) $(DPCMO) $(FIELDCMO) \
	$(FOURIERCMO) $(EXTRACTIONCMO) $(JPROVERCMO) $(XMLCMO) \
	$(CCCMO)  $(FOCMO) $(SUBTACCMO) $(RTAUTOCMO) \
        $(RECDEFCMO) $(FUNINDCMO)

CMA=$(CLIBS) $(CAMLP4OBJS)
CMXA=$(CMA:.cma=.cmxa)

# LINK ORDER:
# Beware that highparsing.cma should appear before hightactics.cma
# respecting this order is useful for developers that want to load or link
# the libraries directly
LINKCMO=$(CONFIG) lib/lib.cma kernel/kernel.cma library/library.cma \
        pretyping/pretyping.cma interp/interp.cma proofs/proofs.cma \
        parsing/parsing.cma tactics/tactics.cma toplevel/toplevel.cma \
        parsing/highparsing.cma tactics/hightactics.cma contrib/contrib.cma
LINKCMOCMXA=$(LINKCMO:.cma=.cmxa)
LINKCMX=$(LINKCMOCMXA:.cmo=.cmx)

# objects known by the toplevel of Coq
OBJSCMO=$(CONFIG) $(LIBREP) $(KERNEL) $(LIBRARY) $(PRETYPING) $(INTERP) \
        $(PROOFS) $(PARSING) $(TACTICS) $(TOPLEVEL) $(HIGHPARSING) \
        $(HIGHTACTICS) $(USERTACMO) $(CONTRIB)

###########################################################################
# Compilation option for .c files 
###########################################################################

CINCLUDES= -I $(CAMLHLIB)

# libcoqrun.a 

$(LIBCOQRUN): kernel/byterun/coq_jumptbl.h $(BYTERUN) 
	$(AR) rc $(LIBCOQRUN) $(BYTERUN) 
	$(RANLIB) $(LIBCOQRUN)

#coq_jumptbl.h is required only if you have GCC 2.0 or later
kernel/byterun/coq_jumptbl.h : kernel/byterun/coq_instruct.h
	sed -n -e '/^  /s/ \([A-Z]\)/ \&\&coq_lbl_\1/gp' \
               -e '/^}/q' kernel/byterun/coq_instruct.h > \
                          kernel/byterun/coq_jumptbl.h


kernel/copcodes.ml: kernel/byterun/coq_instruct.h
	sed -n -e '/^enum/p' -e 's/,//g' -e '/^  /p' \
	kernel/byterun/coq_instruct.h | \
	awk -f kernel/make-opcodes > kernel/copcodes.ml

BEFOREDEPEND+= kernel/byterun/coq_jumptbl.h kernel/copcodes.ml

clean ::
	rm -f kernel/byterun/coq_jumptbl.h kernel/copcodes.ml

###########################################################################
# Main targets (coqmktop, coqtop.opt, coqtop.byte)
###########################################################################

COQMKTOPBYTE=bin/coqmktop.byte$(EXE)
COQMKTOPOPT=bin/coqmktop.opt$(EXE)
BESTCOQMKTOP=bin/coqmktop.$(BEST)$(EXE)
COQMKTOP=bin/coqmktop$(EXE) 
COQCBYTE=bin/coqc.byte$(EXE)
COQCOPT=bin/coqc.opt$(EXE)
BESTCOQC=bin/coqc.$(BEST)$(EXE)
COQC=bin/coqc$(EXE)
COQTOPBYTE=bin/coqtop.byte$(EXE)
COQTOPOPT=bin/coqtop.opt$(EXE)
BESTCOQTOP=bin/coqtop.$(BEST)$(EXE)
COQTOP=bin/coqtop$(EXE)

COQBINARIES= $(COQMKTOP) $(COQC) $(COQTOPBYTE) $(BESTCOQTOP) $(COQTOP)

coqbinaries:: ${COQBINARIES}

coq: coqlib tools coqbinaries

coqlib:: theories contrib

coqlight: theories-light tools coqbinaries

states:: states/initial.coq

$(COQTOPOPT): $(COQMKTOP) $(LINKCMX) $(LIBCOQRUN) $(USERTACCMX)
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQTOPBYTE): $(COQMKTOP) $(LINKCMO) $(LIBCOQRUN) $(USERTACCMO)
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -top $(BYTEFLAGS) -o $@

$(COQTOP):
	cd bin; ln -sf coqtop.$(BEST)$(EXE) coqtop$(EXE)

# coqmktop 
COQENVCMO:=$(CONFIG) lib/pp_control.cmo lib/pp.cmo  lib/compat.cmo \
	lib/util.cmo lib/system.cmo
COQMKTOPCMO=$(COQENVCMO) scripts/tolink.cmo scripts/coqmktop.cmo 
COQMKTOPCMX=$(COQMKTOPCMO:.cmo=.cmx)

$(COQMKTOPBYTE): $(COQMKTOPCMO)
	$(SHOW)'OCAMLC -o $@'	
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -o $@ str.cma unix.cma gramlib.cma \
          $(COQMKTOPCMO) $(OSDEPLIBS)

$(COQMKTOPOPT): $(COQMKTOPCMX)
	$(SHOW)'OCAMLOPT -o $@'	
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -o $@ str.cmxa unix.cmxa gramlib.cmxa \
          $(COQMKTOPCMX) $(OSDEPLIBS)

$(COQMKTOP): $(BESTCOQMKTOP)
	cd bin; ln -sf coqmktop.$(BEST)$(EXE) coqmktop$(EXE)


scripts/tolink.ml: Makefile
	$(SHOW)"ECHO... >" $@
	$(HIDE)echo "let copts = \"-cclib -lcoqrun\"" > $@
	$(HIDE)echo "let core_libs = \""$(LINKCMO)"\"" >> $@
	$(HIDE)echo "let core_objs = \""$(OBJSCMO)"\"" >> $@
	$(HIDE)echo "let ide = \""$(COQIDECMO)"\"" >> $@

BEFOREDEPEND+= scripts/tolink.ml

# coqc

COQCCMO=$(CONFIG) toplevel/usage.cmo scripts/coqc.cmo
COQCCMX=config/coq_config.cmx toplevel/usage.cmx scripts/coqc.cmx

$(COQCBYTE): $(COQCCMO) $(COQTOPBYTE) $(BESTCOQTOP)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -o $@ unix.cma $(COQCCMO) $(OSDEPLIBS)

$(COQCOPT): $(COQCCMX) $(COQTOPOPT) $(BESTCOQTOP)
	$(SHOW)'OCAMLOPT -o $@'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -o $@ unix.cmxa $(COQCCMX) $(OSDEPLIBS)

$(COQC): $(BESTCOQC)
	cd bin; ln -sf coqc.$(BEST)$(EXE) coqc$(EXE)


clean::
	rm -f scripts/tolink.ml

archclean::
	rm -f $(COQTOPBYTE) $(COQTOPOPT) $(BESTCOQTOP) $(COQC) $(COQMKTOP)
	rm -f $(COQTOP)

# we provide targets for each subdirectory

lib: $(LIBREP)
kernel: $(KERNEL)
byterun: $(BYTERUN)
library: $(LIBRARY)
proofs: $(PROOFS)
tactics: $(TACTICS)
interp: $(INTERP)
parsing: $(PARSING)
pretyping: $(PRETYPING)
highparsing: $(HIGHPARSING)
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

###########################################################################
# CoqIde special targets
###########################################################################

# target to build CoqIde
coqide:: coqide-files coqide-binaries states

COQIDEBYTE=bin/coqide.byte$(EXE)
COQIDEOPT=bin/coqide.opt$(EXE)
COQIDE=bin/coqide$(EXE)

COQIDECMO=ide/utils/okey.cmo ide/utils/config_file.cmo \
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
COQIDEFLAGS=-thread $(COQIDEINCLUDES)
BEFOREDEPEND+= ide/config_lexer.ml ide/find_phrase.ml ide/highlight.ml
BEFOREDEPEND+= ide/config_parser.mli ide/config_parser.ml
BEFOREDEPEND+= ide/utf8_convert.ml

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

$(COQIDEOPT): $(COQMKTOP) $(LINKCMX) $(LIBCOQRUN) $(USERTACCMX) ide/ide.cmxa
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -ide -opt $(OPTFLAGS) -o $@
	$(STRIP) $@

$(COQIDEBYTE): $(COQMKTOP) $(LINKCMO) $(LIBCOQRUN) $(USERTACCMO) ide/ide.cma
	$(SHOW)'COQMKTOP -o $@'	
	$(HIDE)$(COQMKTOP) -g -ide -top $(BYTEFLAGS) -o $@

$(COQIDE):
	cd bin; ln -sf coqide.$(HASCOQIDE)$(EXE) coqide$(EXE)

ide/%.cmo: ide/%.ml
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/%.cmi: ide/%.mli
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/%.cmx: ide/%.ml
	$(SHOW)'OCAMLOPT  $<'	
	$(HIDE)$(OCAMLOPT) $(COQIDEFLAGS) $(OPTFLAGS) -c $<

ide/utils/%.cmo: ide/%.ml
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/utils/%.cmi: ide/%.mli
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) -g $(COQIDEFLAGS) $(BYTEFLAGS) -c $<

ide/utils/%.cmx: ide/%.ml
	$(SHOW)'OCAMLOPT  $<'	
	$(HIDE)$(OCAMLOPT) $(COQIDEFLAGS) $(OPTFLAGS) -c $<

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

PARSERREQUIRES=$(LINKCMO) $(LIBCOQRUN) # Solution de facilité...
PARSERREQUIRESCMX=$(LINKCMX)

ifeq ($(BEST),opt)
  COQINTERFACE=bin/coq-interface$(EXE) bin/coq-interface.opt$(EXE) bin/parser$(EXE) bin/parser.opt$(EXE)
else
  COQINTERFACE=bin/coq-interface$(EXE) bin/parser$(EXE)
endif

pcoq-binaries:: $(COQINTERFACE) 

bin/coq-interface$(EXE): $(COQMKTOP) $(LINKCMO) $(LIBCOQRUN) $(USERTACCMO) $(INTERFACE)
	$(SHOW)'COQMKTOP -o $@'
	$(HIDE)$(COQMKTOP) -top $(BYTEFLAGS) -o $@ $(INTERFACE)

bin/coq-interface.opt$(EXE): $(COQMKTOP) $(LINKCMX) $(LIBCOQRUN) $(USERTACCMX) $(INTERFACECMX)
	$(SHOW)'COQMKTOP -o $@'
	$(HIDE)$(COQMKTOP) -opt $(OPTFLAGS) -o $@ $(INTERFACECMX)

PARSERCODE=contrib/interface/line_parser.cmo contrib/interface/vtp.cmo \
           contrib/interface/xlate.cmo contrib/interface/parse.cmo
PARSERCMO=$(PARSERREQUIRES) $(PARSERCODE)
PARSERCMX= $(PARSERREQUIRESCMX) $(PARSERCODE:.cmo=.cmx)

bin/parser$(EXE):$(LIBCOQRUN) $(PARSERCMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) -custom -linkall $(BYTEFLAGS) -o $@ \
	  dynlink.cma $(LIBCOQRUN) $(CMA) $(PARSERCMO)

bin/parser.opt$(EXE): $(LIBCOQRUN) $(PARSERCMX)
	$(SHOW)'OCAMLOPT -o $@'
	$(HIDE)$(OCAMLOPT) -linkall $(OPTFLAGS) -o $@ \
	  $(LIBCOQRUN) $(CMXA) $(PARSERCMX)

INTERFACEVO=

INTERFACERC= contrib/interface/vernacrc

pcoq-files:: $(INTERFACEVO) $(INTERFACERC)

clean::
	rm -f bin/parser$(EXE) bin/parser.opt$(EXE) bin/coq-interface$(EXE) bin/coq-interface.opt$(EXE)

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
 theories/Init/Tactics.vo           theories/Init/Prelude.vo

init: $(INITVO)

LOGICVO=\
 theories/Logic/Hurkens.vo            theories/Logic/ProofIrrelevance.vo\
 theories/Logic/Classical.vo          theories/Logic/Classical_Type.vo \
 theories/Logic/Classical_Pred_Set.vo theories/Logic/Eqdep.vo          \
 theories/Logic/Classical_Prop.vo     theories/Logic/Classical_Pred_Type.vo \
 theories/Logic/ClassicalFacts.vo     theories/Logic/ChoiceFacts.vo \
 theories/Logic/Berardi.vo            theories/Logic/Eqdep_dec.vo \
 theories/Logic/Decidable.vo          theories/Logic/JMeq.vo \
 theories/Logic/ClassicalChoice.vo    theories/Logic/ClassicalDescription.vo \
 theories/Logic/RelationalChoice.vo   theories/Logic/Diaconescu.vo \
 theories/Logic/EqdepFacts.vo         theories/Logic/ProofIrrelevanceFacts.vo \
 theories/Logic/ClassicalEpsilon.vo   theories/Logic/ClassicalUniqueChoice.vo \
 theories/Logic/DecidableType.vo      theories/Logic/DecidableTypeEx.vo \
 theories/Logic/ConstructiveEpsilon.vo

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
 theories/Arith/Arith_base.vo 

SORTINGVO=\
 theories/Sorting/Heap.vo	theories/Sorting/Permutation.vo \
 theories/Sorting/Sorting.vo	theories/Sorting/PermutSetoid.vo \
 theories/Sorting/PermutEq.vo
 
BOOLVO=\
 theories/Bool/Bool.vo  	theories/Bool/IfProp.vo \
 theories/Bool/Zerob.vo 	theories/Bool/DecBool.vo \
 theories/Bool/Sumbool.vo 	theories/Bool/BoolEq.vo \
 theories/Bool/Bvector.vo

NARITHVO=\
 theories/NArith/BinPos.vo	theories/NArith/Pnat.vo \
 theories/NArith/BinNat.vo	theories/NArith/NArith.vo \
 theories/NArith/Nnat.vo	theories/NArith/Ndigits.vo \
 theories/NArith/Ndec.vo	theories/NArith/Ndist.vo 

ZARITHVO=\
 theories/ZArith/BinInt.vo      theories/ZArith/Wf_Z.vo \
 theories/ZArith/ZArith.vo      theories/ZArith/ZArith_dec.vo \
 theories/ZArith/auxiliary.vo   theories/ZArith/Zmisc.vo \
 theories/ZArith/Zcompare.vo    theories/ZArith/Znat.vo \
 theories/ZArith/Zorder.vo      theories/ZArith/Zabs.vo \
 theories/ZArith/Zmin.vo        theories/ZArith/Zmax.vo \
 theories/ZArith/Zminmax.vo     theories/ZArith/Zeven.vo \
 theories/ZArith/Zhints.vo	theories/ZArith/Zlogarithm.vo \
 theories/ZArith/Zpower.vo 	theories/ZArith/Zcomplements.vo \
 theories/ZArith/Zdiv.vo	theories/ZArith/Zsqrt.vo \
 theories/ZArith/Zwf.vo		theories/ZArith/ZArith_base.vo \
 theories/ZArith/Zbool.vo	theories/ZArith/Zbinary.vo \
 theories/ZArith/Znumtheory.vo  theories/ZArith/Int.vo \
 theories/ZArith/Zpow_def.vo

QARITHVO=\
 theories/QArith/QArith_base.vo theories/QArith/Qreduction.vo \
 theories/QArith/Qring.vo       theories/QArith/Qreals.vo \
 theories/QArith/QArith.vo	theories/QArith/Qcanon.vo 

LISTSVO=\
 theories/Lists/MonoList.vo \
 theories/Lists/ListSet.vo   	theories/Lists/Streams.vo \
 theories/Lists/TheoryList.vo   theories/Lists/List.vo \
 theories/Lists/SetoidList.vo   theories/Lists/ListTactics.vo

STRINGSVO=\
 theories/Strings/Ascii.vo      theories/Strings/String.vo

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

FSETSBASEVO=\
 theories/FSets/OrderedType.vo \
 theories/FSets/OrderedTypeEx.vo     theories/FSets/OrderedTypeAlt.vo \
 theories/FSets/FSetInterface.vo     theories/FSets/FSetList.vo \
 theories/FSets/FSetBridge.vo        theories/FSets/FSetFacts.vo \
 theories/FSets/FSetProperties.vo    theories/FSets/FSetEqProperties.vo \
 theories/FSets/FSets.vo             theories/FSets/FSetWeakProperties.vo \
 theories/FSets/FSetWeakInterface.vo theories/FSets/FSetWeakList.vo \
 theories/FSets/FSetWeakFacts.vo     theories/FSets/FSetWeak.vo \
 theories/FSets/FMapInterface.vo     theories/FSets/FMapList.vo \
 theories/FSets/FMaps.vo             theories/FSets/FMapFacts.vo \
 theories/FSets/FMapWeakFacts.vo \
 theories/FSets/FMapWeakInterface.vo theories/FSets/FMapWeakList.vo \
 theories/FSets/FMapWeak.vo          theories/FSets/FMapPositive.vo \
 theories/FSets/FMapIntMap.vo        theories/FSets/FSetToFiniteSet.vo

FSETS_basic=

FSETS_all=\
 theories/FSets/FMapAVL.vo           theories/FSets/FSetAVL.vo \

FSETSVO=$(FSETSBASEVO) $(FSETS_$(FSETS))

ALLFSETS=$(FSETSBASEVO) $(FSETS_all)

INTMAPVO=\
 theories/IntMap/Adalloc.vo    theories/IntMap/Mapcanon.vo \
 theories/IntMap/Mapfold.vo \
 theories/IntMap/Mapcard.vo    theories/IntMap/Mapc.vo \
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
 theories/Reals/Rdefinitions.vo theories/Reals/Rpow_def.vo \
 theories/Reals/Raxioms.vo      theories/Reals/RIneq.vo \
 theories/Reals/DiscrR.vo       theories/Reals/Rbase.vo \
 theories/Reals/LegacyRfield.vo

REALS_basic= 

REALS_all=\
 theories/Reals/R_Ifp.vo        theories/Reals/Rpow_def.vo \
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

SETOIDSVO=theories/Setoids/Setoid.vo

THEORIESVO =\
  $(INITVO) $(LOGICVO) $(ARITHVO) $(BOOLVO) $(NARITHVO) $(ZARITHVO) \
  $(SETOIDSVO) $(LISTSVO) $(STRINGSVO) $(SETSVO) $(FSETSVO) $(INTMAPVO) \
  $(RELATIONSVO) $(WELLFOUNDEDVO) $(REALSVO)  $(SORTINGVO) $(QARITHVO)

THEORIESLIGHTVO = $(INITVO) $(LOGICVO) $(ARITHVO)

theories: $(THEORIESVO)
theories-light: $(THEORIESLIGHTVO)

logic: $(LOGICVO)
arith: $(ARITHVO)
bool: $(BOOLVO)
narith: $(NARITHVO)
zarith: $(ZARITHVO)
qarith: $(QARITHVO)
lists: $(LISTSVO)
strings: $(STRINGSVO)
sets: $(SETSVO)
fsets: $(FSETSVO)
allfsets: $(ALLFSETS)
intmap: $(INTMAPVO)
relations: $(RELATIONSVO)
wellfounded: $(WELLFOUNDEDVO)
# reals
reals: $(REALSVO)
allreals: $(ALLREALS)
setoids: $(SETOIDSVO)
sorting: $(SORTINGVO)

noreal: logic arith bool zarith qarith lists sets fsets intmap relations \
	wellfounded setoids sorting

###########################################################################
# contribs (interface not included)
###########################################################################

OMEGAVO=\
 contrib/omega/OmegaLemmas.vo contrib/omega/Omega.vo

ROMEGAVO=\
 contrib/romega/ReflOmegaCore.vo contrib/romega/ROmega.vo 

RINGVO=\
 contrib/ring/LegacyArithRing.vo      	contrib/ring/Ring_normalize.vo \
 contrib/ring/LegacyRing_theory.vo	contrib/ring/LegacyRing.vo \
 contrib/ring/LegacyNArithRing.vo     \
 contrib/ring/LegacyZArithRing.vo	contrib/ring/Ring_abstract.vo \
 contrib/ring/Quote.vo			contrib/ring/Setoid_ring_normalize.vo \
 contrib/ring/Setoid_ring.vo		contrib/ring/Setoid_ring_theory.vo

FIELDVO=\
 contrib/field/LegacyField_Compl.vo     contrib/field/LegacyField_Theory.vo \
 contrib/field/LegacyField_Tactic.vo    contrib/field/LegacyField.vo

NEWRINGVO=\
 contrib/setoid_ring/BinList.vo   	contrib/setoid_ring/Ring_theory.vo \
 contrib/setoid_ring/Ring_polynom.vo	contrib/setoid_ring/Ring_tac.vo \
 contrib/setoid_ring/Ring_base.vo 	contrib/setoid_ring/InitialRing.vo \
 contrib/setoid_ring/Ring_equiv.vo 	contrib/setoid_ring/Ring.vo \
 contrib/setoid_ring/ArithRing.vo	contrib/setoid_ring/NArithRing.vo \
 contrib/setoid_ring/ZArithRing.vo \
 contrib/setoid_ring/Field_theory.vo	contrib/setoid_ring/Field_tac.vo \
 contrib/setoid_ring/Field.vo		contrib/setoid_ring/RealField.vo

XMLVO= 

FOURIERVO=\
 contrib/fourier/Fourier_util.vo    contrib/fourier/Fourier.vo

FUNINDVO= 

RECDEFVO=contrib/recdef/Recdef.vo

JPROVERVO= 

CCVO=

SUBTACVO=contrib/subtac/SubtacTactics.vo contrib/subtac/Heq.vo \
	contrib/subtac/Utils.vo contrib/subtac/FixSub.vo contrib/subtac/Subtac.vo \
       contrib/subtac/FunctionalExtensionality.vo

RTAUTOVO = \
 contrib/rtauto/Bintree.vo contrib/rtauto/Rtauto.vo

CONTRIBVO = $(OMEGAVO) $(ROMEGAVO) $(RINGVO) $(FIELDVO) $(XMLVO) \
	    $(FOURIERVO) $(JPROVERVO) $(CCVO) $(FUNINDVO) $(SUBTACVO) \
	    $(RTAUTOVO) $(RECDEFVO) $(NEWRINGVO)

$(CONTRIBVO): states/initial.coq

contrib: $(CONTRIBVO) $(CONTRIBCMO)
omega: $(OMEGAVO) $(OMEGACMO) $(ROMEGAVO) $(ROMEGACMO)
ring: $(RINGVO) $(RINGCMO)
setoid_ring: $(NEWRINGVO) $(NEWRINGCMO)
dp: $(DPCMO)
xml: $(XMLVO) $(XMLCMO)
extraction: $(EXTRACTIONCMO)
field: $(FIELDVO) $(FIELDCMO)
fourier: $(FOURIERVO) $(FOURIERCMO)
jprover: $(JPROVERVO) $(JPROVERCMO)
funind: $(FUNINDCMO) $(FUNINDVO)
cc: $(CCVO) $(CCCMO)
subtac: $(SUBTACVO) $(SUBTACCMO)
rtauto: $(RTAUTOVO) $(RTAUTOCMO)

ALLVO = $(INITVO) $(THEORIESVO) $(CONTRIBVO)

###########################################################################
# rules to make theories, contrib and states
###########################################################################

SYNTAXPP=syntax/PPConstr.v syntax/PPCases.v

states/initial.coq: states/MakeInitial.v $(INITVO)
	$(BOOTCOQTOP) -batch -notop -silent -nois -load-vernac-source states/MakeInitial.v -outputstate states/initial.coq

theories/Init/%.vo: $(BESTCOQTOP) theories/Init/%.v
	$(BOOTCOQTOP) -nois -compile theories/Init/$*

theories/%.vo: theories/%.v states/initial.coq
	$(BOOTCOQTOP) -compile theories/$*

contrib/%.vo: contrib/%.v
	$(BOOTCOQTOP) -compile contrib/$*

cleantheories:
	rm -f states/*.coq
	rm -f theories/*/*.vo

clean :: cleantheories

clean :: 
	rm -f contrib/*/*.cm[io] contrib/*.cma contrib/*/*.vo

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

DEBUGPRINTERS=dev/top_printers.cmo dev/vm_printers.cmo dev/printers.cma

printers: $(DEBUGPRINTERS)

tools:: $(TOOLS) $(DEBUGPRINTERS)

COQDEPCMO=config/coq_config.cmo tools/coqdep_lexer.cmo tools/coqdep.cmo

$(COQDEP): $(COQDEPCMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ unix.cma $(COQDEPCMO) $(OSDEPLIBS)

BEFOREDEPEND+= tools/coqdep_lexer.ml

GALLINACMO=tools/gallina_lexer.cmo tools/gallina.cmo

$(GALLINA): $(GALLINACMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ $(GALLINACMO)

BEFOREDEPEND+= tools/gallina_lexer.ml

COQMAKEFILECMO= config/coq_config.cmo tools/coq_makefile.cmo
$(COQMAKEFILE): $(COQMAKEFILECMO)
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ str.cma $(COQMAKEFILECMO)

$(COQTEX): tools/coq-tex.cmo
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ str.cma tools/coq-tex.cmo

BEFOREDEPEND+= tools/coqwc.ml

$(COQWC): tools/coqwc.cmo
	$(SHOW)'OCAMLC -o $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -custom -o $@ tools/coqwc.cmo

BEFOREDEPEND+= tools/coqdoc/pretty.ml tools/coqdoc/index.ml

COQDOCCMO=$(CONFIG) tools/coqdoc/cdglobals.cmo tools/coqdoc/alpha.cmo \
	tools/coqdoc/index.cmo tools/coqdoc/output.cmo \
	tools/coqdoc/pretty.cmo tools/coqdoc/main.cmo

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
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -o $@ $(CMA) $(MINICOQCMO) $(OSDEPLIBS)

archclean::
	rm -f $(MINICOQ)

###########################################################################
# Installation
###########################################################################

COQINSTALLPREFIX=
OLDROOT=

  # Can be changed for a local installation (to make packages).
  # You must NOT put a "/" at the end (Cygnus for win32 does not like "//").

FULLBINDIR=$(BINDIR:"$(OLDROOT)%="$(COQINSTALLPREFIX)%)
FULLCOQLIB=$(COQLIB:"$(OLDROOT)%="$(COQINSTALLPREFIX)%)
FULLMANDIR=$(MANDIR:"$(OLDROOT)%="$(COQINSTALLPREFIX)%)
FULLEMACSLIB=$(EMACSLIB:"$(OLDROOT)%="$(COQINSTALLPREFIX)%)
FULLCOQDOCDIR=$(COQDOCDIR:"$(OLDROOT)%="$(COQINSTALLPREFIX)%)

install-coq: install-binaries install-library install-coq-info
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
	# recopie des fichiers de style pour coqide
	$(MKDIR) $(FULLCOQLIB)/tools/coqdoc
	touch $(FULLCOQLIB)/tools/coqdoc/coqdoc.sty $(FULLCOQLIB)/tools/coqdoc/coqdoc.css # to have the mode according to umask (bug #1715)
	cp tools/coqdoc/coqdoc.css tools/coqdoc/coqdoc.sty $(FULLCOQLIB)/tools/coqdoc
	cp $(TOOLS) $(FULLBINDIR)

LIBFILES=$(THEORIESVO) $(CONTRIBVO)
LIBFILESLIGHT=$(THEORIESLIGHTVO)


GRAMMARCMA=parsing/grammar.cma
OBJECTCMA=lib/lib.cma kernel/kernel.cma library/library.cma \
        pretyping/pretyping.cma interp/interp.cma proofs/proofs.cma \
        parsing/parsing.cma tactics/tactics.cma toplevel/toplevel.cma \
        parsing/highparsing.cma tactics/hightactics.cma contrib/contrib.cma

OBJECTCMI=$(OBJSCMO:.cmo=.cmi)

OBJECTCMXA=$(OBJECTCMA:.cma=.cmxa)

install-library:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(LIBFILES); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states
	cp states/*.coq $(FULLCOQLIB)/states
	$(MKDIR) $(FULLCOQLIB)/user-contrib
	cp $(LIBCOQRUN) $(FULLCOQLIB)
	cp --parents $(CONFIG) $(OBJECTCMI) $(LINKCMO) $(GRAMMARCMA) $(FULLCOQLIB)
ifeq ($(BEST),opt)
	cp --parents $(CONFIG:.cmo=.cmx) $(CONFIG:.cmo=.o) $(LINKCMO:.cma=.cmxa) $(LINKCMO:.cma=.a) $(FULLCOQLIB)
endif

install-library-light:
	$(MKDIR) $(FULLCOQLIB)
	for f in $(LIBFILESLIGHT); do \
	  $(MKDIR) $(FULLCOQLIB)/`dirname $$f`; \
	  cp $$f $(FULLCOQLIB)/`dirname $$f`; \
        done
	$(MKDIR) $(FULLCOQLIB)/states
	cp states/*.coq $(FULLCOQLIB)/states

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

doc: glob.dump
	(cd doc; $(MAKE) all)

clean::
	(cd doc; $(MAKE) clean)

clean::
	rm -f doc/coq.tex

###########################################################################
# Documentation of the source code (using ocamldoc)
###########################################################################

SOURCEDOCDIR=dev/source-doc

.PHONY: source-doc

source-doc:
	if !(test -d $(SOURCEDOCDIR)); then mkdir $(SOURCEDOCDIR); fi
	$(OCAMLDOC) -html -rectypes $(LOCALINCLUDES) -d $(SOURCEDOCDIR) `find . -name "*.ml"`

clean::
	rm -rf $(SOURCEDOCDIR)




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

ML4FILES += parsing/lexer.ml4 parsing/pcoq.ml4 parsing/q_util.ml4 \
  parsing/q_coqast.ml4 parsing/g_prim.ml4 

GRAMMARNEEDEDCMO=\
  lib/pp_control.cmo lib/pp.cmo lib/compat.cmo lib/util.cmo lib/bigint.cmo \
  lib/dyn.cmo lib/options.cmo lib/hashcons.cmo lib/predicate.cmo \
  lib/rtree.cmo \
  kernel/names.cmo kernel/univ.cmo \
  kernel/esubst.cmo kernel/term.cmo kernel/mod_subst.cmo kernel/sign.cmo \
  kernel/cbytecodes.cmo kernel/copcodes.cmo kernel/cemitcodes.cmo \
  kernel/declarations.cmo kernel/pre_env.cmo \
  kernel/cbytegen.cmo kernel/conv_oracle.cmo kernel/environ.cmo \
  kernel/closure.cmo kernel/reduction.cmo kernel/type_errors.cmo\
  kernel/entries.cmo \
  kernel/modops.cmo \
  kernel/inductive.cmo kernel/typeops.cmo \
  kernel/indtypes.cmo kernel/cooking.cmo kernel/term_typing.cmo \
  kernel/subtyping.cmo kernel/mod_typing.cmo kernel/safe_typing.cmo \
  library/nameops.cmo library/libnames.cmo library/summary.cmo \
  library/nametab.cmo library/libobject.cmo library/lib.cmo \
  library/goptions.cmo library/decl_kinds.cmo library/global.cmo \
  pretyping/termops.cmo pretyping/evd.cmo pretyping/reductionops.cmo \
  pretyping/inductiveops.cmo pretyping/rawterm.cmo pretyping/detyping.cmo \
  pretyping/pattern.cmo \
  interp/topconstr.cmo interp/genarg.cmo interp/ppextend.cmo \
  proofs/tacexpr.cmo \
  parsing/lexer.cmo parsing/extend.cmo \
  toplevel/vernacexpr.cmo parsing/pcoq.cmo parsing/q_util.cmo \
  parsing/q_coqast.cmo 

CAMLP4EXTENSIONSCMO=\
  parsing/argextend.cmo parsing/tacextend.cmo parsing/vernacextend.cmo 

GRAMMARSCMO=\
  parsing/g_prim.cmo parsing/g_tactic.cmo \
  parsing/g_ltac.cmo parsing/g_constr.cmo

GRAMMARCMO=$(GRAMMARNEEDEDCMO) $(CAMLP4EXTENSIONSCMO) $(GRAMMARSCMO)

PRINTERSCMO=\
  config/coq_config.cmo lib/lib.cma \
  kernel/names.cmo kernel/univ.cmo kernel/esubst.cmo kernel/term.cmo	\
  kernel/mod_subst.cmo kernel/copcodes.cmo kernel/cemitcodes.cmo	\
  kernel/sign.cmo kernel/declarations.cmo kernel/pre_env.cmo \
  kernel/cbytecodes.cmo kernel/cbytegen.cmo kernel/environ.cmo \
  kernel/conv_oracle.cmo kernel/closure.cmo kernel/reduction.cmo	\
  kernel/modops.cmo kernel/type_errors.cmo kernel/inductive.cmo		\
  kernel/typeops.cmo kernel/subtyping.cmo kernel/indtypes.cmo		\
  kernel/cooking.cmo 		\
  kernel/term_typing.cmo kernel/mod_typing.cmo kernel/safe_typing.cmo	\
  library/summary.cmo library/global.cmo library/nameops.cmo		\
  library/libnames.cmo library/nametab.cmo library/libobject.cmo	\
  library/lib.cmo library/goptions.cmo \
  pretyping/termops.cmo pretyping/evd.cmo				    \
  pretyping/rawterm.cmo pretyping/termops.cmo pretyping/evd.cmo		    \
  pretyping/reductionops.cmo pretyping/inductiveops.cmo			    \
  pretyping/retyping.cmo pretyping/cbv.cmo				    \
  pretyping/pretype_errors.cmo pretyping/recordops.cmo pretyping/typing.cmo \
  pretyping/evarutil.cmo pretyping/unification.cmo pretyping/evarconv.cmo   \
  pretyping/tacred.cmo pretyping/classops.cmo pretyping/detyping.cmo	    \
  pretyping/indrec.cmo pretyping/coercion.cmo pretyping/cases.cmo	    \
  pretyping/pretyping.cmo pretyping/clenv.cmo pretyping/pattern.cmo \
  parsing/lexer.cmo interp/ppextend.cmo interp/genarg.cmo \
  interp/topconstr.cmo interp/notation.cmo interp/reserve.cmo		\
  library/impargs.cmo\
  interp/constrextern.cmo interp/syntax_def.cmo interp/constrintern.cmo	\
  proofs/proof_trees.cmo proofs/logic.cmo proofs/refiner.cmo \
  proofs/tacexpr.cmo \
  proofs/evar_refiner.cmo proofs/pfedit.cmo proofs/tactic_debug.cmo \
  proofs/decl_mode.cmo \
  parsing/ppconstr.cmo parsing/extend.cmo parsing/pcoq.cmo \
  parsing/printer.cmo parsing/pptactic.cmo \
  parsing/ppdecl_proof.cmo \
  parsing/tactic_printer.cmo \
  parsing/egrammar.cmo toplevel/himsg.cmo \
  toplevel/cerrors.cmo toplevel/vernacexpr.cmo toplevel/vernacinterp.cmo \
  dev/top_printers.cmo

dev/printers.cma: $(PRINTERSCMO)
	$(SHOW)'Testing $@'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) gramlib.cma $(PRINTERSCMO) -o test-printer
	@rm -f test-printer
	$(SHOW)'OCAMLC -a $@'   
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) $(PRINTERSCMO) -linkall -a -o $@

parsing/grammar.cma: $(GRAMMARCMO)
	$(SHOW)'Testing $@'
	@touch test.ml4
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) $(GRAMMARCMO) -impl" -impl test.ml4 -o test-grammar
	@rm -f test-grammar test.*
	$(SHOW)'OCAMLC -a $@'   
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) $(GRAMMARCMO) -linkall -a -o $@

clean::
	rm -f parsing/grammar.cma

ML4FILES +=parsing/g_minicoq.ml4 \
	   parsing/g_vernac.ml4 parsing/g_proofs.ml4 \
	   parsing/g_xml.ml4 parsing/g_constr.ml4 \
	   parsing/g_tactic.ml4 parsing/g_ltac.ml4 \
	   parsing/argextend.ml4 parsing/tacextend.ml4 \
	   parsing/vernacextend.ml4 parsing/q_constr.ml4 \
	   parsing/g_decl_mode.ml4


BEFOREDEPEND+= $(GRAMMARCMO)

# BEFOREDEPEND+= parsing/pcoq.ml parsing/extend.ml

# File using pa_macro and only necessary for parsing ml files

parsing/q_coqast.cmo: parsing/q_coqast.ml4
	$(SHOW)'OCAMLC4  $<' 
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) $(CAMLP4OPTIONS) -impl" -c -impl $<

# toplevel/mltop.ml4 (ifdef Byte)

toplevel/mltop.cmo: toplevel/mltop.byteml
	$(SHOW)'OCAMLC    $<'	
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -c -impl $< -o $@

toplevel/mltop.cmx: toplevel/mltop.optml
	$(SHOW)'OCAMLOPT  $<'	
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -c -impl $< -o $@

toplevel/mltop.byteml: toplevel/mltop.ml4
	$(SHOW)'CAMLP4O   $<'	
	$(HIDE)$(CAMLP4O) $(CAMLP4EXTENSIONS) pr_o.cmo -DByte -impl $< > $@ || rm -f $@

toplevel/mltop.optml: toplevel/mltop.ml4
	$(SHOW)'CAMLP4O   $<'	
	$(HIDE)$(CAMLP4O) $(CAMLP4EXTENSIONS) pr_o.cmo -impl $< > $@ || rm -f $@

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

parsing/pptactic.cmo: parsing/pptactic.ml
	$(SHOW)'OCAMLC    -rectypes $<'
	$(HIDE)$(OCAMLC) -rectypes $(BYTEFLAGS) -c $<

parsing/pptactic.cmx: parsing/pptactic.ml
	$(SHOW)'OCAMLOPT    -rectypes $<'
	$(HIDE)$(OCAMLOPT) -rectypes $(OPTFLAGS) -c $<

ML4FILES += lib/pp.ml4 lib/compat.ml4

lib/compat.cmo: lib/compat.ml4
	$(SHOW)'OCAMLC4  $<' 
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) $(CAMLP4OPTIONS) -impl" -c -impl $<

lib/compat.cmx: lib/compat.ml4
	$(SHOW)'OCAMLOPT  $<' 
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) $(CAMLP4OPTIONS) -impl" -c -impl $<

# files compiled with camlp4 because of streams syntax

ML4FILES += contrib/xml/xml.ml4		\
	 contrib/xml/acic2Xml.ml4	\
	 contrib/xml/proofTree2Xml.ml4	\
	 contrib/interface/line_parser.ml4	\
	 tools/coq_makefile.ml4		\
	 tools/coq-tex.ml4

# Add pr_o.cmo to circumvent a useless-warning bug when preprocessed with
# ast-based camlp4

parsing/lexer.cmx: parsing/lexer.ml4
	$(SHOW)'OCAMLOPT4 $<'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) pr_o.cmo `$(CAMLP4DEPS) $<` -impl" -c -impl $<

parsing/lexer.cmo: parsing/lexer.ml4
	$(SHOW)'OCAMLC4   $<'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) pr_o.cmo `$(CAMLP4DEPS) $<` -impl" -c -impl $<

# pretty printing of the revision number when compiling a checked out
# source tree
.PHONY: revision

revision:
ifeq ($(CHECKEDOUT),1)
	- /bin/rm -f revision
	sed -ne '/url/s/^.*\/\([^\/"]\{1,\}\)"$$/\1/p' .svn/entries > revision
	sed -ne '/revision/s/^.*"\([0-9]\{1,\}\)".*$$/r\1/p' .svn/entries >> revision
endif

archclean::
	/bin/rm -f revision


###########################################################################
# Default rules
###########################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly .ml4 .v .vo .el .elc .h .c .o

.c.o:
	$(CC) -o $@ $(CFLAGS) $(CINCLUDES)  -c $<

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
	$(HIDE)$(OCAMLLEX) $<

.mly.ml:
	$(SHOW)'OCAMLYACC $<'
	$(HIDE)$(OCAMLYACC) $<

.mly.mli:
	$(SHOW)'OCAMLYACC $<'
	$(HIDE)$(OCAMLYACC) $<

.ml4.cmx:
	$(SHOW)'OCAMLOPT4 $<'
	$(HIDE)$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) `$(CAMLP4DEPS) $<` $(CAMLP4OPTIONS) -impl" -c -impl $<

.ml4.cmo:
	$(SHOW)'OCAMLC4   $<'
	$(HIDE)$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENSIONS) `$(CAMLP4DEPS) $<` $(CAMLP4OPTIONS) -impl" -c -impl $<

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
	rm -f kernel/byterun/*.o
	rm -f kernel/byterun/libcoqrun.a
	rm -f library/*.cmx* library/*.[soa]
	rm -f proofs/*.cmx* proofs/*.[soa]
	rm -f tactics/*.cmx* tactics/*.[soa]
	rm -f interp/*.cmx* interp/*.[soa]
	rm -f parsing/*.cmx* parsing/*.[soa]
	rm -f pretyping/*.cmx* pretyping/*.[soa]
	rm -f toplevel/*.cmx* toplevel/*.[soa]
	rm -f ide/*.cmx* ide/*.[soa]
	rm -f ide/utils/*.cmx* ide/utils/*.[soa]
	rm -f tools/*.cmx* tools/*.[soa]
	rm -f tools/*/*.cmx* tools/*/*.[soa]
	rm -f scripts/*.cmx* scripts/*.[soa]
	rm -f dev/*.cmx* dev/*.[soa]

clean:: archclean
	rm -f *~ */*~ */*/*~
	rm -f gmon.out core
	rm -f config/*.cm[ioa] config/*.annot
	rm -f lib/*.cm[ioa] lib/*.annot
	rm -f kernel/*.cm[ioa] kernel/*.annot
	rm -f library/*.cm[ioa] library/*.annot
	rm -f proofs/*.cm[ioa] proofs/*.annot
	rm -f tactics/*.cm[ioa] tactics/*.annot
	rm -f interp/*.cm[ioa] interp/*.annot
	rm -f parsing/*.cm[ioa] parsing/*.ppo parsing/*.annot
	rm -f pretyping/*.cm[ioa] pretyping/*.annot
	rm -f toplevel/*.cm[ioa] toplevel/*.annot
	rm -f ide/*.cm[ioa] ide/*.annot
	rm -f ide/utils/*.cm[ioa] ide/utils/*.annot
	rm -f tools/*.cm[ioa] tools/*.annot
	rm -f tools/*/*.cm[ioa] tools/*/*.annot
	rm -f scripts/*.cm[ioa] scripts/*.annot
	rm -f dev/*.cm[ioa] dev/*.annot
	rm -f */*.pp[iox] contrib/*/*.pp[iox]

cleanconfig::
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-v7

###########################################################################
# Dependencies
###########################################################################

.PHONY: alldepend dependcoq scratchdepend

alldepend: depend dependcoq 

dependcoq: $(BEFOREDEPEND) $(COQDEP)
	$(COQDEP) -slash -coqlib . -R theories Coq -R contrib Coq $(COQINCLUDES) \
	 $(ALLFSETS:.vo=.v) $(ALLREALS:.vo=.v) $(ALLVO:.vo=.v) > .depend.coq

# Build dependencies ignoring failures in building ml files from ml4 files
# This is useful to rebuild dependencies when they are strongly corrupted:
# by making scratchdepend, one gets dependencies OK for .ml files and
# .ml4 files not using fancy parsers. This is sufficient to get beforedepend
# and depend targets successfully built
scratchdepend: dependp4
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
	-$(MAKE) -k -f Makefile.dep $(ML4FILESML)
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
	$(MAKE) depend


# Computing the dependencies in camlp4 files is tricky.
# We proceed in several steps:

ML4FILESML = $(ML4FILES:.ml4=.ml)

# Expresses dependencies of the .ml4 files w.r.t their grammars

.PHONY: dependp4
dependp4: 
	rm -f .depend.camlp4
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".ml: " >> .depend.camlp4; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend.camlp4; \
	done

# Produce the .ml files using Makefile.dep
.PHONY: ml4filesml
ml4filesml:: .depend.camlp4 parsing/grammar.cma
	$(MAKE) -f Makefile.dep $(ML4FILESML)


.PHONY: depend
depend: dependp4 ml4filesml $(BEFOREDEPEND)
# 1. We express dependencies of the .ml files w.r.t their grammars
# 2. Then we are able to produce the .ml files using Makefile.dep
# 3. We compute the dependencies inside the .ml files using ocamldep
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
# 4. We express dependencies of .cmo and .cmx files w.r.t their grammars
	for f in $(ML4FILES); do \
	  bn=`dirname $$f`/`basename $$f .ml4`; \
	  deps=`$(CAMLP4DEPS) $$f`; \
	  if [ -n "$${deps}" ]; then \
	    /bin/mv -f .depend .depend.tmp; \
	    sed -e "\|^$${bn}.cmo|s|^$${bn}.cmo: \(.*\)$$|$${bn}.cmo: $${deps} \1|" \
	        -e "\|^$${bn}.cmx|s|^$${bn}.cmx: \(.*\)$$|$${bn}.cmx: $${deps} \1|" \
	        .depend.tmp > .depend; \
	    /bin/rm -f .depend.tmp; \
	  fi; \
	done
# 5.  We express dependencies of .o files
	$(CC) -MM -isystem $(CAMLHLIB) kernel/byterun/*.c >> .depend
# 6. Finally, we erase the generated .ml files
	rm -f $(ML4FILESML)
#    and the .cmo and .cmi files needed by grammar.cma
	rm -f rm parsing/*.cm[io] lib/pp.cm[io] lib/compat.cm[io]
# 7. Since .depend contains correct dependencies .depend.devel can be deleted
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
	$(MAKE) $(DEBUGPRINTERS)

-include .depend
-include .depend.coq

clean::
	find . -name "\.#*" -exec rm -f {} \;

###########################################################################
