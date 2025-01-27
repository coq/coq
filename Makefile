##########################################################################
##         #      The Rocq Prover / The Rocq Development Team           ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################

# Dune Makefile for Rocq

.PHONY: help help-install states world rocqide watch check    # Main developer targets
.PHONY: refman-html refman-pdf corelib-html apidoc     # Documentation targets
.PHONY: test-suite dev-targets
.PHONY: fmt ocheck obuild ireport clean               # Maintenance targets
.PHONY: dunestrap release install                 # Miscellaneous

# We don't allow parallel build here, this is just a placehoder for
# dune commands for the most part
.NOTPARALLEL:

###########################################################################
# The SHOW and HIDE variables control whether make will echo complete commands
# or only abbreviated versions.
# Quiet mode is ON by default except if VERBOSE=1 option is given to make
# Used only by targets which don't go through dune (eg doc_gram_rsts)

VERBOSE ?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

# use DUNEOPT=--display=short for a more verbose build
# DUNEOPT=--display=short

help:
	@echo ""
	@echo "Welcome to Rocq's Dune-based build system. If you are final user type"
	@echo "make help-install for installation instructions. Common developer targets are:"
	@echo ""
	@echo "  - states: build a minimal functional rocq repl"
	@echo "  - world:  build main public binaries and libraries in developer mode (no rocqide)"
	@echo "  - watch:  build main public binaries and libraries [continuous build]"
	@echo "  - rocqide: build rocqide binary in developer mode"
	@echo "  - check:  build all ML files as fast as possible"
	@echo "  - test-suite: run Rocq's test suite [env NJOBS=N to set job parallelism]"
	@echo "  - dunestrap: Generate the dune rules for vo files"
	@echo ""
	@echo "  Note: running ./configure is not recommended for developers,"
	@echo "        see dev/doc/build-system.dune.md for more info"
	@echo "  Note: these targets produce a developer build, not suitable"
	@echo "        for distribution to end-users or install"
	@echo ""
	@echo " To run an \$$app \\in {coqc,coqtop,coqtop.byte,rocqide}:"
	@echo ""
	@echo "  - use 'dune exec -- dev/shim/\$$app args'"
	@echo "    Example: 'dune exec -- dev/shim/coqc file.v'"
	@echo ""
	@echo " Documentation targets:"
	@echo ""
	@echo "  - refman-html: build Rocq's reference manual [HTML version]"
	@echo "  - refman-pdf:  build Rocq's reference manual [PDF version]"
	@echo "  - corelib-html: build Rocq's Corelib documentation [HTML version]"
	@echo "  - apidoc:      build ML API documentation"
	@echo ""
	@echo " Miscellaneous targets:"
	@echo ""
	@echo "  - fmt:     run ocamlformat on the codebase"
	@echo "  - ocheck:  check for a selection of supported OCaml versions [requires OPAM]"
	@echo "  - obuild:  build for a selection of supported OCaml versions [requires OPAM]"
	@echo "  - ireport: build with optimized flambda settings and emit an inline report"
	@echo "  - clean:   remove build directory and autogenerated files"
	@echo "  - help:    show this message"
	@echo ""
	@echo " Type 'make help-install' for installation instructions"
	@echo " Type 'make dev-targets' for more developer targets"

dev-targets:
	@echo ""
	@echo "In order to get a functional Rocq install layout, the world target is required."
	@echo "However, This is often inconvenient for developers, due to the large amount of"
	@echo "files that world will build. We provide some useful subtargets here:"
	@echo ""
	@echo "  - theories-foo: for each directory theories/Foo, build the vo files for it and set them up in _build/install/default."
	@echo "    For instance the init target builds the prelude, combined with rocq-runtime.install it produces a fully functional layout in _build/install/default."

help-install:
	@echo ""
	@echo "The Dune-based Rocq build is split into several packages; see Dune and dev/doc"
	@echo "documentation for more details. A quick install of Rocq alone can be done with"
	@echo ""
	@echo " $$ make dunestrap"
	@echo " $$ dune build -p rocq-runtime,coq-core,rocq-core"
	@echo " $$ dune install --prefix=<install_prefix> rocq-runtime coq-core rocq-core"
	@echo ""
	@echo " Provided opam/dune packages are:"
	@echo ""
	@echo "  - rocq-runtime: base Rocq package, toplevel compilers, plugins, tools, no corelib, no stdlib, no GTK"
	@echo "  - coq-core: compat binaries (coqc instead of rocq compile, etc)"
	@echo "  - rocq-core: Rocq's prelude and corelib"
	@echo "  - coqide-server: XML protocol language server"
	@echo "  - rocqide: RocqIDE gtk application"
	@echo "  - rocq: meta package depending on rocq-runtime rocq-core rocq-stdlib"
	@echo "    (also calls the test suite when using --with-test)"
	@echo "  - coq: meta package depending on rocq coq-core coq-stdlib"
	@echo "    (also calls the test suite when using --with-test)"
	@echo ""
	@echo " To build a package, you can use:"
	@echo ""
	@echo "  - 'dune build package.install' : build package in developer mode"
	@echo "  - 'dune build -p package' : build package in release mode"
	@echo ""
	@echo " Packages _must_ be installed only if built using release mode, to install a package use: "
	@echo ""
	@echo "  - 'dune install --prefix=<install_prefix> package'"
	@echo ""
	@echo " Note that '--prefix' must be passed to dune install. The '-prefix' passed to"
	@echo " configure tells Rocq where to look for libraries."
	@echo ""
	@echo " Note that building a package in release mode ignores other packages present in"
	@echo " the worktree. See Dune documentation for more information."

# We setup the root even in dev mode, to avoid some problems.  We used
# this in the past to workaround a bug in opam, but the bug was that
# we didn't pass `-p` to the dune build below.
#
# This would be fixed once dune can directly use `(include
# theories_dune)` in our files.
DUNESTRAPOPT=--root .

# We regenerate always as to correctly track deps, can do better
# We do a single call to dune as to avoid races and locking
ifneq ($(COQ_SPLIT),) # avoid depending on local rocq-runtime
_build/default/theories_dune_split _build/default/ltac2_dune_split .dune-stamp:
	dune build $(DUNEOPT) $(DUNESTRAPOPT) theories_dune_split ltac2_dune_split
	touch .dune-stamp

theories/dune: .dune-stamp
	cp -a _build/default/theories_dune_split $@ && chmod +w $@

user-contrib/Ltac2/dune: .dune-stamp
	cp -a _build/default/ltac2_dune_split $@ && chmod +w $@
else
_build/default/theories_dune _build/default/ltac2_dune .dune-stamp:
	dune build $(DUNEOPT) $(DUNESTRAPOPT) theories_dune ltac2_dune
	touch .dune-stamp

theories/dune: .dune-stamp
	cp -a _build/default/theories_dune $@ && chmod +w $@

user-contrib/Ltac2/dune: .dune-stamp
	cp -a _build/default/ltac2_dune $@ && chmod +w $@
endif

.PHONY: .dune-stamp

DUNE_FILES=theories/dune user-contrib/Ltac2/dune

dunestrap-generated: $(DUNE_FILES)

dunestrap: ;

states: dunestrap
	dune build $(DUNEOPT) dev/shim/coqtop

MAIN_TARGETS:=rocq-runtime.install coq-core.install rocq-core.install \
  coqide-server.install rocq-devtools.install

world: dunestrap
	dune build $(DUNEOPT) $(MAIN_TARGETS)

rocqide:
	dune build $(DUNEOPT) rocqide.install

watch:
	dune build $(DUNEOPT) $(MAIN_TARGETS) -w

check:
	dune build $(DUNEOPT) @check

test-suite: dunestrap
	dune runtest --no-buffer $(DUNEOPT)

refman-html: dunestrap
	dune build --no-buffer @refman-html

refman-pdf: dunestrap
	dune build --no-buffer @refman-pdf

corelib-html: dunestrap
	dune build @corelib-html

apidoc:
	dune build $(DUNEOPT) @doc

release: theories/dune
	@echo "release target is deprecated, use dune directly"
	dune build $(DUNEOPT) -p coq

# We define this target as to override Make's built-in one
install:
	@echo "To install Rocq using dune, use 'dune build -p P && dune install P'"
	@echo "where P is any of the packages defined by opam files in the root dir"
	@false

fmt:
	dune build @fmt --auto-promote

ocheck:
	dune build $(DUNEOPT) @check --workspace=dev/dune-workspace.all

obuild: dunestrap
	dune build $(DUNEOPT) @default --workspace=dev/dune-workspace.all

ireport:
	dune clean
	dune build $(DUNEOPT) @install --profile=ireport

clean:
	dune clean

# docgram

DOC_GRAM:=_build/default/doc/tools/docgram/doc_grammar.exe

# not worth figuring out dependencies, just leave it to dune
.PHONY: $(DOC_GRAM)
$(DOC_GRAM):
	dune build $(DUNEOPT) $@

include doc/Makefile.docgram

# This requires a install layout to be available.

CONTEXT=_build/install/default

# XXX: Port this to a dune alias so the build is hygienic!
.PHONY: plugin-tutorial
plugin-tutorial: dunestrap
	dune build $(CONTEXT)/lib/rocq-runtime/META $(CONTEXT)/lib/coq-core/META rocq-runtime.install coq-core.install theories/Init/Prelude.vo
	+$(MAKE) OCAMLPATH=$(shell pwd)/$(CONTEXT)/lib/ COQBIN=$(shell pwd)/$(CONTEXT)/bin/ ROCQRUNTIMELIB=$(shell pwd)/$(CONTEXT)/lib/rocq-runtime ROCQLIB=$(shell pwd)/_build/default/ -C doc/plugin_tutorial

# This is broken in a very weird way with a permission error... see
# the rule in doc/plugin_tutorial/dune:

# plugin-tutorial: dunestrap
#	dune build @plugin-tutorial

# ci-* targets

CI_PURE_DUNE:=1
export CI_PURE_DUNE
include Makefile.ci

# Custom targets to create subsets of the world target but with less
# compiled files. This is desired when we want to have our Rocq Dune
# build with Rocq developments that are not dunerized and thus still
# expect an install layout with a working Rocq setup, but smaller than
# world.
#
# Unfortunately, Dune still lacks the capability to refer to install
# targets in rules, see https://github.com/ocaml/dune/issues/3192 ;
# thus we can't simply yet use `%{pkg:coq:theories/Arith/Arith.vo` to
# have the rule install the target, we thus imitate such behavior
# using make as a helper.

# $(1) is the directory (theories/Foo/)
# $(2) is the name (foo)
define subtarget =
  .PHONY: theories-$(2)

  $(2)_FILES=$$(wildcard $(1)*.v)
  $(2)_FILES_PATH=$$(addprefix _build/install/default/lib/coq/, $$($(2)_FILES:.v=.vo))

  theories-$(2):
	@echo "DUNE $(1)*.vo"
	@dune build $$($(2)_FILES_PATH)
endef

$(foreach subdir,$(wildcard theories/*/),$(eval $(call subtarget,$(subdir),$(shell echo $(subst /,,$(subst theories/,,$(subdir))) | tr A-Z a-z))))

# Other common dev targets:
#
# dune build rocq-runtime.install
# dune build coq.install
# dune build rocqide.install
#
# Packaging / OPAM targets:
#
# dune -p coq @install
# dune -p rocqide @install
