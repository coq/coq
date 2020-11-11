##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################

# Dune Makefile for Coq

.PHONY: help help-install states world watch check    # Main developer targets
.PHONY: refman-html refman-pdf stdlib-html apidoc     # Documentation targets
.PHONY: test test-suite dev-targets
.PHONY: fmt ocheck obuild ireport clean               # Maintenance targets
.PHONY: dunestrap vio release install                 # Miscellaneous

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
	@echo "Welcome to Coq's Dune-based build system. If you are final user type"
	@echo "make help-install for installation instructions. Common developer targets are:"
	@echo ""
	@echo "  - states: build a minimal functional coqtop"
	@echo "  - world:  build all public binaries and libraries in developer mode"
	@echo "  - watch:  build all public binaries and libraries [continuous build]"
	@echo "  - check:  build all ML files as fast as possible"
	@echo "  - test-suite: run Coq's test suite [env NJOBS=N to set job parallelism]"
	@echo "  - dunestrap: Generate the dune rules for vo files"
	@echo ""
	@echo "  use 'COQ_DUNE_EXTRA_OPT=\"-vio\" make target' to do a vio build"
	@echo ""
	@echo "  Note: running ./configure is not recommended for developers,"
	@echo "        see dev/doc/build-system.dune.md for more info"
	@echo "  Note: these targets produce a developer build, not suitable"
	@echo "        for distribution to end-users or install"
	@echo ""
	@echo " To run an \$$app \\in {coqc,coqtop,coqbyte,coqide}:"
	@echo ""
	@echo "  - use 'dune exec -- dev/shim/\$$app-prelude args'"
	@echo "    Example: 'dune exec -- dev/shim/coqc-prelude file.v'"
	@echo ""
	@echo " Documentation targets:"
	@echo ""
	@echo "  - refman-html: build Coq's reference manual [HTML version]"
	@echo "  - refman-pdf:  build Coq's reference manual [PDF version]"
	@echo "  - stdlib-html: build Coq's Stdlib documentation [HTML version]"
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
	@echo "In order to get a functional Coq install layout, the world target is required."
	@echo "However, This is often inconvenient for developers, due to the large amount of"
	@echo "files that world will build. We provide some useful subtargets here:"
	@echo ""
	@echo "  - theories-foo: for each directory theories/Foo, build the vo files for it and set them up in _build/install/default."
	@echo "    For instance the init target builds the prelude, combined with coq-core.install it produces a fully functional layout in _build/install/default."

help-install:
	@echo ""
	@echo "The Dune-based Coq build is split in packages; see Dune and dev/doc"
	@echo "documentation for more details. A quick install of Coq alone can done with"
	@echo ""
	@echo " $ ./configure -prefix <install_prefix>"
	@echo " $ make dunestrap"
	@echo " $ dune build -p coq-core,coq-stdlib && dune install coq-core coq-stdlib"
	@echo ""
	@echo " Provided opam/dune packages are:"
	@echo ""
	@echo "  - coq-core: base Coq package, toplevel compilers, plugins, tools, no stdlib, no GTK"
	@echo "  - coq-stdlib: Coq's standard library"
	@echo "  - coqide-server: XML protocol language server"
	@echo "  - coqide: CoqIDE gtk application"
	@echo "  - coq: meta package depending on coq-core coq-stdlib"
	@echo ""
	@echo " To build a package, you can use:"
	@echo ""
	@echo "  - 'dune build package.install' : build package in developer mode"
	@echo "  - 'dune build -p package' : build package in release mode"
	@echo ""
	@echo " Packages _must_ be installed only if built using release mode, to install a package use: "
	@echo ""
	@echo "  - 'dune install $install_opts package'"
	@echo ""
	@echo " Note that -prefix must be passed to dune install, prefix used in configure will tell Coq"
	@echo " where to look for libraries."
	@echo ""
	@echo " Note that building a package in release mode ignores other packages present in"
	@echo " the worktree. See Dune documentation for more information."

# We regenerate always as to correctly track deps, can do better
# We do a single call to dune as to avoid races and locking
_build/default/theories_dune _build/default/ltac2_dune .dune-stamp: FORCE touch-tests
	dune build $(DUNEOPT) --root . theories_dune ltac2_dune
	touch .dune-stamp

touch-tests:
	touch test-suite/test_suite_rules.sexp
	touch test-suite/unit-tests/utest_rules.sexp

theories/dune: .dune-stamp
	cp -a _build/default/theories_dune $@ && chmod +w $@

user-contrib/Ltac2/dune: .dune-stamp
	cp -a _build/default/ltac2_dune $@ && chmod +w $@

FORCE: ;

DUNE_FILES=theories/dune user-contrib/Ltac2/dune

dunestrap: $(DUNE_FILES)

states: dunestrap
	dune build $(DUNEOPT) dev/shim/coqtop-prelude

NONDOC_INSTALL_TARGETS:=coq-core.install coq-stdlib.install coqide-server.install coqide.install coq.install

world: dunestrap
	dune build $(DUNEOPT) $(NONDOC_INSTALL_TARGETS)

# only useful for CI
vio: dunestrap
	dune build $(DUNEOPT) @vio

watch: dunestrap
	dune build $(DUNEOPT) $(NONDOC_INSTALL_TARGETS) -w

check: dunestrap
	dune build $(DUNEOPT) @check

test-gen: dunestrap
	dune build $(DUNEOPT) @test-gen

test test-suite: test-gen
	dune test $(DUNEOPT)

watch-test: dunestrap
	dune build $(DUNEOPT) @runtest -w

refman-html: dunestrap
	dune build --no-buffer @refman-html

refman-pdf: dunestrap
	dune build --no-buffer @refman-pdf

stdlib-html: dunestrap
	dune build @stdlib-html

apidoc: dunestrap
	dune build $(DUNEOPT) @doc

release: theories/dune
	@echo "release target is deprecated, use dune directly"
	dune build $(DUNEOPT) -p coq

# We define this target as to override Make's built-in one
install:
	@echo "To install Coq using dune, use 'dune build -p P && dune install P'"
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
	rm -f .dune-stamp
	dune clean

# docgram

DOC_GRAM:=_build/default/doc/tools/docgram/doc_grammar.exe

# not worth figuring out dependencies, just leave it to dune
.PHONY: $(DOC_GRAM)
$(DOC_GRAM): dunestrap
	dune build $(DUNEOPT) $@

include doc/Makefile.docgram

# This requires a install layout to be available.

CONTEXT=_build/install/default

# XXX: Port this to a dune alias so the build is hygienic!
.PHONY: plugin-tutorial
plugin-tutorial: dunestrap
	dune build $(CONTEXT)/lib/coq-core/META coq-core.install theories/Init/Prelude.vo
	+$(MAKE) OCAMLPATH=$(shell pwd)/$(CONTEXT)/lib/ COQBIN=$(shell pwd)/$(CONTEXT)/bin/ COQCORELIB=$(shell pwd)/$(CONTEXT)/lib/coq-core COQLIB=$(shell pwd)/_build/default/ -C doc/plugin_tutorial

# This is broken in a very weird way with a permission error... see
# the rule in doc/plugin_tutorial/dune:

# plugin-tutorial: dunestrap
#	dune build @plugin-tutorial

# ci-* targets

CI_PURE_DUNE:=1
export CI_PURE_DUNE
include Makefile.ci

# Custom targets to create subsets of the world target but with less
# compiled files. This is desired when we want to have our Coq Dune
# build with Coq developments that are not dunerized and thus still
# expect an install layout with a working Coq setup, but smaller than
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
# dune build coq-core.install
# dune build coq.install
# dune build coqide.install
#
# Packaging / OPAM targets:
#
# dune -p coq @install
# dune -p coqide @install
