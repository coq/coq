# Installing with Dune

The build and installation procedure using Dune is quite
straightforward. We recommend you read Dune's user manual for
questions, as Coq mostly implements a standard build workflow.

## Quick Installation Procedure [Dune].
=======================================

1. COQ_CONFIGURE_PREFIX=$prefix make release
2. dune install [--prefix=$prefix] coq

If you don't pass the prefix argument to `dune install` it will choose
your default OCaml library path.

## Developer setup.
===================

For more information about the Dune build system just type `make`, you
can also read `dev/doc/build-system.dune.md`
