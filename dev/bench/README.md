# Rocq Bench Scripts

## Path and Global Environment Setup

The bench script will create a `$workdir/.bin` folder and place
binaries it owns there. As of today, this is mainly the `opam` binary,
so the script can easily control which version of `opam` is being used.

This is fixed for a single bench invocation.

## Local Environment Setup

Local environment setup is done by creating opam switches, see the
`bench.sh:create_opam` function.

## Timing

Timing of package builds is done by instrumenting opam to wrap build
commands, using the `wrap-build-commands:` field to point to
`wrapper.sh`, which in turn calls `time` and `perf`.

This is not perfect, but seems like a good enough approximation.
