# Working on third-party developments with *this* version of Rocq

Aim: getting an environment suitable for working on a third-party development
using the current version of Rocq (i.e., built from the current state of this
repository).

Dive into such an environment, for the project `example` by running, from the
root of this repository:

    ./dev/ci/nix/shell example

This will build Rocq and the other dependencies of the `example` project, then
open a shell with all these dependencies available (e.g., `coqtop` is in path).

Additionally, three environment variables are set, to abstract over the
build-system of that project: `configure`, `make`, and `clean`. Therefore, after
changing the working directory to the root of the sources of that project, the
contents of these variables can be evaluated to respectively set-up, build, and
clean the project.

## Variant: nocoq

The dependencies of the third-party developments are split into `buildInputs`
and `coqBuildInputs`. The second list gathers the Rocq libraries. In case you
only want the non-coq dependencies (because you want to use Rocq from your `PATH`),
set the environment variable `NOCOQ` to some non-empty value.
