Continuous Integration for the Coq Proof Assistant
==================================================

Changes to Coq are systematically tested for regression and compatibility
breakage on our Continuous Integration (CI) platforms *before* integration,
so as to ensure better robustness and catch problems as early as possible.
These tests include the compilation of several external libraries / plugins.

This document contains information for both external library / plugin authors,
who might be interested in having their development tested, and for Coq
developers / contributors, who must ensure that they don't break these
external developments accidentally.

*Remark:* the CI policy outlined in this document is susceptible to evolve and
specific accommodations are of course possible.

Information for external library / plugin authors
-------------------------------------------------

You are encouraged to consider submitting your development for addition to
our CI. This means that:

- Any time that a proposed change is breaking your development, Coq developers
  will send you patches to adapt it or, at the very least, will work with you
  to see how to adapt it.

On the condition that:

- At the time of the submission, your development works with Coq master branch.

- Your development is publicly available in a git repository and we can easily
  send patches to you (e.g. through pull / merge requests).

- You react in a timely manner to discuss / integrate those patches.

- You do not push, to the branches that we test, commits that haven't been
  first tested to compile with the corresponding branch(es) of Coq.

- Your development compiles in less than 35 minutes with just two threads.
  If this is not the case, consider adding a "lite" target that compiles just
  part of it.

In case you forget to comply with these last three conditions, we would reach
out to you and give you a 30-day grace period during which your development
would be moved into our "allow failure" category. At the end of the grace
period, in the absence of progress, the development would be removed from our
CI.

### Add your development by submitting a pull request

Add a new `ci-mydev.sh` script to [`dev/ci`](/dev/ci) (have a look at
[`ci-coq-dpdgraph.sh`](/dev/ci/ci-coq-dpdgraph.sh) or
[`ci-fiat-parsers.sh`](/dev/ci/ci-fiat-parsers.sh) for simple examples);
set the corresponding variables in
[`ci-basic-overlay.sh`](/dev/ci/ci-basic-overlay.sh); add the corresponding
target to [`Makefile.ci`](/Makefile.ci); add new jobs to
[`.travis.yml`](/.travis.yml) and [`.gitlab-ci.yml`](/.gitlab-ci.yml) so that
this new target is run. **Do not hesitate to submit an incomplete pull request
if you need help to finish it.**

You may also be interested in having your development tested in our
performance benchmark. Currently this is done by providing an OPAM package
in https://github.com/coq/opam-coq-archive and opening an issue at
https://github.com/coq/coq-bench/issues.


Information for developers
--------------------------

When you submit a pull request (PR) on Coq GitHub repository, this will
automatically launch a battery of CI tests. The PR will not be integrated
unless these tests pass.

Currently, we have two CI platforms:

- Travis is the main CI platform. It tests the compilation of Coq, of the
  documentation, and of CoqIDE on Linux with several versions of OCaml /
  camlp5, and with warnings as errors; it runs the test-suite and tests the
  compilation of several external developments. It also tests the compilation
  of Coq on OS X.

- AppVeyor is used to test the compilation of Coq and run the test-suite on
  Windows.

You can anticipate the results of these tests prior to submitting your PR
by having them run of your fork of Coq, on GitHub or GitLab. This can be
especially helpful given that our Travis platform is often overloaded and
therefore there can be a significant delay before these tests are actually
run on your PR. To take advantage of this, simply create a Travis account
and link it to your GitHub account, or activate the pipelines on your GitLab
fork.

You can also run one CI target locally (using `make ci-somedev`).

Whenever your PR breaks tested developments, you should either adapt it
so that it doesn't, or provide a branch fixing these developments (or at
least work with the author of the development / other Coq developers to
prepare these fixes). Then, add an overlay in
[`dev/ci/user-overlays`](/dev/ci/user-overlays) (see the README there)
in a separate commit in your PR.

The process to merge your PR is then to submit PRs to the external
development repositories, merge the latter first (if the fixes are
backward-compatible), drop the overlay commit and merge the PR on Coq then.

See also [`test-suite/README.md`](/test-suite/README.md) for information about adding new tests to the test-suite.


Travis specific information
---------------------------

Travis rebuilds all of Coq's executables and stdlib for each job. Coq
is built with `./configure -local`, then used for the job's test.


GitLab specific information
---------------------------

GitLab is set up to use the "build artifact" feature to avoid
rebuilding Coq. In one job, Coq is built with `./configure -prefix
install` and `make install` is run, then the `install` directory
persists to and is used by the next jobs.

Artifacts can also be downloaded from the GitLab repository.
Currently, available artifacts are:
- the Coq executables and stdlib, in three copies varying in
  architecture and Ocaml version used to build Coq.
- the Coq documentation, in two different copies varying in the OCaml
  version used to build Coq

As an exception to the above, jobs testing that compilation triggers
no Ocaml warnings build Coq in parallel with other tests.
