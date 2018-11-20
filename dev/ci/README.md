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

- You maintain a reasonable build time for your development, or you provide
  a "lite" target that we can use.

In case you forget to comply with these last three conditions, we would reach
out to you and give you a 30-day grace period during which your development
would be moved into our "allow failure" category. At the end of the grace
period, in the absence of progress, the development would be removed from our
CI.

### Add your development by submitting a pull request

Add a new `ci-mydev.sh` script to [`dev/ci`](.); set the corresponding
variables in [`ci-basic-overlay.sh`](ci-basic-overlay.sh); add the
corresponding target to [`Makefile.ci`](../../Makefile.ci) and a new job to
[`.gitlab-ci.yml`](../../.gitlab-ci.yml) so that this new target is run.
Have a look at [#7656](https://github.com/coq/coq/pull/7656/files) for an
example. **Do not hesitate to submit an incomplete pull request if you need
help to finish it.**

You may also be interested in having your development tested in our
performance benchmark. Currently this is done by providing an OPAM package
in https://github.com/coq/opam-coq-archive and opening an issue at
https://github.com/coq/coq-bench/issues.


Information for developers
--------------------------

When you submit a pull request (PR) on Coq GitHub repository, this will
automatically launch a battery of CI tests. The PR will not be integrated
unless these tests pass.

We are currently running tests on the following platforms:

- GitLab CI is the main CI platform. It tests the compilation of Coq, of the
  documentation, and of CoqIDE on Linux with several versions of OCaml /
  camlp5, and with warnings as errors; it runs the test-suite and tests the
  compilation of several external developments.

- Travis CI is used to test the compilation of Coq and run the test-suite on
  macOS. It also runs a linter that checks whitespace discipline. A
  [pre-commit hook](../tools/pre-commit) is automatically installed by
  `./configure`. It should allow complying with this discipline without pain.

- AppVeyor is used to test the compilation of Coq and run the test-suite on
  Windows.

You can anticipate the results of most of these tests prior to submitting your
PR by running GitLab CI on your private branches. To do so follow these steps:

1. Log into GitLab CI (the easiest way is to sign in with your GitHub account).
2. Click on "New Project".
3. Choose "CI / CD for external repository" then click on "GitHub".
4. Find your fork of the Coq repository and click on "Connect".
5. If GitLab did not do so automatically, [enable the Container Registry](https://docs.gitlab.com/ee/user/project/container_registry.html#enable-the-container-registry-for-your-project).
6. You are encouraged to go to the CI / CD general settings and increase the
   timeout from 1h to 2h for better reliability.

Now everytime you push (including force-push unless you changed the default
GitLab setting) to your fork on GitHub, it will be synchronized on GitLab and
CI will be run. You will receive an e-mail with a report of the failures if
there are some.

You can also run one CI target locally (using `make ci-somedev`).

See also [`test-suite/README.md`](../../test-suite/README.md) for information about adding new tests to the test-suite.

### Breaking changes

When your PR breaks an external project we test in our CI, you must prepare a
patch (or ask someone to prepare a patch) to fix the project:

1. Fork the external project, create a new branch, push a commit adapting
   the project to your changes.
2. Test your pull request with your adapted version of the external project by
   adding an overlay file to your pull request (cf.
   [`dev/ci/user-overlays/README.md`](user-overlays/README.md)).
3. Fixes to external libraries (pure Coq projects) *must* be backward
   compatible (i.e. they should also work with the development version of Coq,
   and the latest stable version). This will allow you to open a PR on the
   external project repository to have your changes merged *before* your PR on
   Coq can be integrated.

   On the other hand, patches to plugins (projects linking to the Coq ML API)
   can very rarely be made backward compatible and plugins we test will
   generally have a dedicated branch per Coq version.
   You can still open a pull request but the merging will be requested by the
   developer who merges the PR on Coq. There are plans to improve this, cf.
   [#6724](https://github.com/coq/coq/issues/6724).

Moreover your PR must absolutely update the [`CHANGES.md`](../../CHANGES.md) file.

Advanced GitLab CI information
------------------------------

GitLab CI is set up to use the "build artifact" feature to avoid
rebuilding Coq. In one job, Coq is built with `./configure -prefix _install_ci`
and `make install` is run, then the `_install_ci` directory
persists to and is used by the next jobs.

### Artifacts

Build artifacts from GitLab can be linked / downloaded in a systematic
way, see [GitLab's documentation](https://docs.gitlab.com/ce/user/project/pipelines/job_artifacts.html#downloading-the-latest-job-artifacts)
for more information. For example, to access the documentation of the
`master` branch, you can do:

https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_install_ci/share/doc/coq/sphinx/html/index.html?job=doc:refman

Browsing artifacts is also possible:
https://gitlab.com/coq/coq/-/jobs/artifacts/master/browse/_install_ci/?job=build:base

Above, you can replace `master` and `job` by the desired GitLab branch and job name.

Currently available artifacts are:

- the Coq executables and stdlib, in four copies varying in
  architecture and OCaml version used to build Coq:
  https://gitlab.com/coq/coq/-/jobs/artifacts/master/browse/_install_ci/?job=build:base

- the Coq documentation, built in the `doc:*` jobs. When submitting
  a documentation PR, this can help reviewers checking the rendered result:

  + Coq's Reference Manual [master branch]
    https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_install_ci/share/doc/coq/sphinx/html/index.html?job=doc:refman
  + Coq's Standard Library Documentation [master branch]
    https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_install_ci/share/doc/coq/html/stdlib/index.html?job=build:base
  + Coq's ML API Documentation [master branch]
    https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/dev/ocamldoc/html/index.html?job=doc:ml-api

### GitLab and Windows

If your repository has access to runners tagged `windows`, setting the
secret variable `WINDOWS` to `enabled` will add jobs building Windows
versions of Coq (32bit and 64bit).

If the secret variable `WINDOWS` is set to `enabled_all_addons`,
an extended set of addons will be added to the Windows installer.
This leads to a considerable runtime in CI so this is not enabled
by default for pipelines for pull requests.

The Windows jobs are enabled on Coq's repository, where pipelines for
pull requests run.

### GitLab and Docker

System and opam packages are installed in a Docker image. The image is
automatically built and uploaded to your GitLab registry, and is
loaded by subsequent jobs.

**IMPORTANT**: When updating Coq's CI docker image, you must modify
the `CACHEKEY` variable in [`.gitlab-ci.yml`](../../.gitlab-ci.yml)
and [`Dockerfile`](docker/bionic_coq/Dockerfile)

The Docker building job reuses the uploaded image if it is available,
but if you wish to save more time you can skip the job by setting
`SKIP_DOCKER` to `true`.

This means you will need to change its value when the Docker image
needs to be updated. You can do so for a single pipeline by starting
it through the web interface.

See also [`docker/README.md`](docker/README.md).
