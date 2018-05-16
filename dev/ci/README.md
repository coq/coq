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

Add a new `ci-mydev.sh` script to [`dev/ci`](/dev/ci) (have a look at
[`ci-coq-dpdgraph.sh`](/dev/ci/ci-coq-dpdgraph.sh) or
[`ci-fiat-parsers.sh`](/dev/ci/ci-fiat-parsers.sh) for simple examples);
set the corresponding variables in
[`ci-basic-overlay.sh`](/dev/ci/ci-basic-overlay.sh); add the corresponding
target to [`Makefile.ci`](/Makefile.ci); add new jobs to
[`.gitlab-ci.yml`](/.gitlab-ci.yml),
[`.circleci/config.yml`](/.circleci/config.yml) and
[`.travis.yml`](/.travis.yml) so that this new target is run. **Do not
hesitate to submit an incomplete pull request if you need help to finish it.**

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

- Circle CI runs tests that are redundant with GitLab CI and may be removed
  eventually.

- Travis CI is used to test the compilation of Coq and run the test-suite on
  macOS. It also runs a linter that checks whitespace discipline. A
  [pre-commit hook](/dev/tools/pre-commit) is automatically installed by
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

Whenever your PR breaks tested developments, you should either adapt it
so that it doesn't, or provide a branch fixing these developments (or at
least work with the author of the development / other Coq developers to
prepare these fixes). Then, add an overlay in
[`dev/ci/user-overlays`](/dev/ci/user-overlays) (see the README there)
as part of your PR.

The process to merge your PR is then to submit PRs to the external
development repositories, merge the latter first (if the fixes are
backward-compatible), and merge the PR on Coq then.

See also [`test-suite/README.md`](/test-suite/README.md) for information about adding new tests to the test-suite.


Advanced GitLab CI information
------------------------------

GitLab CI is set up to use the "build artifact" feature to avoid
rebuilding Coq. In one job, Coq is built with `./configure -prefix _install_ci`
and `make install` is run, then the `_install_ci` directory
persists to and is used by the next jobs.

Artifacts can also be downloaded from the GitLab repository.
Currently, available artifacts are:
- the Coq executables and stdlib, in three copies varying in
  architecture and OCaml version used to build Coq.
- the Coq documentation, built only in the `build:base` job. When submitting
  a documentation PR, this can help reviewers checking the rendered result.

As an exception to the above, jobs testing that compilation triggers
no OCaml warnings build Coq in parallel with other tests.

### GitLab and Windows


If your repository has access to runners tagged `windows`, setting the
secret variable `WINDOWS` to `enabled` will add jobs building Windows
versions of Coq (32bit and 64bit).

The Windows jobs are enabled on Coq's repository, where pipelines for
pull requests run.

### GitLab and Docker

System and opam packages are installed in a Docker image. The image is
automatically built and uploaded to your GitLab registry, and is
loaded by subsequent jobs.

The Docker building job reuses the uploaded image if it is available,
but if you wish to save more time you can skip the job by setting
`SKIP_DOCKER` to `true`.

This means you will need to change its value when the Docker image
needs to be updated. You can do so for a single pipeline by starting
it through the web interface.

Setting up runners
------------------

Some of the runners we use come from Inria's CloudStack infrastructure, accessible at:

https://ci.inria.fr/project/coq/slaves

and

https://sesi-cloud-ctl1.inria.fr/client/

Both links require an Inria CI account. When using the second one, type "ci/coq"
for the domain.

To create a new VM, use the first link, click "Add slave", select Win7x64 and
"xLarge instance", then click "Create slave".

To connect to the VMs, follow instructions at: https://wiki.inria.fr/ciportal/Slaves_Access_Tutorial

We recommend to use rdesktop for Windows, and ssh for macOS and Linux.

### Windows

#### Installation of GitLab Runner

Here are the steps to prepare specifically an Inria CloudStack VM to work as a runner for our GitLab:

- Download GitLab Runner at
  https://gitlab-runner-downloads.s3.amazonaws.com/latest/binaries/gitlab-runner-windows-amd64.exe
  and save as C:\Gitlab-Runner\gitlab-runner.exe
- Install git (64 bits) from https://git-scm.com/download/win, to C:\Program Files\git
- When asked, choose autocrlf=input
- Install 7zip from https://www.7-zip.org/download.html, to C:\Program Files\7-Zip
- Start an administrator command prompt
- Run gitlab-runner.exe register and give the relevant settings (runner should use the tag "windows")
- Run gitlab-runner.exe install
- Run gitlab-runner.exe start
- Reboot the VMs (will put git in path for shell jobs)

#### Registering the runner

Follow the general documentation here: https://docs.gitlab.com/runner/install/windows.html
