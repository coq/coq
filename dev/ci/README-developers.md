Information for developers about the CI system
----------------------------------------------

When you submit a pull request (PR) on the Coq GitHub repository, this will
automatically launch a battery of CI tests. The PR will not be integrated
unless these tests pass.

We are currently running tests on the following platforms:

- GitLab CI is the main CI platform. It tests the compilation of Coq,
  of the documentation, and of CoqIDE on Linux with several versions
  of OCaml and with warnings as errors; it runs the test-suite and
  tests the compilation of several external developments. It also runs
  a linter that checks whitespace discipline. A [pre-commit
  hook](../tools/pre-commit) is automatically installed by
  `./configure`. It should allow complying with this discipline
  without pain.

- AppVeyor is used to test the compilation of Coq and run the test-suite on
  Windows.

- Azure Pipelines is used to test the compilation of Coq and run the
  test-suite on Windows and on macOS. It is expected to replace
  appveyor eventually.

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

When your PR breaks an external project we test in our CI, you must
prepare a patch (or ask someone to prepare a patch) to fix the
project. There is experimental support for an improved workflow, see
[the next section](#experimental-automatic-overlay-creation-and-building), below
are the steps to manually prepare a patch:

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

### Experimental automatic overlay creation and building

If you break external projects that are hosted on GitHub, you can use
the `create-overlays.sh` script to automatically perform most of the
above steps. In order to do so, call the script as:
```
./dev/tools/create-overlays.sh ejgallego 9873 aac_tactics elpi ltac
```
replacing `ejgallego` by your GitHub nickname and `9873` by the actual PR
number. The script will:

- checkout the contributions and prepare the branch/remote so you can
  just commit the fixes and push,
- add the corresponding overlay file in `dev/ci/user-overlays`.

For problems related to ML-plugins, if you use `dune build` to build
Coq, it will actually be aware of the broken contributions and perform
a global build. This is very convenient when using `merlin` as you
will get a coherent view of all the broken plugins, with full
incremental cross-project rebuild.

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

  Additionally, an experimental Dune build is provided:
  https://gitlab.com/coq/coq/-/jobs/artifacts/master/browse/_build/?job=build:edge:dune:dev

- the Coq documentation, built in the `doc:*` jobs. When submitting
  a documentation PR, this can help reviewers checking the rendered result:

  + Coq's Reference Manual [master branch]
    https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_install_ci/share/doc/coq/sphinx/html/index.html?job=doc:refman
  + Coq's Standard Library Documentation [master branch]
    https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_install_ci/share/doc/coq/html/stdlib/index.html?job=build:base
  + Coq's ML API Documentation [master branch]
    https://gitlab.com/coq/coq/-/jobs/artifacts/master/file/_build/default/_doc/_html/index.html?job=doc:ml-api:odoc

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
