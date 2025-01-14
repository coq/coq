Information for developers about the CI system
----------------------------------------------

When you submit a pull request (PR) on the Rocq GitHub repository, this will
launch a battery of CI tests. The PR will not be integrated
unless these tests pass.

We are currently running tests on the following platforms:

- GitLab CI is the main CI platform. It tests the compilation of Rocq,
  of the documentation, and of RocqIDE on Linux with several versions
  of OCaml and with warnings as errors; it runs the test-suite and
  tests the compilation of several external developments. It also runs
  a linter that checks whitespace discipline. A [pre-commit
  hook](../tools/pre-commit) is automatically installed by
  `./configure`. It should allow complying with this discipline
  without pain.

- Github Actions are used to test the compilation of Rocq on Windows
  and macOS. For Windows, the Rocq platform script is used, producing
  an installer that can be used to test Rocq.

You can anticipate the results of most of these tests prior to submitting your
PR by running GitLab CI on your private branches. To do so follow these steps:

1. Log into GitLab CI (the easiest way is to sign in with your GitHub account).
2. Click on "New Project".
3. Choose "CI / CD for external repository" then click on "GitHub".
4. Find your fork of the Rocq repository and click on "Connect".
5. If GitLab did not do so automatically, [enable the Container Registry](https://docs.gitlab.com/ee/user/project/container_registry.html#enable-the-container-registry-for-your-project).
6. You are encouraged to go to the CI / CD general settings and increase the
   timeout from 1h to 2h for better reliability.

Now every time you push (including force-push unless you changed the default
GitLab setting) to your fork on GitHub, it will be synchronized on GitLab and
CI will be run. You will receive an e-mail with a report of the failures if
there are some.

You can also run one CI target locally (using `make ci-somedev`).

See also [`test-suite/README.md`](../../test-suite/README.md) for information about adding new tests to the test-suite.

### Light and full CI

By default, only a light CI is run, mostly testing only Rocq itself.
Before merging a PR, it must also pass full CI testing multiple third party
developments. See [`CONTRIBUTING.md`](../../CONTRIBUTING.md#understanding-automatic-feedback)
for more details.

### Breaking changes

When your PR breaks external projects we test in our CI, you must:

1. Assess the breakage.
   * If it is a bug your PR introduces, it should be fixed.
   * Otherwise, you must assess the impact of the breakage and porting
     effort required on a few CI entries that exercise the
     functionality being changed.
2. Some breakages can be accepted, for instance to remove something
   already deprecated for long. Less obvious cases are to be
   determined with the PR assignee and reviewers, or discussed
   during a [weekly Call](https://github.com/coq/coq/wiki/Coq-Calls)
   when doubts remain.
3. For intentional breakages, you must then write porting instructions
   (typically the PR changelog), based on your previous assesment.
   For instance something like "ensuring compilation with Rocq X.Y and
   option -w +thing-we-are-removing-deprecated". You can also offer a
   script to help porting if you wish.
4. The PR assignee will finally ask the project maintainers to prepare
   a patch. For plugins, you must prepare yourself an overlay (you can
   ask the CI project maintainer for help). Ultimately, for
   non-plugin CI projects, the responsibility of preparing a patch
   falls on the project maintainer, but PR writers are encouraged to
   be helpful and may prepare patches themselves to facilitate a
   smooth process of adaptation. To ask project maintainers to adapt
   their development, the PR assignee can use the following template

   > @maintainer please update <dev>. You can do so by <instructions on how
   > to update, typically the PR changelog entry>
   > If <dev> is not updated in 7 days from now, it will be disabled in Rocq CI
   > so as to not further delay the current PR (the project can be reenabled
   > later, once fixed). In case you encounter
   > unanticipated difficulties, please come back to us (for instance below)
   > and feel free to request an extension.

   You can find the maintainers to ping in [ci-basic.sh](./ci-basic.sh).

   Of course, it's not in the interest of any developer to disable
   large spans of the CI, so best efforts will be made, in
   collaboration with the respective project maintainers to not
   disable some projects, considered flagship projects, particularly
   towards the base of the hierarchy.

There is experimental support for
an improved workflow, see [the next
section](#experimental-automatic-overlay-creation-and-building), below
are the steps to manually prepare a patch:

1. Fork the external project, create a new branch, push a commit adapting
   the project to your changes.

   We recommend that the commit message mention your PR's number and a
   short explanation of what changed, eg
   `Adapt to coq/coq#XXXXX (changed order of arguments of foo)`.

   The explanation makes it possible to understand what's going on
   without having to dereference github PR numbers.

2. Test your pull request with your adapted version of the external project by
   adding an overlay file to your pull request (cf.
   [`dev/ci/user-overlays/README.md`](user-overlays/README.md)).
3. Fixes to external libraries (pure Rocq projects) *must* be backward
   compatible (i.e. they should also work with the development version of Rocq,
   and the latest stable version). This will allow you to open a PR on the
   external project repository to have your changes merged *before* your PR on
   Rocq can be integrated.

   On the other hand, patches to plugins (projects linking to the Rocq ML API)
   can very rarely be made backward compatible and plugins we test will
   generally have a dedicated branch per Rocq version.
   You can still open a pull request but the merging will be requested by the
   developer who merges the PR on Rocq. To avoid early merges of such PR,
   which would break Rocq CI, it is recommended to keep them as draft PRs.

Moreover, in case of user visible change, your PR must absolutely add
a changelog entry. See the README in [`doc/changelog`][user-changelog]
for how to add a changelog entry.

### Experimental automatic overlay creation and building

If you break external projects that are hosted on GitHub, you can use
the `create_overlays.sh` script to automatically perform most of the
above steps. In order to do so:

- determine the list of failing projects:
IDs can be found as ci-XXX1 ci-XXX2 ci-XXX3 in the list of GitLab CI failures;
- for each project XXXi, look in [ci-basic-overlay.sh](https://github.com/coq/coq/blob/master/dev/ci/ci-basic-overlay.sh)
to see if the corresponding `XXXi_CI_GITURL` is hosted on GitHub;
- log on GitHub and fork all the XXXi projects hosted there;
- call the script as:

    ```
    ./dev/tools/create_overlays.sh ejgallego 9873 XXX1 XXX2 XXX3
    ```

    replacing `ejgallego` by your GitHub nickname, `9873` by the actual PR
number, and selecting the XXXi hosted on GitHub. The script will:

    + checkout the contributions and prepare the branch/remote so you can
      just commit the fixes and push,
    + add the corresponding overlay file in `dev/ci/user-overlays`;

- go to `_build_ci/XXXi` to prepare your overlay
(you can test your modifications by using `make -C ../.. ci-XXXi`)
and push using `git push ejgallego` (replacing `ejgallego` by your GitHub nickname);
- finally push the `dev/ci/user-overlays/9873-elgallego-YYY.sh` file on your Rocq fork
(replacing `9873` by the actual PR number, and `ejgallego` by your GitHub nickname).

For problems related to ML-plugins, if you use `dune build` to build
Rocq, it will actually be aware of the broken contributions and perform
a global build. This is very convenient when using `merlin` as you
will get a coherent view of all the broken plugins, with full
incremental cross-project rebuild.

Advanced GitLab CI information
------------------------------

GitLab CI is set up to use the "build artifact" feature to avoid
rebuilding Rocq. In one job, Rocq is built with `./configure -prefix _install_ci`
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

- the Rocq executables and stdlib, in four copies varying in
  architecture and OCaml version used to build Rocq:
  https://gitlab.com/coq/coq/-/jobs/artifacts/master/browse/_install_ci/?job=build:base

  Additionally, an experimental Dune build is provided:
  https://gitlab.com/coq/coq/-/jobs/artifacts/master/browse/_build/?job=build:edge:dune:dev

- the Rocq documentation, built in the `doc:*` jobs. When submitting a
  documentation PR, this can help reviewers checking the rendered
  result.  **@coqbot** will automatically post links to these
  artifacts in the PR checks section.  Furthermore, these artifacts are
  automatically deployed at:

  + Rocq's Reference Manual [master branch]:
    <https://coq.github.io/doc/master/refman/>
  + Rocq's Standard Library Documentation [master branch]:
    <https://coq.github.io/doc/master/stdlib/>
  + Rocq's ML API Documentation [master branch]:
    <https://coq.github.io/doc/master/api/>

### GitLab and Docker

System and opam packages are installed in a Docker image. The image is
automatically built and uploaded to your GitLab registry, and is
loaded by subsequent jobs.

**IMPORTANT**: When updating Rocq's CI docker image, you must modify
the `CACHEKEY` variable in [`.gitlab-ci.yml`](../../.gitlab-ci.yml)
(see comment near it for details).

The Docker building job reuses the uploaded image if it is available,
but if you wish to save more time you can skip the job by setting
`SKIP_DOCKER` to `true`.

In the case of the main Rocq repository, this variable is set to true
by default, but coqbot will set it to `false` anytime a PR modifies a
path matching `dev/ci/docker/.*Dockerfile.*`.

See also [`docker/README.md`](docker/README.md).
