Information for external library / Coq plugin authors
-----------------------------------------------------

You are encouraged to consider submitting your project for addition to
Coq's CI. This means that:

- Any time that a proposed change is breaking your project, Coq
  developers and contributors will send you patches to adapt it or
  will explain how to adapt it and work with you to ensure that you
  manage to do it.

On the condition that:

- For libraries: your project should exercise some part of Coq which
  is not well covered by the existing CI and test suite.

  There is no such requirement for plugins: developers may reduce the
  cost of working with Coq's unstable OCaml API by adding
  their plugin to Coq's CI and getting it fixed when the API changes (as long
  as fixing the plugin doesn't put an undue burden on Coq developers).

- At the time of the submission, your project works with Coq's
  `master` branch.

- Your project is publicly available in a git repository and we can easily
  send patches to you (e.g. through pull / merge requests).

- You react in a timely manner to discuss / integrate those patches.
  When seeking your help for preparing such patches, we will accept
  that it takes longer than when we are just requesting to integrate a
  simple (and already fully prepared) patch.

- You do not push, to the branch that we test, commits that haven't been
  first tested to compile with the corresponding branch of Coq.

  For that, we recommend setting a CI system for you project, see
  [supported CI images for Coq](#supported-ci-images-for-coq) below.

- You maintain a reasonable build time for your project, or you provide
  a "lite" target that we can use.

- You keep points of contact up to date.

In case you forget to comply with these last four conditions, we would reach
out to you and give you a 30-day grace period during which your project
would be moved into our "allow failure" category. At the end of the grace
period, in the absence of progress, the project would be removed from our
CI.

### Timely merging of overlays

A pitfall of the current CI setup is that when a breaking change is
merged in Coq upstream, CI for your contrib will be broken until you
merge the corresponding pull request with the fix for your contribution.

As of today, you have to worry about synchronizing with Coq upstream
every once in a while; a workaround is to give merge permissions to
someone from the Coq team as to help with these kind of merges.

### OCaml and plugin-specific considerations

Projects that link against Coq's OCaml API [most of them are known
as "plugins"] do have some special requirements:

- Coq's OCaml API is not stable. We hope to improve this in the future
  but as of today you should expect to have to merge a fair amount of
  "overlays", usually in the form of Pull Requests from Coq developers
  in order to keep your plugin compatible with Coq master.

  In order to alleviate the load, you can delegate the merging of such
  compatibility pull requests to Coq developers themselves, by
  granting access to the plugin repository or by using `bots` such as
  [Bors](https://github.com/apps/bors) that allow for automatic
  management of Pull Requests.

### Add your project by submitting a pull request

Add a new `ci-mydev.sh` script to [`dev/ci`](.); set the corresponding
variables in [`ci-basic-overlay.sh`](ci-basic-overlay.sh); add the
corresponding target to [`Makefile.ci`](../../Makefile.ci) and a new job to
[`.gitlab-ci.yml`](../../.gitlab-ci.yml) so that this new target is run.
Have a look at [#17241](https://github.com/coq/coq/pull/17241/files) for an
example. **Do not hesitate to submit an incomplete pull request if you need
help to finish it.**

Some important points:

- Mention one or a few points of contact in
  [`ci-basic-overlay.sh`](ci-basic-overlay.sh).

- Let `$job` be the name of the new job as used for the name of
  the added script file `dev/ci/ci-$job.sh`. Then the added target
  in `Makefile.ci` must be named `ci-$job` and the added job in
  `.gitlab-ci.yml` must be named `library:$job` or
  `plugin:$job`. `$job` must be a valid shell variable name,
  typically this means replacing dashs (`-`) with underscores (`_`).

- Let `$project` be the name of your project as used for the first
  argument to `project` in `ci-basic-overlay.sh`. Usually this is the
  same as `$job` in the above bullet. It must also be a valid
  shell variable name. In some cases a script will handle multiple
  source repositories and so will need multiple `$project`, see for
  instance script `verdi_raft`.

- If you wish to run a test suite for your project which takes
  non-negligible time, it may be useful to run the test suite in a
  separate `Makefile.ci` target and GitLab job, using a separate shell
  script. In terms of the above bullet points this means a `$project`
  used in multiple `$job`s. See for instance `mathcomp` and `mathcomp_test`.

- When declaring the job in `.gitlab-ci.yml` you must choose the opam
  switch by using `extends: .ci-template` or `extends: .ci-template-flambda`.

  The first one uses the minimum version of OCaml supported by Coq.
  The second one uses the highest version of OCaml supported by Coq,
  with flambda enabled (currently it actually uses OCaml 4.14.1 as 5.0
  has significant performance issues). See also the corresponding
  [`Dockerfiles`](docker/) to find out what
  specific packages are available in each switch.

  If your job depends on other jobs, you must use the same opam
  switch. If you wish to depend on jobs currently declared in separate
  switches, please open a draft pull request and the Coq developers
  will decide which jobs should change switches. If you need an
  exception to this rule for some other reason, please discuss with
  the Coq developers.

- Job dependencies are declared in 2 places: `Makefile.ci` using the
  usual Makefile syntax, and `.gitlab-ci.yml` using `needs`. If you
  only depend on Coq itself the implicit `needs` from the template
  suffices. Otherwise the `needs` list must include `build:base` or
  `build:edge+flambda` (depending on the switch you chose). See for
  instance the declaration for `library:ci-analysis`.

- If you depend on more than Coq itself you must specify the `stage`:
  `build-2` if all your dependencies depend only on Coq itself,
  otherwise `build-3+` (the number is the max depth of the dependency
  chain, with Coq itself at 0 and the default from the template at 1).

- If needed you can disable native compilation by doing `export
  COQEXTRAFLAGS='-native-compiler no'` before the build commands in
  the script file. If any of your dependencies disable native
  compilation you must do the same.

You may also be interested in having your project tested in our
performance benchmark. Currently this is done by providing a `.dev` OPAM package
in https://github.com/coq/opam-coq-archive and opening an issue at
https://github.com/coq/coq/issues.

### Recommended branching policy.

It is sometimes the case that you will need to maintain a branch of
your project for particular Coq versions. This is in fact very likely
if your project includes a Coq ML plugin.

For such projects, we recommend a branching convention that mirrors
Coq's branching policy. Then, you would have a `master` branch that
follows Coq's `master`, a `v8.8` branch that works with Coq's `v8.8`
branch and so on.

This convention will be supported by tools in the future to make some
developer commands work more seamlessly.

### Supported CI images for Coq

The Coq developers and contributors provide official Docker and Nix
images for testing against Coq master. Using these images is highly
recommended:

- For Docker, see: https://github.com/coq-community/docker-coq

  The https://github.com/coq-community/docker-coq/wiki/CI-setup wiki
  page contains additional information and templates to help setting
  Docker-based CI up for your Coq project

- For Nix, see the setup at
  https://github.com/coq-community/manifesto/wiki/Continuous-Integration-with-Nix
