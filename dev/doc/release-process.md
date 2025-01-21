# Release checklist #

## When the release managers for version `X.X` get nominated ##

- [ ] Create a new issue to track the release process where you can copy-paste the present checklist from `dev/doc/release-process.md` (we recommend duplicating the "For each release" section for X.Y+rc1 and for X.Y.0, removing the useless entries in each copy).
- [ ] Decide the release calendar with the team (date of branching, preview and final release).
- [ ] Create a wiki page that you link to from https://github.com/coq/coq/wiki/Release-Plan with this information and the link to the issue.

## About one month before the branching date ##

- [ ] Create both the upcoming final release (`X.X.0`) and the following major release (`Y.Y+rc1`) milestones if they do not already exist.
- [ ] Send an announcement of the upcoming branching date on Coqdev + the Coq development category on Discourse (coqdev@inria.fr + coq+coq-development@discoursemail.com) and ask people to remove from the `X.X+rc1` milestone any feature and clean up PRs that they already know won't be ready on time.
- [ ] Prepare a PR on `master` (not yet to be merged) changing the version name to the next major version and both magic numbers in [`tools/configure/configure.ml`](../../tools/configure/configure.ml). For example, for `8.5`, the version name will be `8.5+alpha` while the magic numbers will end with `80490`.
  This PR should be opened before the branching date to have time to deal with CI issues, but should not be merged until branching.

## On the branching date ##

- [ ] Merge the above PR and create the `vX.X` branch from the last merge commit before this one (using this name will ensure that the branch will be automatically protected).
- [ ] Set the next major version alpha tag using `git tag -s` (you can leave the tag message empty).  The `VY.Y+alpha` tag marks the first commit to be in `master` and not in the `vX.X` release branch (be careful about small `v` for branches and big `V` for tags). Note that this commit is the first commit in the first PR merged in master, not the merge commit for that PR. Therefore, if you proceeded as described above, this should be the commit updating the version and magic numbers.  After tagging, double-check that `git describe` picks up the tag you just made (if not, you tagged the wrong commit).
- [ ] Push the new tag with `git push upstream VY.Y+alpha --dry-run` (remove the `--dry-run` and redo if everything looks OK).
- [ ] In the milestone, add to the description a line like `@coqbot: backport to v8.20 (move rejected PRs to: https://github.com/coq/coq/milestone/60)`
- [ ] Monitor the [Release management project](https://github.com/orgs/coq/projects/11) in which coqbot will keep track of PRs to be backported (according to the previous command)
  The release manager is the person responsible for merging PRs that target the release branch and backporting appropriate PRs (mostly safe bug fixes, user message improvements and documentation updates) that are merged into `master`.
- [ ] For major releases, you can create new views in the above project (on the model of previous releases)
- [ ] Pin the versions of libraries and plugins in [`dev/ci/ci-basic-overlay.sh`](../ci/ci-basic-overlay.sh) to use commit hashes. You can use the [`dev/tools/pin-ci.sh`](../tools/pin-ci.sh) script to do this semi-automatically.
- [ ] In a PR on `master` to be backported, add a new link to the `'versions'` list of the refman (in `html_context` in [`doc/sphinx/conf.py`](../../doc/sphinx/conf.py)). At the same time, update the links of previous versions that were targeting branches to target a tag instead if the latest patch-level release is out.
- [ ] Add `{rocq-runtime,coq-core,rocq-core,coqide-server}.X.X.dev` packages in [`core-dev`](https://github.com/coq/opam-coq-archive/tree/master/core-dev)
- [ ] Ensure a `rocq-stdlib` package compatible with the new packages above exists either in [`ocaml repo`](https://github.com/ocaml/opam-repository) or in [`core-dev`](https://github.com/coq/opam-coq-archive/tree/master/core-dev)
- [ ] Add `coq.X.X.dev` package in [`core-dev`](https://github.com/coq/opam-coq-archive/tree/master/core-dev)
- [ ] Ping `@erikmd` and `@Zimmi48` to set up the infrastructure to have alpha Docker images built for the branch: the main steps amount to release `coq-bignums v9.Y.Y+coqX.X` in [`extra-dev`](https://github.com/coq/opam-coq-archive/tree/master/extra-dev), prepare a new [Docker-Coq](https://github.com/coq-community/docker-coq) image `coqorg/coq:X.X-alpha`, then browse <https://gitlab.inria.fr/coq/coq/-/hooks> to copy the `dev` webhook into a new `vX.X` webhook: `https://gitlab.com/api/v4/projects/19687072/trigger/pipeline?ref=master&variables[CRON_MODE]=rebuild-keyword&variables[ITEM]=X.X&token=_`, Push events → Wildcard pattern → `vX.X`, Test Push events. (If need be, the token can be regenerated at <https://gitlab.com/coq-community/docker-coq/-/settings/ci_cd>.)

## In the days following the branching ##

- [ ] Make sure that all the last feature PRs that you want to include in the release are finished and backported quickly and clean up the milestone.  We recommend backporting as few feature PRs as possible after branching.  In particular, any PR with overlays will require manually bumping the pinned commits when backporting.
- [ ] Delay non-blocking issues to the appropriate milestone and ensure blocking issues are solved. If required to solve some blocking issues, it is possible to revert some feature PRs in the release branch only (but in this case, the blocking issue should be postponed to the next major release instead of being closed).
- [ ] Once the final list of features is known, in a PR on `master` to be backported, generate the release changelog by calling [`dev/tools/generate-release-changelog.sh`](../tools/generate-release-changelog.sh) and include it in a new section in [`doc/sphinx/changes.rst`](../../doc/sphinx/changes.rst).
  The script automatically reorders the entries to show first the **Changed**, then the **Removed**, **Deprecated**, **Added** and last the **Fixed**. Manual adjustement is still needed when multiple entries are combined in a single changelog file.
- [ ] Start a draft release summary taking inspiration from the previous one.
  The [`dev/tools/list-contributors.sh`](../tools/list-contributors.sh) script computes the number and list of contributors between Coq revisions. Typically used with `VX.X+alpha..vX.X` to check the contributors of version `VX.X`.
  Note that this script relies on [`.mailmap`](../../.mailmap) to merge multiple identities.  If you notice anything incorrect while using it, use the opportunity to fix the `.mailmap` file.  Same thing if you want to have the full name of a contributor shown instead of a pseudonym.
Be sure the PR is not draft for better visibility and ask everyone in the dev team to contribute the main features and breaking changes sections before the final release.
- [ ] Put the branch name in the `CACHEKEY` variables in [`.gitlab-ci.yml`](../../.gitlab-ci.yml) (for instance ``old_ubuntu_lts-V2022-05-20-c34331afa5`` to ``"old_ubuntu_lts-v8.16-V2022-05-20-c34331afa5``) to indicate that it shouldn't be cleaned up even once it gets old. This should be done after all PRs touching the `CACHEKEY` variables have been merged.

## For each release (preview, final, patch-level, copy-paste for each) ##

- [ ] Ensure that there exists a milestone for the following version (both major and minor versions like X.Y.1).
- [ ] When doing so, add the new milestone to the coqbot command in the description of still-open previous milestones. For instance, when creating a milestone `8.20.1`, if there is an open milestone `8.19.3`, something tagged with the milestone `8.19.3` means: to be backported to the `v8.19` *and* the `v8.20` branches. The coqbot syntax is `@coqbot: backport to v8.19 (move rejected PRs to: <url of current milestone for 8.20>); backport to v8.20 (move rejected PRs to: <URL of current milestone for 8.21>); ...`.
- [ ] Ensure the release changelog has been merged (for release candidates the release summary can be left empty, it is required only for the final release).
- [ ] In a PR against `vX.X` (for testing):
  - Update the version number in [`tools/configure/configure.ml`](../../tools/configure/configure.ml).
  - Only update the magic numbers for the final release.
  - Set `is_a_released_version` to `true`.
- [ ] Set the tag `VX.X...` using `git tag -s`.
- [ ] Push the new tag with `git push upstream VX.X... --dry-run` (remove the `--dry-run` and redo if everything looks OK).
- [ ] Set `is_a_released_version` to `false` (if you forget about it, you'll be reminded by the test-suite failing whenever you try to backport a PR with a changelog entry).
- [ ] Close the milestone.
- [ ] Publish a release on GitHub with the PDF version of the reference manual attached. The PDF can be recovered from the artifacts of the `doc:ci-refman` job from continuous integration. Also attach a `tar.gz` archive of the sources (to ensure a stable hash, you can copy the archive autogenerated by github when the release is published).
- [ ] Ensure that someone is working on providing an opam package (either in the main [ocaml/opam-repository](https://github.com/ocaml/opam-repository) for standard releases or in the `core-dev` category of the [coq/opam-coq-archive](https://github.com/coq/opam-coq-archive) for preview releases).
- [ ] If pinged by opam package providers in pull requests to [ocaml/opam-repository](https://github.com/ocaml/opam-repository), transfer any changes to opam packages required by opam-repository CI (such as missing dependencies) to the corresponding package definitions in the Coq repository.
- [ ] Cc `@proux01` to ensure that a `coq-bignums` opam package is available in [`extra-dev`](https://github.com/coq/opam-coq-archive/tree/master/extra-dev) or [`released`](https://github.com/coq/opam-coq-archive/tree/master/released), respectively.
- [ ] Cc `@erikmd` to ensure that the necessary configuration is ready to release the Docker images in [`coqorg/coq`](https://hub.docker.com/r/coqorg/coq) (gathering `coq` and `coq-bignums` opam packages).
- [ ] For X.Y+rc1, send an e-mail on coqdev + coq-club + the Coq announcement category on Discourse (coqdev@inria.fr + coq-club@inria.fr + coq+announcements@discoursemail.com) announcing that the tag has been set so that package managers can start preparing package updates and library authors can safely start preparing compatible releases.
- [ ] For X.Y.0, once opam and Nix packages are ready (and ideally Docker images), announce the release to Coq-Club and Discourse (coq-club@inria.fr + coq+announcements@discoursemail.com).

## For each non-preview release ##

- [ ] Modify the version number in the file [`incl/macros.html`](https://github.com/coq/www/blob/master/incl/macros.html) on the website.

## Only for the final release of each major version ##

- [ ] Ping `@coq/zenodo-maintainers` to publish a new version on Zenodo.
  Process:
  1. Go to the [Zenodo Coq community](https://zenodo.org/communities/rocq-prover) and click on the existing "Coq Proof Assistant" record.
  2. Click on "New version".
  3. Click on "Upload files" and upload the PDF manual and the source tarball, copied from the GitHub release.
  4. Select the manual as the default preview.
  5. Enter the release date as publication date.
  6. Replace the release summary in the description with the one from the https://coq.inria.fr/refman/changes.html page for the current release (copy-pasting from the HTML page to the rich text editor works, except that bullet-point lists appear as quoted text, which you can fix easily in the rich text editor). Note that the first paragraph of the description is not the release summary but the general description of Coq, which should not change from one release to another.
  7. Change the "Project manager" to the current release manager, and update the project members to match the current maintainers if necessary.
  8. Add the (major) version number.
  9. Update the link to the release on GitHub (in the related works section).
  10. Click "Publish".
