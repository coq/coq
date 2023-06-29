# Release checklist #

## When the release managers for version `X.X` get nominated ##

- [ ] Create a new issue to track the release process where you can copy-paste the present checklist from `dev/doc/release-process.md`.
- [ ] Decide the release calendar with the team (date of branching, preview and final release).
- [ ] Create a wiki page that you link to from https://github.com/coq/coq/wiki/Release-Plan with this information and the link to the issue.

## About one month before the branching date ##

- [ ] Create both the upcoming final release (`X.X.0`) and the following major release (`Y.Y+rc1`) milestones if they do not already exist.
- [ ] Send an announcement of the upcoming branching date on Coqdev + the Coq development category on Discourse (coqdev@inria.fr + coq+coq-development@discoursemail.com) and ask people to remove from the `X.X+rc1` milestone any feature and clean up PRs that they already know won't be ready on time.
- [ ] In a PR on `master`, call [`dev/tools/update-compat.py`](../tools/update-compat.py) with the `--release` flag; this sets up Coq to support three `-compat` flag arguments including the upcoming one (instead of four).  To ensure that CI passes, you will have to decide what to do about all test-suite files that mention `-compat U.U` or `Coq.Compat.CoqUU` (which is no longer valid, since we only keep compatibility against the two previous versions), and you may have to ping maintainers of projects that are still relying on the old compatibility flag so that they fix this.
- [ ] Make sure that this change is merged in time for the branching date.
- [ ] Prepare a PR on `master` (not yet to be merged) changing the version name to the next major version and both magic numbers in [`tools/configure/configure.ml`](../../tools/configure/configure.ml). For example, for `8.5`, the version name will be `8.5+alpha` while the magic numbers will end with `80490`.
  Additionally, in the same commit, update the compatibility infrastructure, which consists of invoking [`dev/tools/update-compat.py`](../tools/update-compat.py) with the `--master` flag.
  Note that the `update-compat.py` script must be run twice: once in preparation of the release with the `--release` flag (see earlier in this section) and once on the branching date with the `--master` flag to mark the start of the next version.
  This PR should be opened before the branching date to have time to deal with CI issues, but should not be merged until branching.

## On the branching date ##

- [ ] Merge the above PR and create the `vX.X` branch from the last merge commit before this one (using this name will ensure that the branch will be automatically protected).
- [ ] Set the next major version alpha tag using `git tag -s`.  The `VY.Y+alpha` tag marks the first commit to be in `master` and not in the `vX.X` release branch. Note that this commit is the first commit in the first PR merged in master, not the merge commit for that PR. Therefore, if you proceeded as described above, this should be the commit updating the version, magic numbers and compatibility infrastructure.  After tagging, double-check that `git describe` picks up the tag you just made (if not, you tagged the wrong commit).
- [ ] Push the new tag with `git push upstream VY.Y+alpha --dry-run` (remove the `--dry-run` and redo if everything looks OK).
- [ ] Start a new ["classic" project](https://github.com/coq/coq/projects?type=classic) to track PR backporting. The project should have a `Request X.X+rc1 inclusion` column for the PRs that were merged in `master` that are to be considered for backporting, and a `Shipped in X.X+rc1` columns to put what was backported. A message to `@coqbot` in the milestone description tells it to automatically add merged PRs to the `Request ... inclusion` column and backported PRs to the `Shipped in ...` column. See previous milestones for examples. When moving to the next milestone (e.g. `X.X.0`), you can clear and remove the `Request X.X+rc1 inclusion` column and create new `Request X.X.0 inclusion` and `Shipped in X.X.0` columns.
  The release manager is the person responsible for merging PRs that target the release branch and backporting appropriate PRs (mostly safe bug fixes, user message improvements and documentation updates) that are merged into `master`.
- [ ] Pin the versions of libraries and plugins in [`dev/ci/ci-basic-overlay.sh`](../ci/ci-basic-overlay.sh) to use commit hashes. You can use the [`dev/tools/pin-ci.sh`](../tools/pin-ci.sh) script to do this semi-automatically.
- [ ] In a PR on `master` to be backported, add a new link to the `'versions'` list of the refman (in `html_context` in [`doc/sphinx/conf.py`](../../doc/sphinx/conf.py)).
- [ ] Ping `@Zimmi48` and `@erikmd` to set up the infrastructure to have alpha Docker images built for the branch.

## In the days following the branching ##

- [ ] Make sure that all the last feature PRs that you want to include in the release are finished and backported quickly and clean up the milestone.  We recommend backporting as few feature PRs as possible after branching.  In particular, any PR with overlays will require manually bumping the pinned commits when backporting.
- [ ] Delay non-blocking issues to the appropriate milestone and ensure blocking issues are solved. If required to solve some blocking issues, it is possible to revert some feature PRs in the release branch only (but in this case, the blocking issue should be postponed to the next major release instead of being closed).
- [ ] Once the final list of features is known, in a PR on `master` to be backported, generate the release changelog by calling [`dev/tools/generate-release-changelog.sh`](../tools/generate-release-changelog.sh) and include it in a new section in [`doc/sphinx/changes.rst`](../../doc/sphinx/changes.rst).
  The script automatically reorders the entries to show first the **Changed**, then the **Removed**, **Deprecated**, **Added** and last the **Fixed**. Manual adjustement is still needed when multiple entries are combined in a single changelog file.
- [ ] Ping the development coordinator (`@mattam82`) to get him started on writing the release summary.
  The [`dev/tools/list-contributors.sh`](../tools/list-contributors.sh) script computes the number and list of contributors between Coq revisions. Typically used with `VX.X+alpha..vX.X` to check the contributors of version `VX.X`.
  Note that this script relies on [`.mailmap`](../../.mailmap) to merge multiple identities.  If you notice anything incorrect while using it, use the opportunity to fix the `.mailmap` file.  Same thing if you want to have the full name of a contributor shown instead of a pseudonym.
- [ ] Put the branch name in CACHEKEY in [`.gitlab-ci.yml`](../../.gitlab-ci.yml) (for instance ``ubuntu_coq-V2022-05-20-c34331afa5`` to ``"ubuntu_coq-v8.16-V2022-05-20-c34331afa5``) to indicate that it shouldn't be cleaned up even once it gets old. This should be done after all PRs touching CACHEKEY have been merged.

## For each release (preview, final, patch-level) ##

- [ ] Ensure that there exists a milestone for the following version.
- [ ] Ensure the release changelog has been merged (the release summary is required for the final release).
- [ ] In a PR against `vX.X` (for testing):
  - Update the version number in [`tools/configure/configure.ml`](../../tools/configure/configure.ml).
  - Only update the magic numbers for the final release.
  - Set `is_a_released_version` to `true`.
- [ ] Set the tag `VX.X...` using `git tag -s`.
- [ ] Push the new tag with `git push upstream VX.X... --dry-run` (remove the `--dry-run` and redo if everything looks OK).
- [ ] Set `is_a_released_version` to `false` (if you forget about it, you'll be reminded by the test-suite failing whenever you try to backport a PR with a changelog entry).
- [ ] Close the milestone.
- [ ] Send an e-mail on Coqdev + the Coq development category on Discourse (coqdev@inria.fr + coq+coq-development@discoursemail.com) announcing that the tag has been set so that package managers can start preparing package updates (including a `coq-bignums` compatible version).
- [ ] In particular, ensure that someone is working on providing an opam package (either in the main [ocaml/opam-repository](https://github.com/ocaml/opam-repository) for standard releases or in the `core-dev` category of the [coq/opam-coq-archive](https://github.com/coq/opam-coq-archive) for preview releases.
- [ ] Make sure to cc `@erikmd` to request that he prepares the necessary configuration for the Docker release in [`coqorg/coq`](https://hub.docker.com/r/coqorg/coq) (namely, he'll need to make sure a `coq-bignums` opam package is available in [`extra-dev`](https://github.com/coq/opam-coq-archive/tree/master/extra-dev), respectively
  [`released`](https://github.com/coq/opam-coq-archive/tree/master/released), so the Docker image gathering `coq` and `coq-bignums` can be built).
- [ ] Publish a release on GitHub with the PDF version of the reference manual attached. The PDF can be recovered from the artifacts of the `doc:refman-pdf` job from continuous integration.

## For the first release candidate release ##

- [ ] In coordination with platform maintainers, announce the release candidate to Coq-Club and Discourse (coq-club@inria.fr + coq+announcements@discoursemail.com) with the message that:
  - the release candidate is stable: library authors can safely start preparing compatible releases;
  - in particular, the authors of packages that are included in the platform should do so as soon as possible to avoid delaying the platform release (and remind the expected calendar);
  - a further announcement will follow when the platform is ready to install this version of Coq.

## For each non-preview release ##

- [ ] Modify the version number in the file [`incl/macros.html`](https://github.com/coq/www/blob/master/incl/macros.html) on the website.
- [ ] Ping `@Zimmi48` to switch the default version of the reference manual on the website.
  This is done by logging into the server (`vps697916.ovh.net`), editing two `ProxyPass` lines (one for the refman and one for the stdlib doc) with `sudo vim /etc/apache2/sites-available/000-coq.inria.fr.conf`, then running `sudo systemctl reload apache2`.
  *TODO:* automate this or make it doable through the `www` git repository. See [coq/www#111](https://github.com/coq/www/issues/111) and [coq/www#131](https://github.com/coq/www/issues/131).

## Only for the final release of each major version ##

- [ ] Ping `@Zimmi48` to publish a new version on Zenodo.
  *TODO:* automate this with coqbot.

## This is now delegated to the platform maintainers ##

- [ ] Sign the Windows and MacOS packages and upload them on GitHub.
  + The Windows packages must be signed by the Inria IT security service. They should be sent as a link to the binary (via [filesender](https://filesender.renater.fr) for example) together with its SHA256 hash in a signed e-mail to `dsi.securite` @ `inria.fr` putting `@maximedenes` in carbon copy.
  + The MacOS packages should be signed with our own certificate.
  + The Snap package has to be built and uploaded to the snap store by running a [platform CI job manually](https://github.com/coq/platform/tree/2021.02/linux/snap/github_actions).
    Then ask a Platform maintainer with access to the store to publish the upload or give you access so that you can do it yourself.
- [ ] Announce the release to Coq-Club and Discourse (coq-club@inria.fr + coq+announcements@discoursemail.com).
