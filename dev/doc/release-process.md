# Release process #

## As soon as the previous version branched off master ##

- [ ] Create a new issue to track the release process where you can copy-paste
  the present checklist.
- [ ] Change the version name to the next major version and the magic numbers
  (see [#7008](https://github.com/coq/coq/pull/7008/files)).
- [ ] Update the compatibility infrastructure, which consists of doing
      the following steps.  Note that all but the final step can be
      performed automatically by
      [`dev/tools/update-compat.py`](/dev/tools/update-compat.py) so
      long as you have already updated `coq_version` in
      [`configure.ml`](/configure.ml).
  + [ ] Add a file `theories/Compat/CoqXX.v` which contains just the header
        from [`dev/header.ml`](/dev/header.ml)
  + [ ] Add the line `Require Export Coq.Compat.CoqXX.` at the top of
        `theories/Compat/CoqYY.v`, where Y.Y is the version prior to X.X.
  + [ ] Delete the file `theories/Compat/CoqWW.v`, where W.W is three versions
        prior to X.X.
  + [ ] Update
        [`doc/stdlib/index-list.html.template`](/doc/stdlib/index-list.html.template)
        with the deleted/added files.
  + [ ] Remove any notations in the standard library which have `compat "W.W"`.
  + [ ] Update the type `compat_version` in [`lib/flags.ml`](/lib/flags.ml) by
        bumping all the version numbers by one, and update the interpretations
        of those flags in [`toplevel/coqargs.ml`](/toplevel/coqargs.ml) and
        [`vernac/g_vernac.mlg`](/vernac/g_vernac.mlg).
  + [ ] Update the files
        [`test-suite/success/CompatCurrentFlag.v`](/test-suite/success/CompatCurrentFlag.v),
        [`test-suite/success/CompatPreviousFlag.v`](/test-suite/success/CompatPreviousFlag.v),
        and
        [`test-suite/success/CompatOldFlag.v`](/test-suite/success/CompatOldFlag.v)
        by bumping all version numbers by 1.
  + [ ] Decide what to do about all test-suite files which mention `-compat
        W.W` or `Coq.Comapt.CoqWW` (which is no longer valid, since we only
        keep compatibility against the two previous versions)
- [ ] Put the corresponding alpha tag using `git tag -s`.
  The `VX.X+alpha` tag marks the first commit to be in `master` and not in the
  branch of the previous version.
- [ ] Create the `X.X+beta1` milestone if it did not already exist.
- [ ] Decide the release calendar with the team (freeze date, beta date, final
  release date) and put this information in the milestone (using the
  description and due date fields).

## About one month before the beta ##

- [ ] Create the `X.X.0` milestone and set its due date.
- [ ] Send an announcement of the upcoming freeze on Coqdev and ask people to
  remove from the beta milestone what they already know won't be ready on time
  (possibly postponing to the `X.X.0` milestone for minor bug fixes,
  infrastructure and documentation updates).
- [ ] Determine which issues should / must be fixed before the beta, add them
  to the beta milestone, possibly with a
  ["priority: blocker"](https://github.com/coq/coq/labels/priority%3A%20blocker)
  label. Make sure that all these issues are assigned (and that the assignee
  provides an ETA).
- [ ] Ping the development coordinator (**@mattam82**) to get him started on
  the update to the Credits chapter of the reference manual.
  See also [#7058](https://github.com/coq/coq/issues/7058).
  The command to get the list of contributors for this version is
  `git shortlog -s -n VX.X+alpha..master | cut -f2 | sort -k 2`
  (the ordering is approximative as it will misplace people with middle names).

## On the date of the feature freeze ##

- [ ] Create the new version branch `vX.X` and
  [protect it](https://github.com/coq/coq/settings/branches)
  (activate the "Protect this branch", "Require pull request reviews before
  merging" and "Restrict who can push to this branch" guards).
- [ ] Remove all remaining unmerged feature PRs from the beta milestone.
- [ ] Start a new project to track PR backporting. The proposed model is to
  have a "X.X-only PRs" column for the rare PRs on the stable branch, a
  "Request X.X inclusion" column for the PRs that were merged in `master` that
  are to be considered for backporting, a "Waiting for CI" column to put the
  PRs in the process of being backported, and "Shipped in ..." columns to put
  what was backported. (The release manager is the person responsible for
  merging PRs that target the version branch and backporting appropriate PRs
  that are merged into `master`).
  A message to **@coqbot** in the milestone description tells it to
  automatically add merged PRs to the "Request X.X inclusion" column.
- [ ] Delay non-blocking issues to the appropriate milestone and ensure
  blocking issues are solved. If required to solve some blocking issues,
  it is possible to revert some feature PRs in the version branch only.

## Before the beta release date ##

- [ ] Ensure the Credits chapter has been updated.
- [ ] Ensure that an appropriate version of the plugins we will distribute with
  Coq has been tagged.
- [ ] Have some people test the recently auto-generated Windows and MacOS
  packages.
- [ ] Change the version name from alpha to beta1 (see
  [#7009](https://github.com/coq/coq/pull/7009/files)).
  We generally do not update the magic numbers at this point.
- [ ] Put the `VX.X+beta1` tag using `git tag -s`.

### These steps are the same for all releases (beta, final, patch-level) ###

- [ ] Send an e-mail on Coqdev announcing that the tag has been put so that
  package managers can start preparing package updates.
- [ ] Draft a release on GitHub.
- [ ] Get **@maximedenes** to sign the Windows and MacOS packages and
  upload them on GitHub.
- [ ] Prepare a page of news on the website with the link to the GitHub release
  (see [coq/www#63](https://github.com/coq/www/pull/63)).
- [ ] Upload the new version of the reference manual to the website.
  *TODO: setup some continuous deployment for this.*
- [ ] Merge the website update, publish the release
  and send annoucement e-mails.
- [ ] Ping **@Zimmi48** to publish a new version on Zenodo.
  *TODO: automate this.*
- [ ] Close the milestone

## At the final release time ##

- [ ] Change the version name to X.X.0 and the magic numbers (see
  [#7271](https://github.com/coq/coq/pull/7271/files)).
- [ ] Put the `VX.X.0` tag.

Repeat the generic process documented above for all releases.

- [ ] Switch the default version of the reference manual on the website.

## At the patch-level release time ##

We generally do not update the magic numbers at this point (see
[`2881a18`](https://github.com/coq/coq/commit/2881a18)).
