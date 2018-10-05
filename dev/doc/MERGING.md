# Merging changes in Coq

This document describes how patches, submitted as pull requests (PRs) on the
`master` branch, should be merged into the main repository
(https://github.com/coq/coq).

## Code owners

The [CODEOWNERS](../../.github/CODEOWNERS) file describes, for each part of the
system, two owners. One is the principal maintainer of the component, the other
is the secondary maintainer.

When a PR is submitted, GitHub will automatically ask the principal
maintainer for a review. If the PR touches several parts, all the
corresponding principal maintainers will be asked for a review.

Maintainers are never assigned as reviewer on their own PRs.

If a principal maintainer submits a PR that changes the component they own, they
must assign the secondary maintainer as reviewer. They should also do it if they
know they are not available to do the review.

## Reviewing

When maintainers receive a review request, they are expected to:

* Put their name in the assignee field, if they are in charge of the component
  that is the main target of the patch (or if they are the only maintainer asked
  to review the PR).
* Review the PR, approve it or request changes.
* If they are the assignee, check if all reviewers approved the PR. If not,
  regularly ping the author (if changes should be implemented) or the reviewers
  (if reviews are missing). The assignee ensures that any requests for more
  discussion have been granted. When the discussion has converged and ALL
  REVIEWERS(*) have approved the PR, the assignee is expected to follow the merging
  process described below.

In all cases, maintainers can delegate reviews to the other maintainer of the
same component, except if it would lead to a maintainer reviewing their own
patch.

A maintainer is expected to be reasonably reactive, but no specific timeframe is
given for reviewing.

(*) In case a component is touched in a trivial way (adding/removing one file in
a `Makefile`, etc), or by applying a systematic refactoring process (global
renaming for instance) that has been reviewed globally, the assignee can
say in a comment they think a review is not required and proceed with the merge.

### Breaking changes

If the PR breaks compatibility of some external projects in CI, then fixes to
those external projects should have been prepared (cf. the relevant sub-section
in the [CI README](../ci/README.md#Breaking-changes) and the PR can be tested
with these fixes thanks to ["overlays"](../ci/user-overlays/README.md).

Moreover the PR must absolutely update the [`CHANGES.md`](../../CHANGES.md) file.

If overlays are missing, ask the author to prepare them and label the PR with
the [needs: overlay](https://github.com/coq/coq/labels/needs%3A%20overlay) label.

When fixes are ready, there are two cases to consider:

- For patches that are backward compatible (best scenario), you should get the
  external project maintainers to integrate them before merging the PR.
- For patches that are not backward compatible (which is often the case when
  patching plugins after an update to the Coq API), you can proceed to merge
  the PR and then notify the external project maintainers they can merge the
  patch.

## Merging

Once all reviewers approved the PR, the assignee is expected to check that CI
completed without relevant failures, and that the PR comes with appropriate
documentation and test cases. If not, they should leave a comment on the PR and
put the approriate label. Otherwise, they are expected to merge the PR using the
[merge script](../tools/merge-pr.sh).

When CI has a few failures which look spurious, restarting the corresponding
jobs is a good way of ensuring this was indeed the case.
To restart a job on Travis, you should connect using your GitHub account;
being part of the Coq organization on GitHub should give you the permission
to do so.
To restart a job on GitLab CI, you should sign into GitLab (this can be done
using a GitHub account); if you are part of the
[Coq organization on GitLab](https://gitlab.com/coq), you should see a "Retry"
button; otherwise, send a request to join the organization.

When the PR has conflicts, the assignee can either:
- ask the author to rebase the branch, fixing the conflicts
- warn the author that they are going to rebase the branch, and push to the
  branch directly

In both cases, CI should be run again.

In some rare cases (e.g. the conflicts are in the `CHANGES.md` file), it is ok to fix
the conflicts in the merge commit (following the same steps as below), and push
to `master` directly. Don't use the GitHub interface to fix these conflicts.

To merge the PR proceed in the following way
```
$ git checkout master
$ git pull
$ dev/tools/merge-pr.sh XXXX
$ git push upstream
```
where `XXXX` is the number of the PR to be merged and `upstream` is the name
of your remote pointing to `git@github.com:coq/coq.git`.
Note that you are only supposed to merge PRs into `master`. PRs should rarely
target the stable branch, but when it is the case they are the responsibility
of the release manager.

This script conducts various checks before proceeding to merge. Don't bypass them
without a good reason to, and in that case, write a comment in the PR thread to
explain the reason.

Maintainers MUST NOT merge their own patches.

DON'T USE the GitHub interface for merging, since it will prevent the automated
backport script from operating properly, generates bad commit messages, and a
messy history when there are conflicts.

### Merge script dependencies

The merge script passes option `-S` to `git merge` to ensure merge commits
are signed. Consequently, it depends on the GnuPG command utility being
installed and a GPG key being available. Here is a short documentation on
how to use GPG, git & GitHub: https://help.github.com/articles/signing-commits-with-gpg/.

The script depends on a few other utilities. If you are a Nix user, the
simplest way of getting them is to run `nix-shell` first.

**Note for homebrew (MacOS) users:** it has been reported that installing GnuPG
is not out of the box. Installing explicitly "pinentry-mac" seems important for
typing of passphrase to work correctly (see also this
[Stack Overflow Q-and-A](https://stackoverflow.com/questions/39494631/gpg-failed-to-sign-the-data-fatal-failed-to-write-commit-object-git-2-10-0)).
