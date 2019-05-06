# Merging changes in Coq

This document describes how patches, submitted as pull requests (PRs) on the
`master` branch, should be merged into the main repository
(https://github.com/coq/coq).

## Code owners

The [CODEOWNERS](../../.github/CODEOWNERS) file defines owners for each part of
the code. Sometime there is one principal maintainer and one or several
secondary maintainer(s). Sometimes, it is a team of code owners and all of its
members act as principal maintainers for the component.

When a PR is submitted, GitHub will automatically ask the principal
maintainer (or the code owner team) for a review. If the PR touches several
parts, all the corresponding owners will be asked for a review.

Maintainers are never assigned as reviewer on their own PRs.

If a principal maintainer submits a PR or is a co-author of a PR that is
submitted and this PR changes the component they own, they must request a
review from a secondary maintainer. They can also delegate the review if they
know they are not available to do it.

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

To know what files you are a code owner of in a large PR, you can run
`dev/tools/check-owners-pr.sh xxxx`. Results are unfortunately imperfect.

When a PR received lots of comments or if the PR has not been opened for long
and the assignee thinks that some other developers might want to comment,
it is recommended that they announce their intention to merge and wait a full
working day (or more if deemed useful) before the actual merge, as a sort of
last call for comments.

In all cases, maintainers can delegate reviews to the other maintainers,
except if it would lead to a maintainer reviewing their own patch.

A maintainer is expected to be reasonably reactive, but no specific timeframe is
given for reviewing.

When none of the maintainers have commented nor self-assigned a PR in a delay
of five working days, any maintainer of another component who feels comfortable
reviewing the PR can assign it to themselves. To prevent misunderstandings,
maintainers should not hesitate to announce in advance when they shall be
unavailable for more than five working days.

(*) In case a component is touched in a trivial way (adding/removing one file in
a `Makefile`, etc), or by applying a systematic refactoring process (global
renaming for instance) that has been reviewed globally, the assignee can
say in a comment they think a review is not required from every code owner and
proceed with the merge.

### Breaking changes

If the PR breaks compatibility of some external projects in CI, then fixes to
those external projects should have been prepared (cf. the relevant sub-section
in the [CI README](../ci/README.md#Breaking-changes) and the PR can be tested
with these fixes thanks to ["overlays"](../ci/user-overlays/README.md).

Moreover the PR author *must* add an entry to the [unreleased
changelog](../../doc/changelog/README.md) or to the
[`dev/doc/changes.md`](changes.md) file.

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
To restart a job on AppVeyor, you should connect using your GitHub
account; being part of the Coq organization on GitHub should give you the
permission to do so.
To restart a job on GitLab CI, you should sign into GitLab (this can be done
using a GitHub account); if you are part of the
[Coq organization on GitLab](https://gitlab.com/coq), you should see a "Retry"
button; otherwise, send a request to join the organization.

When the PR has conflicts, the assignee can either:
- ask the author to rebase the branch, fixing the conflicts
- warn the author that they are going to rebase the branch, and push to the
  branch directly

In both cases, CI should be run again.

In some rare cases (e.g. the conflicts are in the `CHANGES.md` file and the PR
is not a candidate for backporting), it is ok to fix
the conflicts in the merge commit (following the same steps as below), and push
to `master` directly. DON'T USE the GitHub interface to fix these conflicts.

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

## Addendum for organization admins

### Adding a new code owner individual

If someone is added to the [`CODEOWNERS`](../../.github/CODEOWNERS) file and
they did not have merging rights before, they should also be added to the
**@coq/pushers** team. You may do so using
[this link](https://github.com/orgs/coq/teams/pushers/members?add=true).

Before adding someone to the **@coq/pushers** team, you should ensure that they
have read the present merging documentation, and explicitly tell them not to
use the merging button on the GitHub web interface.

### Adding a new code owner team

Go to [that page](https://github.com/orgs/coq/teams/pushers/teams) and click on
the green "Add a team" button. Use a "-maintainer" suffix for the name of your
team. You may then add new members to this team (you don't need to add them to
the **@coq/pushers** team first as this will be done automatically because the
team you created is a sub-team of **@coq/pushers**).
