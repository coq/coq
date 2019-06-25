# Guide to contributing to Coq #

## Foreword ##

As any piece of code or documentation, this guide can bitrot if people
forget to update it when contributing processes, development tools, or
the Coq ecosystem changes.  If you notice anything inaccurate or
outdated, please signal it in a new issue, or fix it in a new pull
request.

## Table of contents ##

- [Introduction](#introduction)
- [Contributing to the ecosystem](#contributing-to-the-ecosystem)
  - [Asking and answering questions](#asking-and-answering-questions)
  - [Writing tutorials and blog posts](#writing-tutorials-and-blog-posts)
  - [Creating and maintaining Coq packages](#creating-and-maintaining-coq-packages)
    - [Distribution](#distribution)
    - [Support](#support)
    - [Standard libraries](#standard-libraries)
    - [Maintaining existing packages](#maintaining-existing-packages)
  - [Contributing to the wiki](#contributing-to-the-wiki)
  - [Contributing to the website or the package archive](#contributing-to-the-website-or-the-package-archive)
  - [Other ways of creating content](#other-ways-of-creating-content)
- [Issues](#issues)
  - [Reporting a bug, requesting an enhancement](#reporting-a-bug-requesting-an-enhancement)
  - [Helping triage existing issues](#helping-triage-existing-issues)
- [Code changes](#code-changes)
  - [Using GitHub pull requests](#using-github-pull-requests)
  - [Taking feedback into account](#taking-feedback-into-account)
    - [Understanding automatic feedback](#understanding-automatic-feedback)
    - [Understanding reviewers' feedback](#understanding-reviewers-feedback)
    - [Fixing your branch](#fixing-your-branch)
  - [Improving the official documentation](#improving-the-official-documentation)
  - [Contributing to the standard library](#contributing-to-the-standard-library)
  - [Fixing bugs and performing small changes](#fixing-bugs-and-performing-small-changes)
  - [Proposing large changes: Coq Enhancement Proposals](#proposing-large-changes-coq-enhancement-proposals)
  - [Collaborating on a pull request](#collaborating-on-a-pull-request)
- [Becoming a maintainer](#becoming-a-maintainer)
  - [Reviewing pull requests](#reviewing-pull-requests)
  - [Merging pull requests](#merging-pull-requests)
  - [Core development team](#core-development-team)
- [Release management](#release-management)
  - [Packaging](#packaging)
- [Additional resources](#additional-resources)
  - [Developer documentation](#developer-documentation)
    - [Where to find the resources](#where-to-find-the-resources)
    - [Building Coq](#building-coq)
    - [Continuous integration](#continuous-integration)
    - [Code owners, issue and pull request templates](#code-owners-issue-and-pull-request-templates)
    - [Style guide](#style-guide)
    - [OCaml resources](#ocaml-resources)
    - [Git documentation, tips and tricks](#git-documentation-tips-and-tricks)
    - [GitHub documentation, tips and tricks](#github-documentation-tips-and-tricks)
    - [GitLab documentation, tips and tricks](#gitlab-documentation-tips-and-tricks)
    - [Coqbot](#coqbot)
  - [Online forum and chat to talk to developers](#online-forum-and-chat-to-talk-to-developers)
  - [Coq remote working groups](#coq-remote-working-groups)
  - [Coq Users and Developers Workshops](#coq-users-and-developers-workshops)

## Introduction ##

Thank you for your interest in contributing to Coq!  There are many
ways to contribute, and we appreciate all of them.

It is frequent to see a pattern where people start with small
contributions, and contributions to the ecosystem, before working
incrementally their way up to the core parts of the system, and start
to propose larger changes, or take an active role in maintaining the
system.  So this is the way this contributing guide is organized.
However, it is by no means a way of saying that you should go through
these steps in this order.  Feel free to use this guide as a reference
and quickly jump to the part that is most relevant to you at the
current time.

We want to make sure that contributing to Coq is a fun and positive
experience for everyone, so please make sure you read and abide by our
[Code of Conduct][Code-of-conduct].

## Contributing to the ecosystem ##

### Asking and answering questions ###

One very important way of contributing is by asking and answering
questions, in order to create a body of easily-browsable,
problem-oriented, additional documentation.

There are two main platforms for this purpose:

- [Stack Overflow][Stack-Overflow] (or more generally the [Stack
  Exchange][Stack-Exchange] platforms, as some Coq questions may be
  asked on other sites, such as TCS Stack Exchange);
- Our [Discourse forum][Discourse].

In particular, our Discourse forum has several non-English categories
that have yet to find their public, so do not hesitate to advertize
them to people you know who might not be at ease with English.

Other active places to answer questions include the [Coq-Club][]
mailing list, and the Coq IRC channel (`irc://irc.freenode.net/#coq`).

### Writing tutorials and blog posts ###

Writing about Coq, in the form of tutorials or blog posts, is also a
very important contribution.  In particular, it can help new users get
interested in Coq, and learn about it, and existing users learn about
advance features.  Our official resources, such as the [reference
manual][refman] are not suited for learning Coq, but serve as
reference documentation to which you can link from your tutorials.

The Coq website has a page listing known
[tutorials][Coq-documentation] and the [wiki][] home page contains a
list too.  You can expand the former through a pull request on the
[Coq website repository][Coq-website-repository], while the latter can
be edited directly by anyone with a GitHub account.

At the current time, we do not have a way of aggregating blog posts on
a single page (like [OCaml planet][OCaml-planet]), but this would
probably be something useful to get, so do not hesitate if you want to
create it.  Some people use [Reddit][] for this purpose.

### Creating and maintaining Coq packages ###

*Nota: this section is about packages extending Coq, such as plugins
or libraries.  A different, but also very valuable, contribution is to
package Coq for your preferred package manager (see
[Packaging](#packaging)).*

Sharing reusable assets in the form of new libraries, plugins, and
tools is great so that others can start building new things on top.
Having an extensive and healthy package ecosystem will be key to the
success of Coq.

#### Distribution ####

You can distribute your library or plugin through the [Coq package
index][Coq-package-index].  Tools can be advertised on the [tools
page][tools-website] of the Coq website, or the [tools
page][tools-wiki] of the wiki.

#### Support ####

You can find advice and best practices about maintaining a Coq project
on the [coq-community wiki][coq-community-wiki].

Learn how to write a Coq plugin, and about best practices, in the Coq
[plugin tutorial][plugin-tutorial].  This tutorial is still a work in
progress, so do not hesitate to expand it, or ask questions.

If you want quick feedback on best practices, or how to talk to the
Coq API, a good place to hang out is the Coq [Gitter channel][Gitter].

Finally, we strongly encourage authors of plugins to submit their
plugins to join Coq's continuous integration (CI) early on.  Indeed,
the Coq API gets continously reworked, so this is the best way of
ensuring your plugin stays compatible with new Coq versions, as this
means Coq developers will fix your plugin for you.  Learn more about
this in the [CI README (user part)][CI-README-users].

Pure Coq libraries are also welcome to join Coq's CI, especially if
they test underused / undertested features.

#### Standard libraries ####

There are many general purposes Coq libraries, so before you publish
yours, consider whether you could contribute to an existing one
instead (either the official [standard
library](#contributing-to-the-standard-library), or one of the many
[alternative standard libraries][other-standard-libraries]).

#### Maintaining existing packages ####

Some Coq packages are not maintained by their initial authors anymore
(for instance because they changed jobs, or lost interest) even if
they were useful, or interesting.  The coq-community organization is a
place for volunteers to take over the maintenance of such packages.

If you want to contribute by becoming a maintainer, there is [a list
of packages waiting for a
maintainer][coq-community-maintainer-wanted].  You can also propose a
package that is not listed.  Find out more about coq-community in [the
manifesto's README][coq-community-manifesto].

### Contributing to the wiki ###

Coq's [wiki][] is an informal source of additional documentation which
anyone with a GitHub account can edit directly.  In particular, it
contains the Coq [FAQ][] which has not seen so many updates in the
recent years.  You should feel free to fix it, expand it, and even
refactor it (if you are not sure if some changes would be welcome, you
can open an issue to discuss them before performing them).

People who watch the Coq repository will see recent wiki edits in
their GitHub feed.  It is recommended to review them *a posteriori* to
check no mistake was introduced.  The wiki is also a standard git
repository, so people can follow the changes using any standard git
tool.

Coq's wiki is formatted using GitHub's flavored Markdown, with some
wiki-specific extensions.  See:

- [GitHub's Markdown guide][GitHub-markdown]
- [GitHub's wiki extensions][GitHub-wiki-extensions]

### Contributing to the website or the package archive ###

The website and the package archive have their own repositories:

- <https://github.com/coq/www>
- <https://github.com/coq/opam-coq-archive>

You can contribute to them by using issues and pull requests on these
repositories.  These repositories should get their own contributing
guides, but they don't have any at the time of writing this.

### Other ways of creating content ###

There are many other ways of creating content and making the Coq
community strive, including many which we might not have thought
about.  Feel free to add more references / ideas to this sub-section.

You can tweet about Coq, you can give talks about Coq both in
academic, and in non-academic venues (such as developer conferences).

[Codewars][] is a platform where people can try to solve some
programming challenges that were proposed by other community members.
Coq is supported and the community is eager to get more challenges.

## Issues ##

### Reporting a bug, requesting an enhancement ###

Bug reports are enormously useful to identify issues with Coq; we
can't fix what we don't know about.  To report a bug, please open an
issue in the [Coq issue tracker][Coq-issue-tracker] (you'll need a
GitHub account).  You can file a bug for any of the following:

- An anomaly. These are always considered bugs, so Coq will even ask
  you to file a bug report!
- An error you didn't expect. If you're not sure whether it's a bug or
  intentional, feel free to file a bug anyway. We may want to improve
  the documentation or error message.
- Missing documentation. It's helpful to track where the documentation
  should be improved, so please file a bug if you can't find or don't
  understand some bit of documentation.
- An error message that wasn't as helpful as you'd like. Bonus points
  for suggesting what information would have helped you.
- Bugs in CoqIDE should also be filed in the [Coq issue
  tracker][Coq-issue-tracker].  Bugs in the Emacs plugin should be
  filed against [ProofGeneral][ProofGeneral-issues], or against
  [company-coq][company-coq-issues] if they are specific to
  company-coq features.

It would help if you search the existing issues before reporting a
bug. This can be difficult, so consider it extra credit.  We don't
mind duplicate bug reports.  If unsure, you are always very welcome to
ask on our [Discourse forum][Discourse] or [Gitter chat][Gitter]
before, after, or while writing a bug report.

When it applies, it's extremely helpful for bug reports to include sample
code, and much better if the code is self-contained and complete. It's not
necessary to minimize your bug or identify precisely where the issue is,
since someone else can often do this if you include a complete example. We
tend to include the code in the bug description itself, but if you have a
very large input file then you can add it as an attachment.

If you want to minimize your bug (or help minimize someone else's) for
more extra credit, then you can use the [Coq bug
minimizer][JasonGross-coq-tools] (specifically, the bug minimizer is
the `find-bug.py` script in that repo).

### Helping triage existing issues ###

Coq has too many bug reports for its core developers alone to manage.
You can help a lot by:

- confirming that reported bugs are still active with the current
  version of Coq;
- determining if the bug is a regression (new, and unexpected,
  behavior from a recent Coq version);
- more generally, by reproducing a bug, on another system,
  configuration, another version of Coq, and by documenting what you
  did;
- giving a judgement about whether the reported behavior is really a
  bug, or is expected but just improperly documented, or expected and
  already documented;
- producing a trace if it is relevant and you know how to do it;
- producing another example exhibiting the same bug, or minimizing the
  initial example using the bug minimizer mentioned above;
- using `git bisect` to find the commit that introduced a regression;
- fixing the bug if you have an idea of how to do so (see the
  following section).

Once you have some experience with the Coq issue tracker, you can
request to join the **@coq/contributors** team (any member of the
**@coq/core** team can do so using [this link][add-contributor]).
Being in this team will grant you the following access:

- **Updating labels:** every open issue and pull request should
  ideally get one or several `kind:` and `part:` labels.  In
  particular, valid issues should generally get either a `kind: bug`
  (the reported behavior can indeed be considered a bug, this can be
  completed with the `kind: anomaly`, and `kind: regression` labels),
  `kind: documentation` (e.g. if a reported behavior is expected but
  improperly documented), `kind: enhancement` (a request for
  enhancement of an existing feature), or `kind: feature` label (an
  idea for a new feature).
- **Creating new labels:** if you feel a `part:` label is missing, do
  not hesitate to create it.  If you are not sure, you may discuss it
  with other contributors and developers on [Gitter][] first.
- **Closing issues:** if a bug cannot be reproduced anymore, is a
  duplicate, or should not be considered a bug report in the first
  place, you should close it.  When doing so, try putting an
  appropriate `resolved:` label to indicate the reason.  If the bug
  has been fixed already, and you know in which version, you can add a
  milestone to it, even a milestone that's already closed, instead of
  a `resolved:` label.  When closing a duplicate issue, try to add all
  the additional info that could be gathered to the original issue.
- **Editing issue titles:** you may want to do so to better reflect
  the current understanding of the underlying issue.
- **Editing comments:** feel free to do so to fix typos and formatting
  only (in particular, some old comments from the Bugzilla era or
  before are not properly formatted).  You may also want to edit the
  OP's initial comment (a.k.a. body of the issue) to better reflect
  the current understanding of the issue, especially if the discussion
  is long.  If you do so, only add to the original comment, and mark
  it clearly with an `EDITED by @YourNickname:`.
- **Hiding comments:** when the discussion has become too long, this
  can be done to hide irrelevant comments (off-topic, outdated or
  resolved sub-issues).
- **Deleting things:** just don't do it.  FWIW, core developers have
  access to an audit log where all delete actions are listed (among
  other things).
- **Pushing a branch or a tag to the main repository:** just don't do
  it.  We like to reserve the branches on the main repository for the
  development branch (`master`) and the stable branches (`v...`).  If
  you push a branch nonetheless, expect it to be deleted promptly and
  without notice.

Yet to be documented: use of priority, difficulty, `help wanted`, and
`good first issue` labels, of milestones, of assignments, and of
GitHub projects.

## Code changes ##

### Using GitHub pull requests ###

If you want to contribute a documentation update, bug fix or feature
yourself, pull requests (PRs) on the [GitHub
repository][coq-repository] are the way to contribute directly to the
Coq implementation (all changes, even the smallest changes from core
developers, go through PRs).  You will need to create a fork of the
repository on GitHub and push your changes to a new "topic branch" in
that fork (instead of using an existing branch name like `master`).

PRs should always target the `master` branch.  Make sure that your
copy of this branch is up-to-date before starting to do your changes,
and that there are no conflicts before submitting your PR.  If you
need to fix conflicts, we generally prefer that you rebase your branch
on top of `master`, instead of creating a merge commit.

If you are not familiar with `git` or GitHub, Sections [Git
documentation, tips and tricks](#git-documentation-tips-and-tricks),
and [GitHub documentation, tips and
tricks](#github-documentation-tips-and-tricks), should be helpful (and
even if you are, you might learn a few tricks).

Once you have submitted your PR, it may take some time to get
feedback, in the form of reviews from maintainers, and test results
from our continuous integration system.  Our code owner system will
automatically request reviews from relevant maintainers.  Then, one
maintainer should self-assign the PR (if that does not happen after a
few days, feel free to ping the maintainers that were requested a
review).  The PR assignee will then become your main point of contact
for handling the PR: they should ensure that everything is in order
and merge when it is the case (you can ping them if the PR is ready
from your side but nothing happens for a few days).

After your PR is accepted and merged, it may get backported to a
stable branch if relevant, and will eventually make it to a release.
You do not have to worry about this, it is the role of the assignee
and the release manager to do so.  The milestone should give you an
indication of when to expect your change to be released (this could be
several months after your PR is merged).  That said, you can start
using the latest Coq `master` branch to take advantage of all the new
features, improvements, and fixes.

### Taking feedback into account ###

#### Understanding automatic feedback ####

When you open or update a PR, you get automatically some feedback: we
have a bot whose job will be to push a branch to our GitLab mirror to
run some continuous integration (CI) tests.  The tests will run on a
commit merging your branch with the base branch, so if there is a
conflict and this merge cannot be performed automatically, the bot
will put a `needs: rebase` label, and the tests won't run.

Otherwise, a large suite of tests will be run on GitLab, plus some
additional tests on Azure for Windows and macOS compatibility.

If a test fails on GitLab, you will see in the GitHub PR interface,
both the failure of the whole pipeline, and of the specific failed
job.  Most of these failures indicate problems that should be
addressed, but some can still be due to synchronization issues out of
your control.  In particular, if you get a failure in one of the
tested plugins but you didn't change the Coq API, it is probably a
transient issue and you shouldn't have to worry about it.  In case of
doubt, ask the reviewers.

##### Test-suite failures #####

If you broke the test-suite, you should get many failed jobs, because
the test-suite is run multiple times in various settings.  You should
get the same failure locally by running `make test-suite` or `make -f
Makefile.dune test-suite`.  It's helpful to run this locally and
ensure the test-suite is not broken before submitting a PR as this
will spare a lot of runtime on distant machines.

To learn more about the test-suite, you should refer to its
[README][test-suite-README].

##### Linter failures #####

We have a linter that checks a few different things:

- **Every commit can build.** This is an important requirement to
  allow the use of `git bisect` in the future.  It should be possible
  to build every commit, and in principle even the test-suite should
  pass on every commit (but this isn't tested in CI because it would
  take too long).  You can test and fix this locally with `git
  rebase`.
- **No tabs or end-of-line spaces on updated lines** (and all files
  should end with a single newline).  We are trying to get rid of all
  tabs (except in the `Makefile`s) and all end-of-line spaces from the
  code base.  This checks not only that you didn't introduce new ones,
  but also that updated lines are clean (even if they were there
  before).  You can avoid worrying about this issue completely by
  installing our [pre-commit git hook][git-hook], which will fix these
  issues at commit time.  Running `./configure` once will install this
  hook automatically unless you already have a pre-commit hook
  installed.  If you are encountering this issue nonetheless, you can
  fix it by rebasing your branch with `git rebase --whitespace=fix`.

You may run the linter yourself with `dev/lint-repository.sh`.

##### Plugin failures #####

If you did change the Coq API, then you may have broken a plugin.
After ensuring that the failure comes from your change, you will have
to provide a fix to the plugin, and the PR assignee will have to
ensure that this fix is merged in the plugin simultaneously with your
PR on the Coq repository.

If your changes to the API are not straightforward, you should also
document them in `dev/doc/changes.md`.

The [CI README (developer part)][CI-README-developers] contains more
information on how to fix plugins, test and submit your changes, and
how you can anticipate the results of the CI before opening a PR.

##### Library failures #####

Such a failure can indicate either a bug in your branch, or a breaking
change that you introduced voluntarily.  All such breaking changes
should be properly documented in the [user changelog][user-changelog].
Furthermore, a backward-compatible fix should be found, and this fix
should be merged in the broken projects *before* your PR to the Coq
repository can be.  You can use the same documentation as above to
learn about testing and fixing locally the broken libraries.

#### Understanding reviewers' feedback ####

The reviews you get are highly dependent on the kind of changes you
did.  In any case, you should always remember that reviewers are
friendly volunteers that do their best to help you get your changes in
(and should abide by our [Code of Conduct][Code-of-Conduct]).  But at
the same time, they try to ensure that code that is introduced or
updated is of the highest quality and will be easy to maintain in the
future, and that's why they may ask you to perform small or even large
changes.  If you need a clarification, do not hesitate to ask.

Here are a few labels that reviewers may add to your PR to track its
status.  In general, this will come in addition to comments from the
reviewers, with specific requests.

- [needs: rebase][needs-rebase] indicates the PR should be rebased on
  top of the latest version of the base branch (usually `master`).  We
  generally ask you to rebase only when there are merge conflicts or
  if the PR has been opened for a long time and we want a fresh CI
  run.
- [needs: fixing][needs-fixing] indicates the PR needs a fix, as
  discussed in the comments.
- [needs: documentation][needs-documentation] indicates the PR
  introduce changes that should be documented before it can be merged.
- [needs: changelog entry][needs-changelog] indicates the PR introduce
  changes that should be documented in the [user
  changelog][user-changelog].
- [needs: benchmarking][needs-benchmarking] and [needs: testing][needs-testing]
  indicate the PR needs testing beyond what the test suite can handle.
  For example, performance benchmarking is currently performed with a different
  infrastructure ([documented in the wiki][jenkins-doc]). Unless some followup
  is specifically requested, you aren't expected to do this additional testing.

More generally, such labels should come with a description that should
allow you to understand what they mean.

#### Fixing your branch ####

If you have changes to perform before your PR can be merged, you might
want to do them in separate commits at first to ease the reviewers'
task, but we generally appreciate that they are squashed with the
commits that they fix before merging.  This is especially true of
commits fixing previously introduced bugs or failures.

### Improving the official documentation ###

The documentation is usually a good place to start contributing,
because you can get used to the pull request submitting and review
process, without needing to learn about the code source of Coq at the
same time.

The official documentation is formed of two components:

- the [reference manual][refman],
- the [documentation of the standard library][stdlib-doc].

The sources of the reference manual are located in the
[`doc/sphinx`][refman-sources] directory.  They are written in rst
(Sphinx) format with some Coq-specific extensions, which are
documented in the [README][refman-README] in the above directory.
This README was written to be read from begin to end.  As soon as your
edits to the documentation are more than changing the textual content,
we strongly encourage you to read this document.

The documentation of the standard library is generated with
[coqdoc][coqdoc-documentation] from the comments in the sources of the
standard library.

The [README in the `doc` directory][doc-README] contains more
information about the documentation's build dependencies, and the
`make` targets.

You can browse through the list of open documentation issues using the
[kind: documentation][kind-documentation] label, or the [user
documentation GitHub project][documentation-github-project] (you can
look in particular at the "Writing" and "Fixing" columns).

### Contributing to the standard library ###

Contributing to the standard library is also made easier by not having
to learn about Coq's internals, and its implementation language.

However, you should be aware that, because of the age of the library,
and the compatibility constraints created by the many projects that
depend on it, proposing breaking changes, such as changing a
definition, might be frequently rejected, or at the very least might
take a long time before getting approved and merged.  This does not
mean that you cannot try.

There exists a [stdlib2][] project, that will be much more open to
compatibility-breaking changes once it starts accepting external
contributions.

In the meantime, contributing new lemmas on exisiting definitions
should be generally favorably accepted, cleaning up existing proofs as
well.  Contributing new operations on existing types is also likely to
be accepted in many cases.  In case of doubt, ask in an issue before
spending too much time preparing your PR.

If you create a new file, it needs to be listed in
`doc/stdlib/index-list.html`.

Add coqdoc comments to extend the [standard library
documentation][stdlib-doc].  See the [coqdoc
documentation][coqdoc-documentation] to learn more.

### Fixing bugs and performing small changes ###

Just open a PR with your fix.  If it is not yet completed, do not
hesitate to open a Work-in-Progress PR to get early feedback, and talk
to developers on [Gitter][].

It is generally a good idea to add a regression test to the
test-suite. See the test-suite [README][test-suite-README] for how to
do so.

Small fixes do not need any documentation, or changelog update.  New,
or updated, user-facing features, and major bug fixes do.  See above
on how to contribute to the documentation, and the README in
[`doc/changelog`][user-changelog] for how to add a changelog entry.

### Proposing large changes: Coq Enhancement Proposals ###

You are always welcome to open a PR for a change of any size.
However, you should be aware that the larger the change, the higher
the chances it will take very long to review, and possibly never get
merged.

So it is recommended that before spending a lot of time coding, you
seek feedback from maintainers to see if your change would be
supported, and if they have recommendation about its implementation.
You can do this informally by opening an issue, or more formally by
producing a design document as a [Coq Enhancement Proposal][CEP].

Another recommendation is that you do not put several unrelated
changes (even if you produced them together) in the same PR.  Spliting
out what can be to smaller-scale PRs is the best way to ensure that
your changes are reviewed and merged promptly.

### Collaborating on a pull request ###

Beyond making suggestions to a PR author during the review process,
you may want to collaborate further by checking out the code, making
changes, and pushing them.  There are two main ways of doing this:

- **Pull requests on pull requests:** You can checkout the PR branch
  (GitHub provides the link to the remote to pull from and the branch
  name on the top and the bottom of the PR discussion thread),
  checkout a new personal branch from there, do some changes, commit
  them, push to your fork, and open a new PR on the PR author's fork.
- **Pushing to the PR branch:** If the PR author has not unchecked the
  "Allow edit from maintainers" checkbox, and you have write-access to
  the repository (i.e. you are in the **@coq/contributors** team),
  then you can also push (and even force-push) directly to the PR
  branch, on the main author's fork.  Obviously, don't do it without
  coordinating with the PR author first (in particular, in case you
  need to force-push).

When several people have co-authored a single commit (e.g. because
someone fixed something in a commit initially authored by someone
else), this should be reflected by adding ["Co-authored-by:"
tags][GitHub-co-authored-by] at the end of the commit message.  The
line should contain the co-author name and committer e-mail address.

## Becoming a maintainer ##

### Reviewing pull requests ###

You can start reviewing PRs as soon as you feel comfortable doing so.
Reviewers should ensure that the code that is changed or introduced is
in good-shape and will not be a burden to maintain, is unlikely to
break anything, or the compatibility-breakage has been identified and
validated, includes documentation, changelog entries, and test files
when necessary.  Reviewers can use labels, or change requests to
further emphasize what remains to be changed before they can approve
the PR.  Once reviewers are satisfied (regarding the part they
reviewed), they should formally approve the PR, possibly stating what
they reviewed.

That being said, reviewers should also make sure that they do not make
the contributing process harder than necessary: they should make it
clear which comments are really required to perform before approving,
and which are just suggestions.  They should strive to reduce the
number of rounds of feedback that are needed by posting most of their
comments at the same time.  If they are opposed to the change, they
should clearly say so from the beginning to avoid the contributor
spending time in vain.

### Merging pull requests ###

Our [CODEOWNERS][] file associates a team of maintainers, or a
principal and secondary maintainers, to each component.  They will be
responsible for self-assigning and merging PRs (they didn't co-author)
that change this component.  When several components are changed in
significant ways, at least a maintainer (other than the PR author)
must approve the PR for each affected component before it can be
merged, and one of them has to assign the PR, and merge it when it is
time.  Before merging, the assignee must also select a milestone for
the PR (see also Sec. [Release Management](#release-management)).

If you feel knowledgeable enough to maintain a component, and have a
good track record of contributing to it, we would be happy to have you
join one of the maintainer teams.

The merging process is described in more details in [this
document][MERGING].

The people with merging powers (either because listed as a principal
or secondary maintainer in [CODEOWNERS][], or because member of a
maintainer team), are the members of the **@coq/pushers** team.

### Core development team ###

The core developers are the active developers with a lengthy and
significant contribution track record.  They are the ones with admin
powers over the Coq organization, and the ones who take part in votes
in case of conflicts to take a decision (rare).  One of them is
designated as a development coordinator, and has to approve the
changes in the core team membership (until we get a more formal
joining and leaving process).

The core developers are the members of the **@coq/core** team.

## Release management ##

Coq's major release cycles generally span about six months, with about
4-5 months of development, and 1-2 months of stabilization /
beta-releases.  The release manager (RM) role is a rolling position
among core developers.

Development of new features, refactorings, deprecations and clean-ups
always happens on `master`.  Stabilization starts by branching
(creating a new stable `v...` branch from the current `master`), which
marks the beginning of a feature freeze (new features will continue to
be merged into `master` but won't make it for the upcoming major
release, but only for the next one).

After branching, most changes are introduced in the stable branch by a
backporting process.  PR authors and assignee can signal intent of
having a PR backported or not by selecting an appropriate milestone.
Most of the time, the choice of milestone is between two options: the
next major version that has yet to branch from `master`, or the next
version (beta, final, or patch-level release) of the active stable
branch.  In the end, it is the RM who decides whether to follow or not
the recommendation of the PR assignee, and who backports PRs to the
stable branch.

Very specific changes that are only relevant for the stable branch and
not for the `master` branch can result in a PR targetting the stable
branch instead of `master`.  In this case, the RM is the only one who
can merge the PR, and they may even do so if they are the author of
the PR.  Examples of such PRs include bug fixes to a feature that has
been removed in `master`, and PRs from the RM changing the version
number in preparation for the next release.

Some automation is in place to help the RM in their task: a GitHub
project is created at branching time to manage PRs to backport; when a
PR is merged in a milestone corresponding to the stable branch, our
bot will add this PR in a "Request inclusion" column in this project;
the RM can browse through the list of PRs waiting to be backported in
this column, possibly reject some of them by simply removing the PR
from the column (in which case, the bot will update the PR milestone),
and proceed to backport others; when a backported PR is pushed to the
stable branch, the bot moves the PR from the "Request inclusion"
column to a "Shipped" column.

More information about the RM tasks can be found in the [release
process checklist][RM-checklist].

### Packaging ###

The RM role does not include the task of preparing packages: the
Windows and macOS packages are auto-generated by our CI, while some
other people take care of packaging Coq for opam, Nix, and a number of
additional package managers.  We thank them for this.  If your
preferred package manager does not include Coq, you can contribute by
adding it in there.

## Additional resources ##

### Developer documentation ###

#### Where to find the resources ####

- You can find developer resources in the `dev` directory, and more
  specifically developer documentation in `dev/doc`. The
  [README][dev-README] in the `dev` directory lists what's available.

  For example, [`dev/doc/README.md`][dev-doc-README] is a beginner's
  guide to hacking Coq, and documentation on debugging Coq can be
  found in [`dev/doc/debugging.md`][debugging-doc].

- When it makes sense, the documentation is kept even closer to the
  sources, in README files in various directories (e.g. the test-suite
  [README][test-suite-README] or the refman [README][refman-README]).

- Documentation of the Coq API is written directly in comments in
  `.mli` files.  You can browse it on [the Coq website][api-doc], or
  rebuild it locally (`make -f Makefile.dune apidoc`, requires `odoc`
  and `dune`).

- A plugin tutorial is located in
  [`doc/plugin_tutorial`][plugin-tutorial].

- The Coq [wiki][] contains additional developer resources.

#### Building Coq ####

The list of dependencies can be found in the first section of the
[`INSTALL`](INSTALL) file.

Today, the recommended method for building Coq is to use `dune`.  Run
`make -f Makefile.dune` to get help on the various available targets,
Additional documentation can be found in
[`dev/doc/build-system.dune.md`][dev-doc-dune], and in [the official
Dune documentation][dune-doc].

The legacy make-based system is still available.  If you wish to use
it, you need to start by running `./configure -profile devel`.  Most
of the available targets are not documented, so you will need to ask.

#### Continuous integration ####

Continuous integration (CI) testing is key in ensuring that the
`master` branch is kept in a well-functioning state at all times, and
that no accidental compatibility breakages are introduced.  Our CI is
quite extensive since it includes testing many external projects, some
of them taking more than an hour to compile.  However, you can get
partial results much more quickly (when our CI is not overloaded).

The main documentation resources on our CI are:

- the [README for users, i.e. plugin and library authors][CI-README-users];
- the [README for developers, and contributors][CI-README-developers];
- the README of the [user-overlays][] directory.

Preparing an overlay is a step that everyone goes through at some
point.  All you need to know to prepare an overlay manually is in the
README in the [user-overlays][] directory.  You might
want to use some additional tooling such as the `make ci-*` targets of
`Makefile.ci`, the Nix support for getting the dependencies of the
external projects (see the README in [`dev/ci/nix`](dev-ci-nix), and
the (undocumented so far) `dev/tools/create_overlays.sh` script.

More work is to be done on understanding how each developer proceeds
to prepare overlays, and propose a simplified and documented
procedure.

We also have a benchmarking infrastructure, which is documented [on
the wiki][jenkins-doc].

#### Code owners, issue and pull request templates ####

These files can be found in the [`.github`](.github) directory.  The
templates are particularly useful to remind contributors what
information we need for them, and, in the case of PRs, to update the
documentation, changelog, and test-suite when relevant.

GitHub now supports setting up multiple issue templates, and we could
use this to define distinct requirements for various kind of bugs,
enhancement and feature requests.

#### Style guide ####

There exists an [old style guide][old-style-guide] whose content is
still mostly relevant.  We don't use a code formatter at the current
time, and we are reluctant to formatting-only commits, or commits
formatting parts of code that are unchanged beyond formatting.
However, it is still a good idea if you don't know how to format a
block to use the formatting that [ocamlformat][] would give

#### OCaml resources ####

You may find lots of OCaml resources on <http://ocaml.org/>, including
documentation, a Discourse forum, the package archive, etc.  You may
also want to refer to the [Dune documentation][dune-doc].

#### Git documentation, tips and tricks ####

Lots of resources about git, the version control system, are available
on the web, starting with the [official website][git].

We recommend a setup with two configured remotes, one for the official
Coq repository, called `upstream`, and one for your fork, called
`origin`.  Here is a way to do this for a clean clone:

``` shell
git clone https://github.com/coq/coq -o upstream
cd coq
git remote add origin git@github.com:$YOURNAME/coq
# Make sure you click the fork button on GitHub so that this repository exists
cp dev/tools/pre-commit .git/hooks/ # Setup the pre-commit hook
```

Then, if you want to prepare a fix:

``` shell
git checkout master
git pull # Make sure we start from an up-to-date master
git checkout -b my-topic-branch
# Modify some files
git add .
# Every untracked or modified file will be included in the next commit
# You can also replace the dot with an explicit list of files
git commit -m "My commit summary.

You can add more information on multiple lines,
but you need to skip a line first."
git push -u origin my-topic-branch
# Next time, you push to this branch, you can just do git push
```

When you push a new branch for the first time, GitHub gives you a link
to open a PR.

If you need to fix the last commit in your branch (typically, if your
branch has a single commit on top of `master`), you can do so with

```
git add .
git commit --amend --no-edit
```

If you need to fix another commit in your branch, or if you need to
fix a conflict with `master`, you will need to learn about `git rebase`.
GitHub provides [a short introduction][GitHub-rebase] to `git rebase`.

#### GitHub documentation, tips and tricks ####

GitHub has [extensive documentation][GitHub-doc] about everything you
can do on the platform, and tips about using `git` as well.  See in
particular, [how to make configure your commit e-mail
address][GitHub-commit-email] and [how to open a PR from a
fork][GitHub-PR-from-fork].

##### Watching the repository #####

["Watching" this repository][GitHub-watching] can result in a very
large number of notifications.  We recommend you, either, [configure
your mailbox][notification-email] to handle incoming notifications
efficiently, or you read your notifications within a web browser.  You
can configure how you receive notifications in [your GitHub
settings][GitHub-notification-settings], you can use the GitHub
interface to mark as read, save for later or mute threads.  You can
also manage your GitHub web notifications using a tool such as
[Octobox][].

#### GitLab documentation, tips and tricks ####

We use GitLab mostly for its CI service.  The [Coq organization on
GitLab][GitLab-coq] hosts a number of CI/CD-only mirrors.  If you are
a regular contributor, you can request access to this organization
(from the organization page): this will grant you permission to
restart failing CI jobs.

GitLab too has [extensive documentation][GitLab-doc], in particular on
configuring CI.

#### Coqbot ####

Our bot sources can be found at <https://github.com/coq/bot>.  Its
documentation is still a work-in-progress.

### Online forum and chat to talk to developers ###

We have a [Discourse forum][Discourse] (see in particular the [Coq
development category][Discourse-development-category]) and a [Gitter
chat][Gitter].  Feel free to join any of them and ask questions.
People are generally happy to help and very reactive.

Obviously, the issue tracker is also a good place to ask questions,
especially if the development processes are unclear, or the developer
documentation should be improved.

### Coq remote working groups ###

We semi-regularly (up to every month) organize remote working groups,
which can be accessed through video-conference, and are most often
live streamed on [YouTube][].  Summary notes and announcements of the
next working group can be found [on the wiki][wiki-WG]

These working groups are where important decisions are taken, most
often by consensus, but also, if it is needed, by a vote of core
developers.

### Coq Users and Developers Workshops ###

We have an annual gathering late Spring in France where most core
developers are present, and whose objective is to help new
contributors get started with the Coq codebase, provide help to plugin
and library authors, and more generally have fun together.

The list of past (and upcoming, when it's already planned) workshops
can be found [on the wiki][wiki-CUDW].

[add-contributor]: https://github.com/orgs/coq/teams/contributors/members?add=true
[api-doc]: https://coq.github.io/doc/master/api/
[CEP]: https://github.com/coq/ceps
[CI-README-developers]: dev/ci/README-developers.md
[CI-README-users]: dev/ci/README-users.md
[Code-of-Conduct]: CODE_OF_CONDUCT.md
[CODEOWNERS]: .github/CODEOWNERS
[Codewars]: https://www.codewars.com/?language=coq
[company-coq-issues]: https://github.com/cpitclaudel/company-coq/issues
[Coq-Club]: https://sympa.inria.fr/sympa/arc/coq-club
[coq-community-maintainer-wanted]: https://github.com/coq-community/manifesto/issues?q=is%3Aissue+is%3Aopen+label%3Amaintainer-wanted
[coq-community-manifesto]: https://github.com/coq-community/manifesto
[coq-community-wiki]: https://github.com/coq-community/manifesto/wiki
[coqdoc-documentation]: https://coq.inria.fr/refman/practical-tools/utilities.html#documenting-coq-files-with-coqdoc
[Coq-documentation]: https://coq.inria.fr/documentation
[Coq-issue-tracker]: https://github.com/coq/coq/issues
[Coq-package-index]: https://coq.inria.fr/packages
[coq-repository]: https://github.com/coq/coq
[Coq-website-repository]: https://github.com/coq/www
[debugging-doc]: dev/doc/debugging.md
[dev-doc-README]: dev/doc/README.md
[dev-doc-dune]: dev/doc/build-system.dune.md
[dev-README]: dev/README.md
[Discourse]: https://coq.discourse.group/
[Discourse-development-category]: https://coq.discourse.group/c/coq-development
[doc-README]: doc/README.md
[documentation-github-project]: https://github.com/coq/coq/projects/3
[dune-doc]: https://dune.readthedocs.io/en/latest/
[FAQ]: https://github.com/coq/coq/wiki/The-Coq-FAQ
[git]: https://git-scm.com/
[git-hook]: dev/tools/pre-commit
[GitHub-co-authored-by]: https://github.blog/2018-01-29-commit-together-with-co-authors/
[GitHub-commit-email]: https://help.github.com/en/articles/setting-your-commit-email-address-in-git
[GitHub-doc]: https://help.github.com/
[GitHub-markdown]: https://guides.github.com/features/mastering-markdown/
[GitHub-notification-settings]: https://github.com/settings/notifications
[GitHub-PR-from-fork]: https://help.github.com/en/articles/creating-a-pull-request-from-a-fork
[GitHub-rebase]: https://help.github.com/articles/about-git-rebase/
[GitHub-watching]: https://github.com/coq/coq/subscription
[GitHub-wiki-extensions]: https://help.github.com/en/articles/editing-wiki-content
[GitLab-coq]: https://gitlab.com/coq
[GitLab-doc]: https://docs.gitlab.com/
[Gitter]: https://gitter.im/coq/coq
[JasonGross-coq-tools]: https://github.com/JasonGross/coq-tools
[jenkins-doc]: https://github.com/coq/coq/wiki/Jenkins-(automated-benchmarking)
[kind-documentation]: https://github.com/coq/coq/issues?q=is%3Aopen+is%3Aissue+label%3A%22kind%3A+documentation%22
[MERGING]: dev/doc/MERGING.md
[needs-benchmarking]: https://github.com/coq/coq/labels/needs%3A%20benchmarking
[needs-changelog]: https://github.com/coq/coq/labels/needs%3A%20changelog%20entry
[needs-documentation]: https://github.com/coq/coq/labels/needs%3A%20documentation
[needs-fixing]: https://github.com/coq/coq/labels/needs%3A%20fixing
[needs-rebase]: https://github.com/coq/coq/labels/needs%3A%20rebase
[needs-testing]: https://github.com/coq/coq/labels/needs%3A%20testing
[notification-email]: https://blog.github.com/2017-07-18-managing-large-numbers-of-github-notifications/#prioritize-the-notifications-you-receive
[OCaml-planet]: http://ocaml.org/community/planet/
[ocamlformat]: https://github.com/ocaml-ppx/ocamlformat
[Octobox]: http://octobox.io/
[old-style-guide]: dev/doc/style.txt
[other-standard-libraries]: https://github.com/coq/stdlib2/wiki/Other-%22standard%22-libraries
[plugin-tutorial]: doc/plugin_tutorial
[ProofGeneral-issues]: https://github.com/ProofGeneral/PG/issues
[Reddit]: https://www.reddit.com/r/Coq/
[refman]: https://coq.inria.fr/refman
[refman-sources]: doc/sphinx
[refman-README]: doc/sphinx/README.rst
[RM-checklist]: dev/doc/release-process.md
[Stack-Exchange]: https://stackexchange.com/filters/299857/questions-tagged-coq-on-stackexchange-sites
[Stack-Overflow]: https://stackoverflow.com/questions/tagged/coq
[stdlib2]: https://github.com/coq/stdlib2
[stdlib-doc]: https://coq.inria.fr/stdlib/
[test-suite-README]: test-suite/README.md
[tools-website]: https://coq.inria.fr/related-tools.html
[tools-wiki]: https://github.com/coq/coq/wiki/Tools
[user-changelog]: doc/changelog
[user-overlays]: dev/ci/user-overlays
[wiki]: https://github.com/coq/coq/wiki
[wiki-CUDW]: https://github.com/coq/coq/wiki/CoqImplementorsWorkshop
[wiki-WG]: https://github.com/coq/coq/wiki/Coq-Working-Groups
[YouTube]: https://www.youtube.com/channel/UCbJo6gYYr0OF18x01M4THdQ
