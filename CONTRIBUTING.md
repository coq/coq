# Contributing to Coq

Thank you for your interest in contributing to Coq! There are many ways to
contribute, and we appreciate all of them. Please make sure you read and
abide by the [Code of Conduct](CODE_OF_CONDUCT.md).

## Bug Reports

Bug reports are enormously useful to identify issues with Coq; we can't fix
what we don't know about. To report a bug, please open an issue in the
[Coq issue tracker][] (you'll need a GitHub
account). You can file a bug for any of the following:

- An anomaly. These are always considered bugs, so Coq will even ask you to
  file a bug report!
- An error you didn't expect. If you're not sure whether it's a bug or
  intentional, feel free to file a bug anyway. We may want to improve the
  documentation or error message.
- Missing documentation. It's helpful to track where the documentation should
  be improved, so please file a bug if you can't find or don't understand some
  bit of documentation.
- An error message that wasn't as helpful as you'd like. Bonus points for
  suggesting what information would have helped you.
- Bugs in CoqIDE should also be filed in the
  [Coq issue tracker][].
  Bugs in the Emacs plugin should be filed against
  [ProofGeneral](https://github.com/ProofGeneral/PG/issues), or against
  [company-coq](https://github.com/cpitclaudel/company-coq/issues) if they are
  specific to company-coq features.

It would help if you search the existing issues before reporting a bug. This
can be difficult, so consider it extra credit. We don't mind duplicate bug
reports. If unsure, you are always very welcome to ask on our [Discourse forum][]
or [Gitter chat][] before, after, or while writing a bug report

When it applies, it's extremely helpful for bug reports to include sample
code, and much better if the code is self-contained and complete. It's not
necessary to minimize your bug or identify precisely where the issue is,
since someone else can often do this if you include a complete example. We
tend to include the code in the bug description itself, but if you have a
very large input file then you can add it as an attachment.

If you want to minimize your bug (or help minimize someone else's) for more
extra credit, then you can use the
[Coq bug minimizer](https://github.com/JasonGross/coq-tools) (specifically,
the bug minimizer is the `find-bug.py` script in that repo).

### Triaging bug reports

Triaging bug reports (adding labels, closing outdated / resolved bugs)
requires you to be granted some permissions. You may request members of the
**@coq/core** team to add you to the contributors team. They can do so using
this link: <https://github.com/orgs/coq/teams/contributors/members?add=true>.

## Pull requests

**Beginner's guide to hacking Coq: [`dev/doc/README.md`](dev/doc/README.md)** \
**Development information and tools: [`dev/README.md`](dev/README.md)**

If you want to contribute a bug fix or feature yourself, pull requests on
the [GitHub repository](https://github.com/coq/coq) are the way to contribute
directly to the Coq implementation. We recommend you create a fork of the
repository on GitHub and push your changes to a new "topic branch" in that
fork. From there you can follow the
[GitHub pull request documentation](https://help.github.com/articles/about-pull-requests/)
to get your changes reviewed and pulled into the Coq source repository.

Documentation for getting started with the Coq sources is located in various
files in [`dev/doc`](dev/doc) (for example, [debugging.md](dev/doc/debugging.md)).

Please make pull requests against the `master` branch.

If it's your first significant contribution to Coq (significant means: more
than fixing a typo), your pull request should include a commit adding your name
to the [`CREDITS`](CREDITS) file (possibly with the name of your
institution / employer if relevant to your contribution, an ORCID if you have
one —you may log into https://orcid.org/ using your institutional account to
get one—, and the year of your contribution).

It's helpful to run the Coq test suite with `make test-suite` before submitting
your change. Our CI runs this test suite and lots of other tests, including
building external Coq projects, on every pull request, but these results
take significantly longer to come back (on the order of a few hours). Running
the test suite locally will take somewhere around 10-15 minutes. Refer to
[`dev/ci/README-developers.md`](dev/ci/README-developers.md) for more
information on CI tests, including how to run them on your private branches.

If your pull request fixes a bug, please consider adding a regression test as
well. See [`test-suite/README.md`](test-suite/README.md) for how to do so.

If your pull request fixes a critical bug (a bug allowing a proof of `False`),
please add an entry to [`dev/doc/critical-bugs`](/dev/doc/critical-bugs).

Don't be alarmed if the pull request process takes some time. It can take a
few days to get feedback, approval on the final changes, and then a merge.
Do not hesitate to ping the reviewers if it takes longer than this.
Coq doesn't release new versions very frequently so it can take a few months
for your change to land in a released version. That said, you can start using
the latest Coq `master` branch to take advantage of all the new features,
improvements, and fixes.

Whitespace discipline (do not indent using tabs, no trailing spaces, text
files end with newlines) is checked by the `lint` job on GitLab CI (using
`git diff --check`). We ship a [`dev/tools/pre-commit`](/dev/tools/pre-commit)
git hook which fixes these errors at commit time. `configure` automatically
sets you up to use it, unless you already have a hook at `.git/hooks/pre-commit`.

Each commit in your pull request should compile (this makes bisecting
easier). The `lint` job checks compilation of the OCaml files, please
try to keep the rest of Coq in a functioning state as well.

You may run the linter yourself with `dev/lint-repository.sh`.

Here are a few tags Coq developers may add to your PR and what they mean. In
general feedback and requests for you as the pull request author will be in
the comments and tags are only used to organize pull requests.

- [needs: rebase][rebase-label] indicates the PR should be rebased on top of
  the latest base branch (usually `master`). See the
  [GitHub documentation](https://help.github.com/articles/about-git-rebase/)
  for a brief introduction to using `git rebase`.
  We generally ask you to rebase only when there are merge conflicts or if
  the PR has been opened for a long time and we want a fresh CI run.
- [needs: fixing][fixing-label] indicates the PR needs a fix, as discussed in the comments.
- [needs: benchmarking][benchmarking-label] and [needs: testing][testing-label]
  indicate the PR needs testing beyond what the test suite can handle.
  For example, performance benchmarking is currently performed with a different
  infrastructure ([documented in the wiki][jenkins-doc]). Unless some followup
  is specifically requested you aren't expected to do this additional testing.

To learn more about the merging process, you can read the
[merging documentation for Coq maintainers](dev/doc/MERGING.md).

[rebase-label]: https://github.com/coq/coq/pulls?utf8=%E2%9C%93&q=is%3Aopen%20is%3Apr%20label%3A%22needs%3A%20rebase%22
[fixing-label]: https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+fixing%22
[benchmarking-label]: https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+benchmarking%22
[testing-label]: https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+testing%22

[jenkins-doc]: https://github.com/coq/coq/wiki/Jenkins-(automated-benchmarking)

## Documentation

Currently the process for contributing to the documentation is the same as
for changing anything else in Coq, so please submit a pull request as
described above.

Our issue tracker includes a flag to mark bugs related to documentation.
You can view a list of documentation-related bugs using a
[GitHub issue search](https://github.com/coq/coq/issues?q=is%3Aopen+is%3Aissue+label%3A%22kind%3A+documentation%22).
Many of these bugs can be fixed by contributing writing, without knowledge
of Coq's OCaml source code.

The sources for the [Coq reference manual](https://coq.inria.fr/distrib/current/refman/)
are at [`doc/sphinx`](/doc/sphinx). These are written in reStructuredText
and compiled to HTML and PDF with [Sphinx](http://www.sphinx-doc.org/).

You will find information on how to build the documentation in
[`doc/README.md`](doc/README.md) and information about the specificities of
the Coq Sphinx format in [`doc/sphinx/README.rst`](doc/sphinx/README.rst).

You may also contribute to the informal documentation available in
[Cocorico](https://github.com/coq/coq/wiki) (the Coq wiki), and the
[Coq FAQ](https://github.com/coq/coq/wiki/The-Coq-FAQ). Both of these are
editable by anyone with a GitHub account.

## Where to get help (with the Coq source code, or anything else)

We have a [Discourse forum][] (see in particular the [Coq development category][])
and a [Gitter chat][]. Feel free to join any of them and ask questions.
People are generally happy to help and very reactive.

[Coq development category]: https://coq.discourse.group/c/coq-development

## Watching the repository

["Watching" this repository](https://github.com/coq/coq/subscription)
can result in a very large number of notifications. We advise that if
you do, either [configure your mailbox](https://blog.github.com/2017-07-18-managing-large-numbers-of-github-notifications/#prioritize-the-notifications-you-receive)
to handle incoming notifications efficiently, or you read your
notifications within a web browser. You can configure how you receive
notifications in [your GitHub settings](https://github.com/settings/notifications),
you can use the GitHub interface to mark as read, save for later or
mute threads.  You can also manage your GitHub web notifications using
a tool such as [Octobox](http://octobox.io/).

## Contributing outside this repository

There are many useful ways to contribute to the Coq ecosystem that don't
involve the Coq repository.

Tutorials to teach Coq, and especially to teach particular advanced features,
are much appreciated. Some tutorials are listed on the
[Coq website](https://coq.inria.fr/documentation). If you would like to add
a link to this list, please make a pull request against the Coq website
repository at <https://github.com/coq/www>.

External plugins / libraries contribute to create a successful ecosystem
around Coq. If your external development is mature enough, you may consider
submitting it for addition to our CI tests. Refer to
[`dev/ci/README-users.md`](dev/ci/README-users.md) for more information.

Some Coq packages are not maintained by their authors anymore even if they
were useful (for instance because they changed jobs). The coq-community
organization is a place for people to take over the maintenance of such
useful packages. If you want to contribute by becoming a maintainer, you can
find a list of packages waiting for a maintainer [here](https://github.com/coq-community/manifesto/issues?q=is%3Aissue+is%3Aopen+label%3Amaintainer-wanted).
You can also propose a package that is not listed. Find out more about
coq-community in [the manifesto's README](https://github.com/coq-community/manifesto).

Ask and answer questions on our [Discourse forum][], on [Stack Exchange][],
and on the Coq IRC channel (`irc://irc.freenode.net/#coq`).

[Coq issue tracker]: https://github.com/coq/coq/issues
[Discourse forum]: https://coq.discourse.group/
[Gitter chat]: https://gitter.im/coq/coq
[Stack Exchange]: https://stackexchange.com/filters/299857/questions-tagged-coq-on-stackexchange-sites
