# Contributing to Coq

Thank you for your interest in contributing to Coq! There are many ways to contribute, and we appreciate all of them.

## Bug Reports

Bug reports are enormously useful to identify issues with Coq; we can't fix what we don't know about. To report a bug, please open an issue in the [Coq issue tracker](https://github.com/coq/coq/issues) (you'll need a GitHub account). You can file a bug for any of the following:

- An anomaly. These are always considered bugs, so Coq will even ask you to file a bug report!
- An error you didn't expect. If you're not sure whether it's a bug or intentional, feel free to file a bug anyway. We may want to improve the documentation or error message.
- Missing documentation. It's helpful to track where the documentation should be improved, so please file a bug if you can't find or don't understand some bit of documentation.
- An error message that wasn't as helpful as you'd like. Bonus points for suggesting what information would have helped you.
- Bugs in CoqIDE should also be filed in the [Coq issue tracker](https://github.com/coq/coq/issues). Bugs in the Emacs plugin should be filed against [ProofGeneral](https://github.com/ProofGeneral/PG/issues), or against [company-coq](https://github.com/cpitclaudel/company-coq/issues) if they are specific to company-coq features.

It would help if you search the existing issues before reporting a bug. This can be difficult, so consider it extra credit. We don't mind duplicate bug reports.

When it applies, it's extremely helpful for bug reports to include sample code, and much better if the code is self-contained and complete. It's not necessary to minimize your bug or identify precisely where the issue is, since someone else can often do this if you include a complete example. We tend to include the code in the bug description itself, but if you have a very large input file then you can add it as an attachment.

If you want to minimize your bug (or help minimize someone else's) for more extra credit, then you can use the [Coq bug minimizer](https://github.com/JasonGross/coq-tools) (specifically, the bug minimizer is the `find-bug.py` script in that repo).

## Pull requests

**Beginner's guide to hacking Coq: [`dev/doc/README.md`](dev/doc/README.md)** \
**Development information and tools: [`dev/README.md`](dev/README.md)**

If you want to contribute a bug fix or feature yourself, pull requests on the [GitHub repository](https://github.com/coq/coq) are the way to contribute directly to the Coq implementation. We recommend you create a fork of the repository on GitHub and push your changes to a new "topic branch" in that fork. From there you can follow the [GitHub pull request documentation](https://help.github.com/articles/about-pull-requests/) to get your changes reviewed and pulled into the Coq source repository.

Documentation for getting started with the Coq sources is located in various
files in [`dev/doc`](dev/doc) (for example, [debugging.md](dev/doc/debugging.md)).
For further help with the Coq sources, feel free to join
the [Coq Gitter chat](https://gitter.im/coq/coq) and ask questions.

Please make pull requests against the `master` branch.

If it's your first significant contribution to Coq (significant means: more
than fixing a typo), your pull request should include a commit adding your name
to the [`CREDITS`](CREDITS) file (possibly with the name of your
institution / employer if relevant to your contribution, an ORCID if you have
one —you may log into https://orcid.org/ using your institutional account to
get one—, and the year of your contribution).

It's helpful to run the Coq test suite with `make test-suite` before submitting
your change. Our CI runs this test suite and lots of other tests, including
building external Coq developments, on every pull request, but these results
take significantly longer to come back (on the order of a few hours). Running
the test suite locally will take somewhere around 10-15 minutes. Refer to
[`dev/ci/README.md`](dev/ci/README.md#information-for-developers) for more
information on CI tests, including how to run them on your private branches.

If your pull request fixes a bug, please consider adding a regression test as
well. See [`test-suite/README.md`](test-suite/README.md) for how to do so.

If your pull request fixes a critical bug (a bug allowing a proof of `False`),
please add an entry to [`dev/doc/critical-bugs`](/dev/doc/critical-bugs).

Don't be alarmed if the pull request process takes some time. It can take a few days to get feedback, approval on the final changes, and then a merge. Coq doesn't release new versions very frequently so it can take a few months for your change to land in a released version. That said, you can start using the latest Coq `master` branch to take advantage of all the new features, improvements, and fixes.

Whitespace discipline (do not indent using tabs, no trailing spaces, text files end with newlines) is checked by Travis (using `git diff --check`). We ship a [`dev/tools/pre-commit`](/dev/tools/pre-commit) git hook which fixes these errors at commit time. `configure` automatically sets you up to use it, unless you already have a hook at `.git/hooks/pre-commit`.

Here are a few tags Coq developers may add to your PR and what they mean. In general feedback and requests for you as the pull request author will be in the comments and tags are only used to organize pull requests.

- [needs: rebase][rebase-label] indicates the PR should be rebased on top of
  the latest base branch (usually `master`). See the
  [GitHub documentation](https://help.github.com/articles/about-git-rebase/)
  for a brief introduction to using `git rebase`.
  This label will be automatically added if you open or synchronize your PR and
  it is not up-to-date with the base branch. So please, do not forget to rebase
  your branch every time you update it.
- [needs: fixing][fixing-label] indicates the PR needs a fix, as discussed in the comments.
- [needs: benchmarking][benchmarking-label] and [needs: testing][testing-label]
  indicate the PR needs testing beyond what the test suite can handle.
  For example, performance benchmarking is currently performed with a different
  infrastructure ([documented in the wiki][jenkins-doc]). Unless some followup
  is specifically requested you aren't expected to do this additional testing.

To learn more about the merging process, you can read the
[merging documentation for Coq maintainers](dev/doc/MERGING.md).

## Documentation

Currently the process for contributing to the documentation is the same as for changing anything else in Coq, so please submit a pull request as described above.

Our issue tracker includes a flag to mark bugs related to documentation. You can view a list of documentation-related bugs using a [GitHub issue search](https://github.com/coq/coq/issues?q=is%3Aopen+is%3Aissue+label%3A%22kind%3A+documentation%22). Many of these bugs can be fixed by contributing writing, without knowledge of Coq's OCaml source code.

The sources for the [Coq reference manual](https://coq.inria.fr/distrib/current/refman/) are at [`doc/sphinx`](/doc/sphinx). These are written in reStructuredText and compiled to HTML and PDF with [Sphinx](http://www.sphinx-doc.org/).

You may also contribute to the informal documentation available in [Cocorico](https://github.com/coq/coq/wiki) (the Coq wiki), and the [Coq FAQ](https://github.com/coq/coq/wiki/The-Coq-FAQ). Both of these are editable by anyone with a GitHub account.

## Following the development

If you want to follow the development activity around Coq, you are encouraged
to subscribe to the [Coqdev mailing list](https://sympa.inria.fr/sympa/info/coqdev).
This mailing list has reasonably low traffic.

You may also choose to use GitHub feature to
["watch" this repository](https://github.com/coq/coq/subscription), but be
advised that this means receiving a very large number of notifications.
GitHub gives [some advice](https://blog.github.com/2017-07-18-managing-large-numbers-of-github-notifications/#prioritize-the-notifications-you-receive)
on how to configure your e-mail client to filter these notifications.
A possible alternative is to deactivate e-mail notifications and manage your
GitHub web notifications using a tool such as [Octobox](http://octobox.io/).

## Contributing outside this repository

There are many useful ways to contribute to the Coq ecosystem that don't involve the Coq repository.

Tutorials to teach Coq, and especially to teach particular advanced features, would be much appreciated. Some tutorials are listed on the [Coq website](https://coq.inria.fr/documentation). If you would like to add a link to this list, please make a pull request against the Coq website repository at https://github.com/coq/www.

External plugins / libraries contribute to create a successful ecosystem around Coq. If your external development is mature enough, you may consider submitting it for addition to our CI tests. Refer to [`dev/ci/README.md`](/dev/ci/README.md) for more information.

Ask and answer questions on [Stack Exchange](https://stackexchange.com/filters/299857/questions-tagged-coq-on-stackexchange-sites) which has a helpful community of Coq users.

Hang out on the Coq IRC channel, `irc://irc.freenode.net/#coq`, and help answer questions.

[rebase-label]: https://github.com/coq/coq/pulls?utf8=%E2%9C%93&q=is%3Aopen%20is%3Apr%20label%3A%22needs%3A%20rebase%22
[fixing-label]: https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+fixing%22
[benchmarking-label]: https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+benchmarking%22
[testing-label]: https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+testing%22

[jenkins-doc]: https://github.com/coq/coq/wiki/Jenkins-(automated-benchmarking)
