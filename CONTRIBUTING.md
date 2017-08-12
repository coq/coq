# Contributing to Coq

Thank you for your interest in contributing to Coq! There are many ways to contribute, and we appreciate all of them.

## Bug Reports

Bug reports are enormously useful to identify issues with Coq; we can't fix what we don't know about. Bug reports should all be filed on the [Coq Bugzilla](https://coq.inria.fr/bugs/) (you'll have to make an account). You can file a bug for any of the following:

- An anomaly. These are always considered bugs, so Coq will even ask you to file a bug report!
- An error you didn't expect. If you're not sure whether it's a bug or intentional, feel free to file a bug anyway. We may want to improve the documentation or error message.
- Missing documentation. It's helpful to track where the documentation should be improved, so please file a bug if you can't find or don't understand some bit of documentation.
- An error message that wasn't as helpful as you'd like. Bonus points for suggesting what information would have helped you.
- Bugs in CoqIDE should also be filed on the Bugzilla. Bugs in the Emacs plugin should be filed against [ProofGeneral](https://github.com/ProofGeneral/PG/issues), or against [company-coq](https://github.com/cpitclaudel/company-coq/issues) if they are specific to company-coq features.

It would help if you search the existing issues before reporting a bug. This can be difficult, so consider it extra credit. We don't mind duplicate bug reports.

When it applies, it's extremely helpful for bug reports to include sample code, and much better if the code is self-contained and complete. It's not necessary to minimize your bug or identify precisely where the issue is, since someone else can often do this if you include a complete example. We tend to include the code in the bug description itself, but if you have a very large input file then you can add it as an attachment.

## Pull requests

If you want to contribute a bug fix or feature yourself, pull requests on the [GitHub repository](https://github.com/coq/coq) are the way to contribute directly to the Coq implementation. We recommend you create a fork of the repository on GitHub and push your changes to a new "topic branch" in that fork. From there you can follow the [GitHub pull request documentation](https://help.github.com/articles/about-pull-requests/) to get your changes reviewed and pulled into the Coq source repository.

Documentation for getting started with the Coq sources is located in various files in [`dev/doc`](/dev/doc) (for example, [debugging.txt](/dev/doc/debugging.txt)).

Please make pull requests against the `master` branch.

It's helpful to run the Coq test suite with `make test-suite` before submitting your change. Travis CI runs this test suite and a much larger one including external Coq developments on every pull request, but these results take significantly longer to come back (on the order of a few hours). Running the test suite locally will take somewhere around 10-15 minutes.

Don't be alarmed if the pull request process takes some time. It can take a few days to get feedback, approval on the final changes, and then a merge. Coq doesn't release new versions very frequently so it can take a few months for your change to land in a released version. That said, you can start using the latest Coq `master` branch to take advantage of all the new features, improvements, and fixes.

Here are a few tags Coq developers may add to your PR and what they mean. In general feedback and requests for you as the pull request author will be in the comments and tags are only used to organize pull requests.

- [needs: rebase](https://github.com/coq/coq/pulls?utf8=%E2%9C%93&q=is%3Aopen%20is%3Apr%20label%3A%22needs%3A%20rebase%22%20) indicates the PR should be rebased on top of the latest `master` branch. See the [GitHub documentation](https://help.github.com/articles/about-git-rebase/) for a brief introduction to using `git rebase`.
- [needs: fixing](https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+fixing%22) indicates the PR needs a fix, as discussed in the comments.
- [needs: testing](https://github.com/coq/coq/pulls?q=is%3Aopen+is%3Apr+label%3A%22needs%3A+testing%22) indicates the PR needs testing. This is often used when testing beyond what the test suite can handle is required. For example, performance benchmarking is currently performed with a different infrastructure. Unless some followup is specifically requested you aren't expected to do this additional testing.

## Documentation

Currently the process for contributing to the documentation is the same as for changing anything else in Coq, so please submit a pull request as described above.

Bugzilla includes a component to mark bugs related to documentation. You can view a list of documentation-related bugs using a [Bugzilla search](https://coq.inria.fr/bugs/buglist.cgi?component=Doc&list_id=455006&product=Coq&resolution=---). Many of these bugs can be fixed by contributing writing, without knowledge of Coq's OCaml source code.

The sources for the [Coq reference manual](https://coq.inria.fr/distrib/current/refman/) are at [`doc/refman`](/doc/refman). These are written in LaTeX and compiled to HTML with [HeVeA](http://hevea.inria.fr/).

## Contributing outside this repository

There are many useful ways to contribute to the Coq ecosystem that don't involve the Coq repository.

Tutorials to teach Coq, and especially to teach particular advanced features, would be much appreciated. Some tutorials are listed on the [Coq website](https://coq.inria.fr/documentation). If you would like to add a link to this list, please make a pull request against the Coq website repository at https://github.com/coq/www.

Subscribe to the [coq-club](https://coq.inria.fr/community) mailing list and answer questions there. Asking your own questions on the mailing list will also help others learn from the answers, which often come from experts in the community.
