# Contributing to Coq

Thank you for your interest in contributing to Coq! There are many ways to contribute, and we appreciate all of them.

## Bug Reports

Bug reports are enormously useful to identify issues with Coq; we can't fix what we don't know about. Bug reports should all be filed on the [Coq Bugzilla](https://coq.inria.fr/bugs/) (you'll have to make an account). You can file a bug for any of the following:

- An anomaly. These are always considered bugs, so Coq will even ask you to file a bug report!
- An error you didn't expect. If you're not sure whether it's a bug or intentional, feel free to file a bug anyway. We may want to improve the documentation or error message.
- An error message that wasn't as helpful as you'd like. Bonus points for suggesting what information would have helped you.
- Bugs in CoqIDE should also be filed on the Bugzilla. Bugs in the Emacs plugin should be filed against [ProofGeneral](https://github.com/ProofGeneral/PG/issues), or against [company-coq](https://github.com/cpitclaudel/company-coq/issues) if they are specific to company-coq features.

It would help if you searched the existing issues to see if someone has already reported your error. This can be difficult and the search feature isn't as powerful as we'd like, so consider this extra credit. We don't mind duplicate bug reports.

When it applies, it's extremely helpful for bug reports to include sample code, and much better if the code is self-contained and complete. It's not necessary to minimize your bug or identify precisely where the issue is, since someone else can often do this if you include a complete example. We tend to include the code in the bug description itself, but if you have a very large input file then you can add it as an attachment.

## Pull requests

Sometimes you able to contribute a bug fix or improvement yourself, and pull requests are the mechanism to get these changes into Coq.

Please make pull requests against the `master` branch.

It's helpful to run the Coq test suite with `make -C test-suite` before submitting your change. Travis CI runs this test suite and a much larger one on every pull request, but these results take significantly longer to come back (on the order of a few hours). Running the test suite locally will take somewhere around 10-15 minutes.

Don't be alarmed if pull requests take some time. It can take a few days to get feedback, approval on the final changes, and then a merge. Coq doesn't release new versions very frequently so it can take a few months for your change to land in a released version. That said, you can start using the latest Coq `master` branch to take advantage of all the new features, improvements, and fixes.

## Documentation

Currently the process for contributing to the documentation is the same as for changing anything else in Coq, so please submit a pull request as described above. We hope to streamline this process eventually.
