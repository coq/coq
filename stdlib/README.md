# The Standard Library of Coq

[![Zulip][zulip-badge]][zulip-link]
[![Discourse][discourse-badge]][discourse-link]

[discourse-badge]: https://img.shields.io/badge/Discourse-forum-informational.svg
[discourse-link]: https://coq.discourse.group/

[zulip-badge]: https://img.shields.io/badge/Zulip-chat-informational.svg
[zulip-link]: https://coq.zulipchat.com/

[Coq](https://coq.inria.fr) is a formal proof management system. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

This repository contains the standard library of Coq.

## Installation

Please see https://coq.inria.fr/download.
Information on how to build and install from sources can be found in
[`INSTALL.md`](INSTALL.md).

Then, the recommended way to require standard library modules is `From
Stdlib Require {Import,Export,} <LibraryModules>.`, except for `Byte`
(use `From Stdlib.Strings` or `From Stdlib.Init`), `Tactics` (use
`From Stdlib.Program` or `From Stdlib.Init`), `Tauto` (use `From
Stdlib.micromega` of `From Stdlib.Init`) and `Wf` (use `From
Stdlib.Program` or `From Stdlib.Init`).

## Documentation

The sources of the documentation can be found in directory [`doc`](doc).
See [`doc/README.md`](/doc/README.md) to learn more about the documentation,
in particular how to build it. The
documentation of the last released version is available on the Coq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).

The documentation of the master branch is continuously deployed.  See:
- [Reference Manual (master)][refman-master]
- [Documentation of the standard library (master)][stdlib-master]

[refman-master]: https://coq.github.io/doc/master/refman/
[stdlib-master]: https://coq.github.io/doc/master/stdlib/

## Changes

The [Recent
changes](https://coq.github.io/doc/master/refman/changes.html) chapter
of the reference manual explains the differences and the
incompatibilities of each new version of the standard library. If you upgrade,
please read it carefully as it contains important advice on how to
approach some problems you may encounter.

## Questions and discussion

We have a number of channels to reach the user community and the
development team:

- Our [Zulip chat][zulip-link], for casual and high traffic discussions.
- Our [Discourse forum][discourse-link], for more structured and easily browsable discussions and Q&A.
- Our historical mailing list, the [Coq-Club](https://sympa.inria.fr/sympa/info/coq-club).

See also [coq.inria.fr/community](https://coq.inria.fr/community.html), which
lists several other active platforms.

## Bug reports

Please report any bug / feature request in [our issue tracker](https://github.com/coq-community/stdlib/issues).

To be effective, bug reports should mention
the Coq version (`coqtop -v`), the configuration
used, and include a complete source example leading to the bug.

## Contributing to the Standard Library of Coq

Guidelines for contributing in various ways are listed in the [contributor's guide](CONTRIBUTING.md).
