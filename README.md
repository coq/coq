# The Rocq Prover

[![GitLab CI][gitlab-badge]][gitlab-link]
[![GitHub macOS CI][gh-macos-badge]][gh-macos-link]
[![GitHub Windows CI][gh-win-badge]][gh-win-link]
[![Zulip][zulip-badge]][zulip-link]
[![Discourse][discourse-badge]][discourse-link]
[![DOI][doi-badge]][doi-link]

[gitlab-badge]: https://gitlab.inria.fr/coq/coq/badges/master/pipeline.svg
[gitlab-link]: https://gitlab.inria.fr/coq/coq/commits/master

[gh-macos-badge]: https://github.com/coq/coq/actions/workflows/ci-macos.yml/badge.svg
[gh-macos-link]: https://github.com/coq/coq/actions/workflows/ci-macos.yml

[gh-win-badge]: https://github.com/coq/coq/actions/workflows/ci-windows.yml/badge.svg
[gh-win-link]: https://github.com/coq/coq/actions/workflows/ci-windows.yml

[discourse-badge]: https://img.shields.io/badge/Discourse-forum-informational.svg
[discourse-link]: https://coq.discourse.group/

[zulip-badge]: https://img.shields.io/badge/Zulip-chat-informational.svg
[zulip-link]: https://coq.zulipchat.com/

[doi-badge]: https://zenodo.org/badge/DOI/10.5281/zenodo.1003420.svg
[doi-link]: https://doi.org/10.5281/zenodo.1003420

The Rocq Prover is an interactive theorem prover, or proof assistant. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

## Installation

[![latest packaged version(s)][repology-badge]][repology-link]

[![Docker Hub package][dockerhub-badge]][dockerhub-link]
[![latest dockerized version][coqorg-badge]][coqorg-link]

[repology-badge]: https://repology.org/badge/latest-versions/coq.svg
[repology-link]: https://repology.org/metapackage/coq/versions

[dockerhub-badge]: https://img.shields.io/badge/images%20on-Docker%20Hub-blue.svg
[dockerhub-link]: https://hub.docker.com/r/coqorg/coq#supported-tags "Supported tags on Docker Hub"

[coqorg-badge]: https://img.shields.io/docker/v/coqorg/coq/latest
[coqorg-link]: https://github.com/coq-community/docker-coq/wiki#docker-coq-images "coqorg/coq:latest"

Please see https://coq.inria.fr/download.
Information on how to build and install from sources can be found in
[`INSTALL.md`](INSTALL.md).

## Documentation

The sources of the documentation can be found in directory [`doc`](doc).
See [`doc/README.md`](/doc/README.md) to learn more about the documentation,
in particular how to build it. The
documentation of the last released version is available on the Rocq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).
See also [the Rocq wiki](https://github.com/coq/coq/wiki),
and the [Rocq FAQ](https://github.com/coq/coq/wiki/The-Coq-FAQ),
for additional user-contributed documentation.

The documentation of the master branch is continuously deployed.  See:
- [Reference Manual (master)][refman-master]
- [Documentation of the standard library (master)][stdlib-master]
- [Documentation of the ML API (master)][api-master]

[api-master]: https://coq.github.io/doc/master/api/
[refman-master]: https://coq.github.io/doc/master/refman/
[stdlib-master]: https://coq.github.io/doc/master/stdlib/

## Changes

The [Recent
changes](https://coq.github.io/doc/master/refman/changes.html) chapter
of the reference manual explains the differences and the
incompatibilities of each new version of the Rocq Prover. If you upgrade Rocq,
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

Please report any bug / feature request in [our issue tracker](https://github.com/coq/coq/issues).

To be effective, bug reports should mention the OCaml version used
to compile and run Rocq, the Rocq version (`coqtop -v` or `rocq -v`), the configuration
used, and include a complete source example leading to the bug.

## Contributing to Rocq

Guidelines for contributing to Rocq in various ways are listed in the [contributor's guide](CONTRIBUTING.md).

Information about release plans is at https://github.com/coq/coq/wiki/Release-Plan

## Supporting Rocq

Help the Rocq community grow and prosper by becoming a sponsor! The [Rocq
Consortium](https://rocq-prover.org/consortium) can establish sponsorship contracts
or receive donations. If you want to take an active role in shaping Rocq's
future, you can also become a Consortium member. If you are interested, please
get in touch!
