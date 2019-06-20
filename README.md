# Coq

[![GitLab][gitlab-badge]][gitlab-link]
[![Azure Pipelines][azure-badge]][azure-link]
[![Gitter][gitter-badge]][gitter-link]
[![DOI][doi-badge]][doi-link]

[gitlab-badge]: https://gitlab.com/coq/coq/badges/master/pipeline.svg
[gitlab-link]: https://gitlab.com/coq/coq/commits/master

[azure-badge]: https://dev.azure.com/coq/coq/_apis/build/status/coq.coq?branchName=master
[azure-link]: https://dev.azure.com/coq/coq/_build/latest?definitionId=1?branchName=master

[gitter-badge]: https://badges.gitter.im/coq/coq.svg
[gitter-link]: https://gitter.im/coq/coq

[doi-badge]: https://zenodo.org/badge/DOI/10.5281/zenodo.1003420.svg
[doi-link]: https://doi.org/10.5281/zenodo.1003420

Coq is a formal proof management system. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

## Installation

[![latest packaged version(s)][repology-badge]][repology-link]

[![Arch package][arch-badge]][arch-link]
[![Chocolatey package][chocolatey-badge]][chocolatey-link]
[![Conda package][conda-badge]][conda-link]
[![Homebrew package][homebrew-badge]][homebrew-link]
[![nixpkgs unstable package][nixpkgs-badge]][nixpkgs-link]

[repology-badge]: https://repology.org/badge/latest-versions/coq.svg
[repology-link]: https://repology.org/metapackage/coq/versions

[arch-badge]: https://repology.org/badge/version-for-repo/arch/coq.svg
[arch-link]: https://www.archlinux.org/packages/community/x86_64/coq/

[chocolatey-badge]: https://repology.org/badge/version-for-repo/chocolatey/coq.svg
[chocolatey-link]: https://chocolatey.org/packages/Coq

[conda-badge]: https://img.shields.io/conda/vn/conda-forge/coq.svg?label="Conda%20package"
[conda-link]: https://github.com/conda-forge/coq-feedstock

[homebrew-badge]: https://repology.org/badge/version-for-repo/homebrew/coq.svg
[homebrew-link]: https://formulae.brew.sh/formula/coq

[macports-badge]: https://repology.org/badge/version-for-repo/macports/coq.svg
[macports-link]: https://www.macports.org/ports.php?by=name&substr=coq

[nixpkgs-badge]: https://repology.org/badge/version-for-repo/nix_unstable/coq.svg
[nixpkgs-link]: https://nixos.org/nixos/packages.html#coq

Download the pre-built packages of the [latest release][] for Windows and macOS;
read the [help page][opam-using] on how to install Coq with OPAM;
or refer to the [`INSTALL`](INSTALL) file for the procedure to install from source.

[latest release]: https://github.com/coq/coq/releases/latest
[opam-using]: https://coq.inria.fr/opam/www/using.html

## Documentation

The sources of the documentation can be found in directory [`doc`](doc).
See [`doc/README.md`](/doc/README.md) to learn more about the documentation,
in particular how to build it. The
documentation of the last released version is available on the Coq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).
See also [Cocorico](https://github.com/coq/coq/wiki) (the Coq wiki),
and the [Coq FAQ](https://github.com/coq/coq/wiki/The-Coq-FAQ),
for additional user-contributed documentation.

## Changes

The [Recent
changes](https://coq.github.io/doc/master/refman/changes.html) chapter
of the reference manual explains the differences and the
incompatibilities of each new version of Coq. If you upgrade Coq,
please read it carefully as it contains important advice on how to
approach some problems you may encounter.

## Questions and discussion

We have a number of channels to reach the user community and the
development team:

- Our [Discourse forum](https://coq.discourse.group).
- Our mailing list, the [Coq-Club](https://sympa.inria.fr/sympa/info/coq-club).
- Our [Gitter channel][gitter-link], which is a good way to reach
  developers for quick chat and development questions.

See also [coq.inria.fr/community](https://coq.inria.fr/community.html).

## Bug reports

Please report any bug / feature request in [our issue tracker](https://github.com/coq/coq/issues).

To be effective, bug reports should mention the OCaml version used
to compile and run Coq, the Coq version (`coqtop -v`), the configuration
used, and include a complete source example leading to the bug.

## Contributing to Coq

Guidelines for contributing to Coq in various ways are listed in the [contributor's guide](CONTRIBUTING.md).

Information about the next release is at https://github.com/coq/coq/wiki/Release-Plan

## Supporting Coq

Help the Coq community grow and prosper by becoming a sponsor! The [Coq
Consortium](https://coq.inria.fr/consortium) can establish sponsorship contracts
or receive donations. If you want to take an active role in shaping Coq's
future, you can also become a Consortium member. If you are interested, please
get in touch!
