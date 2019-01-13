# Coq

[![GitLab][gitlab-badge]][gitlab-link]
[![Azure Pipelines][azure-badge]][azure-link]
[![Travis][travis-badge]][travis-link]
[![Appveyor][appveyor-badge]][appveyor-link]
[![Gitter][gitter-badge]][gitter-link]
[![DOI][doi-badge]][doi-link]

[gitlab-badge]: https://gitlab.com/coq/coq/badges/master/pipeline.svg
[gitlab-link]: https://gitlab.com/coq/coq/commits/master

[azure-badge]: https://dev.azure.com/coq/coq/_apis/build/status/coq.coq?branchName=master
[azure-link]: https://dev.azure.com/coq/coq/_build/latest?definitionId=1?branchName=master

[travis-badge]: https://travis-ci.org/coq/coq.svg?branch=master
[travis-link]: https://travis-ci.org/coq/coq/builds

[appveyor-badge]: https://ci.appveyor.com/api/projects/status/eln43k05pa2vm908/branch/master?svg=true
[appveyor-link]: https://ci.appveyor.com/project/coq/coq/branch/master

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
[![Homebrew package][homebrew-badge]][homebrew-link]
[![MacPorts package][macports-badge]][macports-link]
[![nixpkgs unstable package][nixpkgs-badge]][nixpkgs-link]

[repology-badge]: https://repology.org/badge/latest-versions/coq.svg
[repology-link]: https://repology.org/metapackage/coq/versions

[arch-badge]: https://repology.org/badge/version-for-repo/arch/coq.svg
[arch-link]: https://www.archlinux.org/packages/community/x86_64/coq/

[chocolatey-badge]: https://repology.org/badge/version-for-repo/chocolatey/coq.svg
[chocolatey-link]: https://chocolatey.org/packages/Coq

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
There is a file named [`CHANGES.md`](CHANGES.md) that explains the differences and the
incompatibilities since last versions. If you upgrade Coq, please read
it carefully.

## The Coq Club
The Coq Club moderated mailing list is meant to be a standard way
to discuss questions about the Coq system and related topics. The
subscription link can be found at [coq.inria.fr/community](http://coq.inria.fr/community).

The topics to be discussed in the club should include:

* technical problems;
* questions about proof developments;
* suggestions and questions about the implementation;
* announcements of proofs;
* theoretical questions about typed lambda-calculi which are
  closely related to Coq.

## Bugs report
Please report any bug / feature request in [our issue tracker](https://github.com/coq/coq/issues).

To be effective, bug reports should mention the OCaml version used
to compile and run Coq, the Coq version (`coqtop -v`), the configuration
used, and include a complete source example leading to the bug.

## Contributing

Guidelines for contributing to Coq in various ways are listed in the [contributor's guide](CONTRIBUTING.md).

## Supporting Coq

Help the Coq community grow and prosper by becoming a sponsor! The [Coq
Consortium](https://coq.inria.fr/consortium) can establish sponsorship contracts
or receive donations. If you want to take an active role in shaping Coq's
future, you can also become a Consortium member. If you are interested, please
get in touch!
