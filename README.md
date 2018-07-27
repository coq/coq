# Coq

[![Travis](https://travis-ci.org/coq/coq.svg?branch=master)](https://travis-ci.org/coq/coq/builds)
[![Appveyor](https://ci.appveyor.com/api/projects/status/eln43k05pa2vm908/branch/master?svg=true)](https://ci.appveyor.com/project/coq/coq/branch/master)
[![Gitter](https://badges.gitter.im/coq/coq.svg)](https://gitter.im/coq/coq)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1003420.svg)](https://doi.org/10.5281/zenodo.1003420)

Coq is a formal proof management system. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

## Installation
Download the pre-built packages of the [latest release](https://github.com/coq/coq/releases/latest) for Windows and MacOS;
read the [help page](https://coq.inria.fr/opam/www/using.html) on how to install Coq with OPAM;
or refer to the [`INSTALL` file](/INSTALL) for the procedure to install from source.

## Documentation

The sources of the documentation can be found in directory [`doc`](/doc). The
documentation of the last released version is available on the Coq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).
See also [Cocorico](https://github.com/coq/coq/wiki) (the Coq wiki),
and the [Coq FAQ](https://github.com/coq/coq/wiki/The-Coq-FAQ),
for additional user-contributed documentation.

## Changes
There is a file named [`CHANGES`](/CHANGES) that explains the differences and the
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
