# Coq

[![Travis](https://travis-ci.org/coq/coq.svg?branch=master)](https://travis-ci.org/coq/coq/builds) [![Build status](https://ci.appveyor.com/api/projects/status/eln43k05pa2vm908/branch/master?svg=true)](https://ci.appveyor.com/project/coq/coq/branch/master) [![Gitter](https://badges.gitter.im/coq/coq.svg)](https://gitter.im/coq/coq)

Coq is a formal proof management system. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

## Installation
Go to the [download page](https://coq.inria.fr/download) for Windows and MacOS packages;
read the [help page](https://coq.inria.fr/opam/www/using.html) on how to install Coq with OPAM;
or refer to the [`INSTALL` file](/INSTALL) for the procedure to install from source.

## Documentation
The documentation is part of the archive in directory doc. The
documentation of the last released version is available on the Coq
web site at [coq.inria.fr/documentation](http://coq.inria.fr/documentation).

## Changes
There is a file named [`CHANGES`](/CHANGES) that explains the differences and the
incompatibilities since last versions. If you upgrade Coq, please read
it carefully.

## Availability
Coq is available from [coq.inria.fr](http://coq.inria.fr).

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

For any questions/suggestions about the Coq Club, please write to
`coq-club-request@inria.fr`.

## Bugs report
Please report any bug in [our issue tracker](https://github.com/coq/coq/issues).

To be effective, bug reports should mention the OCaml version used
to compile and run Coq, the Coq version (`coqtop -v`), the configuration
used, and include a complete source example leading to the bug.

## Contributing

Guidelines for contributing to Coq in various ways are listed in the [contributor's guide](CONTRIBUTING.md).
