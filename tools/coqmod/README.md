# coqmod

- [coqmod](#coqmod)
- [Example](#example)
- [Testing](#testing)
- [Specification](#specification)
  - [Name](#name)
  - [Require](#require)
  - [From](#from)
  - [Declare](#declare)
  - [Load logical](#load-logical)
  - [Load physical](#load-physical)
  - [Extra Dependency](#extra-dependency)


`coqmod` outputs Coq modules and OCaml libraries that a `.v` file depends on.

It is intended to be a minimalistic replacement to `coqdep` for use by `dune`.

Unlike `coqdep`, it does not scan directories making it lightweight in
comparison.

It has 3 `--format` modes:
- `csexp` - canonical serial expresion (default)
- `read` - human readable output
- `sexp` - pretty printed serial expression

When a single `.v` file is passed to `coqmod`, it will output the tokens
corresponding to dependencies in the specified format.

# Example

Here is the output for an `example.v` file:

```coq
  From A.B.C Require Import R.X L.Y.G Z.W.

  Load X.
  Load "A/b/c".

  Declare ML Module "foo.bar.baz".

  Require A B C.

  Require Import AI BI CI.
```


```lisp
  $ coqmod example.v
  (8:Document(4:Name9:example.v)(7:Require(((3:Loc(1:81:9)(1:82:10))1:A))(((3:Loc(2:102:16)(2:102:18))2:AI))(((3:Loc(1:82:11)(1:82:12))1:B))(((3:Loc(2:102:19)(2:102:21))2:BI))(((3:Loc(1:82:13)(1:82:14))1:C))(((3:Loc(2:102:22)(2:102:24))2:CI))(((3:Loc(1:31:6)(1:31:7))1:X))(((3:Loc(1:11:6)(1:12:11))5:A.B.C)((3:Loc(1:12:31)(1:12:36))5:L.Y.G))(((3:Loc(1:11:6)(1:12:11))5:A.B.C)((3:Loc(1:12:27)(1:12:30))3:R.X))(((3:Loc(1:11:6)(1:12:11))5:A.B.C)((3:Loc(1:12:37)(1:12:40))3:Z.W)))(7:Declare((3:Loc(1:62:19)(1:62:32))11:foo.bar.baz))(4:Load((3:Loc(1:41:6)(1:42:13))5:A/b/c)))
```

```coq
  $ coqmod example.v --format=read
  Begin example.v
  Ln 8, Col 9-10 Require A
  Ln 10, Col 16-18 Require AI
  Ln 8, Col 11-12 Require B
  Ln 10, Col 19-21 Require BI
  Ln 8, Col 13-14 Require C
  Ln 10, Col 22-24 Require CI
  Ln 3, Col 6-7 Require X
  Ln 1, Col 6-11 From A.B.C Ln 1, Col 31-36 Require L.Y.G
  Ln 1, Col 6-11 From A.B.C Ln 1, Col 27-30 Require R.X
  Ln 1, Col 6-11 From A.B.C Ln 1, Col 37-40 Require Z.W
  Ln 6, Col 19-32 Declare ML Module Ln 6, Col 19-32 Require foo.bar.baz
  Ln 4, Col 6-13 Physical "A/b/c"
  End example.v
```

```lisp
  $ coqmod example.v --format=sexp
  (Document
   (Name example.v)
   (Require
    (((Loc (8 9) (8 10)) A))
    (((Loc (10 16) (10 18)) AI))
    (((Loc (8 11) (8 12)) B))
    (((Loc (10 19) (10 21)) BI))
    (((Loc (8 13) (8 14)) C))
    (((Loc (10 22) (10 24)) CI))
    (((Loc (3 6) (3 7)) X))
    (((Loc (1 6) (1 11)) A.B.C) ((Loc (1 31) (1 36)) L.Y.G))
    (((Loc (1 6) (1 11)) A.B.C) ((Loc (1 27) (1 30)) R.X))
    (((Loc (1 6) (1 11)) A.B.C) ((Loc (1 37) (1 40)) Z.W)))
   (Declare
    ((Loc (6 19) (6 32)) foo.bar.baz))
   (Load
    ((Loc (4 6) (4 13)) A/b/c)))
```


# Testing

There is a cram test for `coqmod` in `tools/coqmod/test-coqmod.t/`.

To run it do:
```
dune build @test-coqmod
```

You can also use watch mode `-w` to get a continuous build and `--auto-promote`
to get the output of the cram test updated on each save.

# Specification

`coqmod` tokenizes Coq and OCaml module names and groups them in various
s-expressions detailed as follows. All parsed files are wrapped in the
`(Document ...)` s-exp.

The `(Name ...)` token is always the name of the file that was passed to
`coqmod`.

Location s-exps `(Loc (1 9) (1 10))` correspond to the line and coloumn number
of the begining and end of the token. In this case begining at `Ln 1, Col 9` and
and ending at `Ln 1, Col 10`.

Here are the corresponding s-exp for Coq vernac commands that add dependencies:

## Name
```lisp
  $ cat > FileName.v << EOF
  > EOF
  $ coqmod FileName.v --format=sexp
  (Document
   (Name FileName.v))
```
## Require
```lisp
  $ cat > Require.v << EOF
  > Require A B.
  > Require B C.
  > EOF
  $ coqmod Require.v --format=sexp
  (Document
   (Name Require.v)
   (Require
    (((Loc (1 9) (1 10)) A))
    (((Loc (2 9) (2 10)) B))
    (((Loc (2 11) (2 12)) C))))
```
## From
```lisp
  $ cat > From.v << EOF
  > From A Require B C.
  > From A Require C D.
  > From R Require E.
  > EOF
  $ coqmod From.v --format=sexp
  (Document
   (Name From.v)
   (Require
    (((Loc (1 6) (1 7)) A) ((Loc (1 16) (1 17)) B))
    (((Loc (1 6) (1 7)) A) ((Loc (1 18) (1 19)) C))
    (((Loc (2 6) (2 7)) A) ((Loc (2 18) (2 19)) D))
    (((Loc (3 6) (3 7)) R) ((Loc (3 16) (3 17)) E))))
```
## Declare
```lisp
  $ cat > Declare.v << EOF
  > Declare ML Module "foo" "bar.baz".
  > Declare ML Module "zoo" "foo".
  > EOF
  $ coqmod Declare.v --format=sexp
  (Document
   (Name Declare.v)
   (Declare
    ((Loc (1 25) (1 34)) bar.baz)
    ((Loc (2 25) (2 30)) foo)
    ((Loc (2 19) (2 24)) zoo)))
```
## Load logical
```lisp
  $ cat > LoadLogical.v << EOF
  > Load A.
  > Load B.
  > EOF
  $ coqmod LoadLogical.v --format=sexp
  (Document
   (Name LoadLogical.v)
   (Require
    (((Loc (1 6) (1 7)) A))
    (((Loc (2 6) (2 7)) B))))
```
## Load physical
```lisp
  $ cat > LoadPhysical.v << EOF
  > Load "a/b/c".
  > Load "c/d/e".
  > EOF
  $ coqmod LoadPhysical.v --format=sexp
  (Document
   (Name LoadPhysical.v)
   (Load
    ((Loc (1 6) (1 13)) a/b/c)
    ((Loc (2 6) (2 13)) c/d/e)))
```
## Extra Dependency
```lisp
  $ cat > ExtraDependency.v << EOF
  > From A Extra Dependency "b/c/d".
  > EOF
  $ coqmod ExtraDependency.v --format=sexp
  (Document
   (Name ExtraDependency.v)
   (ExtraDep
    (((Loc (1 6) (1 7)) A) (Loc (1 25) (1 32)) b/c/d)))
```
