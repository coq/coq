# Coq Test Suite

## Table of contents

- [Coq Test Suite](#coq-test-suite)
  - [Table of contents](#table-of-contents)
  - [Introduction](#introduction)
    - [Quality of life suggestions](#quality-of-life-suggestions)
  - [Adding a test](#adding-a-test)
    - [Promoting test output](#promoting-test-output)
    - [Output test example](#output-test-example)
  - [Rule generation](#rule-generation)
  - [Cram tests](#cram-tests)
  - [Updating csdp cache](#updating-csdp-cache)
  - [Complexity tests](#complexity-tests)
  - [Unit tests](#unit-tests)
  - [Misc tests](#misc-tests)

## Introduction

The test suite can be run from the Coq root directory by running `make`. This
does two things:
  1. Run `dune build @test-gen` to generate the rules for the test-suite.
  2. Run `dune test` to build all the testing targets.

The test suite is incremental meaning that you do not have to build the rest of
the repository in order to run it. You may also run it after hacking on some
files and dune will rebuild only what is necessery.

`dune test` is very flexible, you can for instance build all the targets in a
certain subdirectory by running `dune test test-suite/bugs`.

### Quality of life suggestions

Here are a few quality of life suggestions:

+ We suggest passing `--display=short` to dune (or `DUNEOPT="--display=short"`
  for make). This will display every target that dune is building at a give
  time.

+ The option `--always-show-command-line` is also very useful since dune will
  dump a subshell command that you can run to reproduce the failing test. (You
  might need to add a `$` before running it in your terminal.


## Adding a test

For simple tests, placing the new .v file will be enough. If the test expects an
output, a file `test.out` should provided for the file `test.v`. The `.out` file
can be empty for the time being, and the correct output generated using `dune
promote`. See [Promoting test output](#promoting-test-output).

### Promoting test output

If the ouput of a test does not match the expected output, dune will report this
diff. You can use the `promote` target of `Makefile.dune` in order to promote
all the expected output files to the new output. To have finer control, use
`dune promote` with which you can even promote more refined targets such as
`dune promote test-suite/bugs/mybug.out`.

### Output test example

Adding `_test.v` to `output/` for instance will yield the following when running
`make test`:
```sh
Error: No rule found for test-suite/output/_test.out
-> required by alias test-suite/output/runtest in
   test-suite/test_suite_rules.sexp:56694
make: *** [Makefile:122: test] Error 1
```
To fix this, we `touch` the file:
```sh
touch test-suite/output/_test.out
```
and rerun `make test`. Now dune will complain that the output is different:
```diff
File "test-suite/output/_test.out", line 1, characters 0-0:
diff --git a/_build/default/test-suite/output/_test.out b/_build/default/test-suite/output/_test.v.log
index e69de29bb2..a7de56ea32 100644
--- a/_build/default/test-suite/output/_test.out
+++ b/_build/default/test-suite/output/_test.v.log
@@ -0,0 +1,2 @@
+Type : Type
+     : Type
make: *** [Makefile:122: test] Error 1
```
Running `make promote` will now update the `.out` file with the new output:
```sh
Promoting _build/default/test-suite/output/_test.v.log to
  test-suite/output/_test.out.
```
Finally running `make test`, dune will report no problems.

---

## Rule generation
TODO

## Cram tests
TODO

## Updating csdp cache
TODO

## Complexity tests
TODO

## Unit tests
TODO Currently broken

## Misc tests
TODO
