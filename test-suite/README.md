# Coq Test Suite

The test suite can be run from the root directory by `make test-suite`.

From this directory, `make aaa/bbb/ccc.v.log` runs one test (if not already run), storing the output in the named `.log` file.
See [`test-suite/Makefile`](/test-suite/Makefile) for more information.

## Adding a test

Regression tests for closed bugs should be added to `test-suite/bugs/closed`, as `1234.v` where `1234` is the bug number.
Files in this directory are tested for successful compilation.
When you fix a bug, you should usually add a regression test here as well.

The error "(bug seems to be opened, please check)" when running `make test-suite` means that a test in `bugs/closed` failed to compile.

There are also output tests in `test-suite/output` which consist of a `.v` file and a `.out` file with the expected output.

