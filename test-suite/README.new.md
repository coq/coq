# Coq Test Suite

## Table Of Contents

- [Coq Test Suite](#coq-test-suite)
  - [Table Of Contents](#table-of-contents)
  - [Introduction](#introduction)
    - [Quality of Life Suggestions](#quality-of-life-suggestions)
  - [Dealing With Failures](#dealing-with-failures)
  - [Adding a Test](#adding-a-test)
    - [Promoting Test Output](#promoting-test-output)
    - [Output Test Example](#output-test-example)
  - [Running Single Tests](#running-single-tests)
  - [Running Multiple Tests](#running-multiple-tests)
  - [Running Single Tests Without Rebuilding Deps](#running-single-tests-without-rebuilding-deps)
  - [Running Single Tests With Backtrace](#running-single-tests-with-backtrace)
  - [Rule Generation](#rule-generation)
  - [Unit Tests](#unit-tests)
  - [Complexity Tests](#complexity-tests)
  - [Output Modulo Time Tests](#output-modulo-time-tests)
  - [Misc Tests](#misc-tests)
  - [Updating the csdp Cache](#updating-the-csdp-cache)
  - [Cram Tests](#cram-tests)

## Introduction

The test suite can be run from the Coq root directory by running `make test`.
This does two things:
  1. Run `make duneteststrap` to generate the `.vo` rules for the repo.
  2. Run `dune test` to build all the testing targets.

The test suite is incremental meaning that you do not have to build the rest of
the repository in order to run it. You may also run it after hacking on some
files and Dune will rebuild only what is necessary.

`dune test` is very flexible. For instance, you can build all the test targets
in a certain subdirectory by running `dune test test-suite/bugs`. `dune test` is
really just `dune build @runtest` with some convenient features.

### Quality of Life Suggestions

Here are a few quality of life suggestions:

+ Run `make test-replay` to see the outputs of all the failing tests.

+ The option `--always-show-command-line` can be very useful since Dune will
  dump a subshell command that you can run to reproduce the failing test
  command. Remember to remove any log file redirects to see the output.

+ Passing `--display=short` to `dune` (or `DUNEOPT="--display=short"` for make).
  This will display every process that Dune is running at a given time.

## Dealing With Failures

When a test fails in the test-suite, it will give an output like:
```sh
File "test-suite/dune", line 160971, characters 1-330:
160971 |  (rule
160972 |   (alias runtest)
160973 |   (targets Nat.vo
........
160980 |         ../modules/Nat.v)
160981 |   (action
160982 |    (with-outputs-to Nat.v.log (run %{bin:coqc} -R .. Mods Nat.v))))
Command exited with code 1.
```
This is because the generated Dune rule has failed. In order to see the actual
error message you have three choices:

1. Use the `@*.debug` alias. Simply run `dune build @Nat.debug`. This will rerun
   the tests run by `dune build @Nat` and show stderr in the console together
   with a backtrace.

2. Run `make test-replay` to see the output of all the failing tests. This will
   run a shell script rerunning all the failing commands.

3. Use the output of `--always-show-command-line` and rerun the shell command
   manually.

```sh
$ dune build @Nat.debug
File "test-suite/dune", line 161000, characters 1-291:
161000 |  (rule
161001 |   (alias Nat.debug)
161002 |   (deps %{bin:coqtacticworker.opt}
161003 |         %{bin:coqproofworker.opt}
161004 |         %{bin:coqqueryworker.opt}
161005 |         ../../theories/Init/Prelude.vo
161006 |         ../modules/Nat.v)
161007 |   (action
161008 |    (run %{bin:coqc} -bt -R .. Mods
161009 |     Nat_debug_f63227d67eca844cbf7b40e6a4d45f04.v)))
cannot guess a path for Coq libraries; please use -coqlib option or ensure you have installed the package containing Coq's stdlib (coq-stdlib in OPAM) If you intend to use Coq without a standard library, the -boot -noinit options must be used.
```

If a failure is due to a missing dependency for a test, make sure you ran `make
dunestrap` so that the test-suite rules are fresh. If it still doesn't work,
open an issue or complain on Zulip.

## Adding a Test

For simple tests, placing the new `.v` file in the correct directory will be
enough. If the test expects an output, a file `test.out` should provided for the
file `test.v`. The `.out` file can be omitted for the time being, and the
correct output generated using `dune promote`. See [Promoting test
output](#promoting-test-output).

### Promoting Test Output

If the ouput of a test does not match the expected output, Dune will report the
diff. You can use `make promote` in order to promote all the actual output files
form the `_build` directory to be the expected output.

 To have finer control, use `dune promote` on a specific target such as
 ```sh
 dune promote test-suite/bugs/mybug.out
 ```

### Output Test Example

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
and rerun `make test`. Now Dune will complain that the output is different:
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
Finally when running `make test`, Dune will report no problems.

## Running Single Tests

All tests output targets such as .vo files or .log files. You can tell Dune to
build these targets directly. For example:

```sh
dune build test-suite/bugs/bug_1446.vo
```

However this is not ideal, since it requires you to know exactly where the test
is located and at least one of the targets it is expected to produce.

To remedy this, the test-suite will provide a *Dune alias* for each of the `.v`
file tests. Simply write:

```sh
dune build @bug_1446
```

to run the test directly. Note the dropping of the ".v" file suffix. You can of
course build multiple aliases too.

Currently only the `.v` file tests have support for aliases. Most of the other
shell tests do not yet have support. There is no reason for this, it is just a
matter of adding the alias generation where needed. See the generation for misc
tests for an example of aliases on non-v file tests.

## Running Multiple Tests

You can run all the tests appearing in a specific directory if you build the
directory directly. For example, to run all the tests in `test-suite/bugs` you
can do:

```sh
dune build test-suite/bugs
```

This will build all the targets appearing in that directory. As stated above,
you can build multiple targets by listing them out in `dune build`:

```sh
dune build @test1 @test2 test-suite/some-other-tests
```

## Running Single Tests Without Rebuilding Deps

You can run a test without compiling its dependencies simply by running:

```sh
dune build @DiscrR.replay
```

This is almost identical to `dune build @DiscrR` which will run a test called
`success/DiscrR.v` except that the dependencies and targets of the test are left
out. This allows for the quick rerunning of tests if you are absolutely sure
that the .vo dependencies do not need to be rebuilt.

## Running Single Tests With Backtrace

You can run a test `@test1` and show an error together with a backtrace by using
the `@test1.debug` alias.

```sh
dune build @test1.debug
```

This is especially useful since when a test fails, Dune will only report its
exit code and a snippet of the Dune rule. In order to see the actual error use
`@test1.debug`.

## Rule Generation

The rule generation code for all tests excluding Unit and Cram tests can be
found in `test-suite/tools/gen_rules`.

This tool consists of 3 main files:

- `gen_rules.ml`: Rule generation for the test-suite
- `coq_rules.ml`: Coq specific rule generation
- `dune.ml`: Generic Dune rule generation

 All the specific test styles with their dependencies are specified in
 `gen_rules.ml`. The `Makefile` will run the rule generation binary which will
 output a file called `test_suite_rules.sexp`. This file is then included in
 `test-suite/dune` (via an include stanza).

## Unit Tests

Unit tests can be found in `test-suite/unit-tests` and have their own rule
generation. Each of the subdirectories of `unit-tests` is linked with a
particular OCaml library and tested using a wrapper based on OUnit.

## Complexity Tests

When on Linux, gen_rules will generate rules for running complexity tests which
consist of timing the compilation of a `.v` file against some timing estimate.
These can be found in `test-suite/complexity`.

On slow computers this estimate may not be enough causing the test to fail.

## Output Modulo Time Tests

These tests check the output of ltac profiling and scrub the times from the
output using a script `test-suite/tools/modulo-time-output-log.sh`. The outputs
of these tests look weird, but that is because they have already been scrubbed.

For example:

```
total time:      0.922s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─abstract (sleep; constructor) ---------   0.0% 100.0%       1    0.922s
─sleep' -------------------------------- 100.0% 100.0%       1    0.922s
─constructor ---------------------------   0.0%   0.0%       1    0.000s
─sleep ---------------------------------   0.0%   0.0%       0    0.000s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─abstract (sleep; constructor) ---------   0.0% 100.0%       1    0.922s
 ├─sleep' ------------------------------ 100.0% 100.0%       1    0.922s
 ├─constructor -------------------------   0.0%   0.0%       1    0.000s
 └─sleep -------------------------------   0.0%   0.0%       0    0.000s
  └sleep' ------------------------------   0.0%   0.0%       0    0.000s
```

gets turned into

```
abstract (sleep; constructor) ---------%%       1s
abstract (sleep; constructor) ---------%%       1s
constructor -------------------------%%       1s
constructor ---------------------------%%       1s
sleep -------------------------------%%       0s
sleep ---------------------------------%%       0s
sleep' ------------------------------%%       0s
sleep' ------------------------------%%       1s
sleep' --------------------------------%%       1s
tactic                                   local  total   calls       max
tactic                                   local  total   calls       max
total time:s

```

## Misc Tests

The tests in `test-suite/misc` are expected to have a `.sh` with the test name
and optionally a directory of the same name with additional resources. The `.sh`
script will be able to run arbitrary shell (currently BASH) scripts.

In the future these may be converted to cram tests for reliability and more
platform support.

## Updating the csdp Cache

Tests in the `test-suite/micromega` directory and elsewhere rely on a common
`.csdp.cache` to run. There is a copy of this cache in the test-suite called
`.csdp.cache.test-suite`. When tests depending on the cache are run, Dune will
copy the `.csdp.cache.test-suite` into the `_build/default/test-suite` directory
for usage under the name `.csdp.cache`. There is some special Dune hackery to
make sure that this copy is also writable.

If the .csdp.cache needs to be updated, then it simply needs to be copied:
```sh
cp _build/default/test-suite/.csdp.cache test-suite/.csdp.cache.test-suite
```

---

## Cram Tests
TODO: There are currently no Cram tests in the repo. Update the documentation
here when they are added.
