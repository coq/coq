#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

# Setup iris_examples and separate dependencies first
git_download autosubst
git_download iris_string_ident
git_download iris_examples

# Extract required version of Iris (avoiding "+" which does not work on MacOS :( *)
iris_CI_REF=$(grep -F '"coq-iris-heap-lang"' < "${CI_BUILD_DIR}/iris_examples/coq-iris-examples.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
[ -n "$iris_CI_REF" ] || { echo "Could not find Iris dependency version" && exit 1; }

# Setup Iris
git_download iris

# Extract required version of std++
stdpp_CI_REF=$(grep -F '"coq-stdpp"' < "${CI_BUILD_DIR}/iris/coq-iris.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
[ -n "$stdpp_CI_REF" ] || { echo "Could not find stdpp dependency version" && exit 1; }

# Setup std++
git_download stdpp

# Build std++
( cd "${CI_BUILD_DIR}/stdpp" && make && make install )

# Build and validate Iris
( cd "${CI_BUILD_DIR}/iris" && make && make validate && make install )

# Build autosubst
( cd "${CI_BUILD_DIR}/autosubst" && make && make install )

# Build iris-string-ident
( cd "${CI_BUILD_DIR}/iris_string_ident" && make && make install )

# Build Iris examples
( cd "${CI_BUILD_DIR}/iris_examples" && make && make install )
