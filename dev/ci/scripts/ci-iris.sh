#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download iris_examples

# Extract required version of Iris (avoiding "+" which does not work on MacOS :( *)
iris_CI_REF=$(grep -F '"coq-iris-heap-lang"' < "${CI_BUILD_DIR}/iris_examples/coq-iris-examples.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
[ -n "$iris_CI_REF" ] || { echo "Could not find Iris dependency version" && exit 1; }

# Download Iris
git_download iris

# Extract required version of std++
stdpp_CI_REF=$(grep -F '"coq-stdpp"' < "${CI_BUILD_DIR}/iris/coq-iris.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
[ -n "$stdpp_CI_REF" ] || { echo "Could not find stdpp dependency version" && exit 1; }

# Download std++
git_download stdpp

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

# Build

( cd "${CI_BUILD_DIR}/stdpp"
  make
  make install
)

( cd "${CI_BUILD_DIR}/iris"
  make
  make validate
  make install
)

( cd "${CI_BUILD_DIR}/iris_examples"
  make
  make install
)
