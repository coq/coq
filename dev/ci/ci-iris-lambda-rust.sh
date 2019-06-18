#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

install_ssreflect

# Setup lambdaRust first
git_download lambdaRust

# Extract required version of Iris (avoiding "+" which does not work on MacOS :( *)
Iris_CI_REF=$(grep -F coq-iris < "${CI_BUILD_DIR}/lambdaRust/opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')

# Setup Iris
git_download Iris

# Extract required version of std++
stdpp_CI_REF=$(grep -F coq-stdpp < "${CI_BUILD_DIR}/Iris/opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')

# Setup std++
git_download stdpp

# Build std++
( cd "${CI_BUILD_DIR}/stdpp" && make && make install )

# Build and validate Iris
( cd "${CI_BUILD_DIR}/Iris" && make && make validate && make install )

# Build lambdaRust
( cd "${CI_BUILD_DIR}/lambdaRust" && make && make install )
