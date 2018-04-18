#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

stdpp_CI_DIR="${CI_BUILD_DIR}/coq-stdpp"
Iris_CI_DIR="${CI_BUILD_DIR}/iris-coq"
lambdaRust_CI_DIR="${CI_BUILD_DIR}/lambdaRust"

install_ssreflect

# Setup lambdaRust first
git_checkout "${lambdaRust_CI_BRANCH}" "${lambdaRust_CI_GITURL}" "${lambdaRust_CI_DIR}"

# Extract required version of Iris
Iris_SHA=$(grep -F coq-iris < "${lambdaRust_CI_DIR}/opam" | sed 's/.*"dev\.[0-9.-]\+\.\([0-9a-z]\+\)".*/\1/')

# Setup Iris
git_checkout "${Iris_CI_BRANCH}" "${Iris_CI_GITURL}" "${Iris_CI_DIR}" "${Iris_SHA}"

# Extract required version of std++
stdpp_SHA=$(grep -F coq-stdpp < "${Iris_CI_DIR}/opam" | sed 's/.*"dev\.[0-9.-]\+\.\([0-9a-z]\+\)".*/\1/')

# Setup std++
git_checkout "${stdpp_CI_BRANCH}" "${stdpp_CI_GITURL}" "${stdpp_CI_DIR}" "${stdpp_SHA}"

# Build std++
( cd "${stdpp_CI_DIR}" && make && make install )

# Build and validate (except on Travis, i.e., skip if TRAVIS is non-empty) Iris
( cd "${Iris_CI_DIR}" && make && (test -n "${TRAVIS}" || make validate) && make install )

# Build lambdaRust
( cd "${lambdaRust_CI_DIR}" && make && make install )
