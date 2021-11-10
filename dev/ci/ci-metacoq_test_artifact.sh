#!/usr/bin/env bash

set -e

# this dummy file exists only so that we have a script to run for
# ci-metacoq_test_artifact.  This CI target is really only present to
# ensure that running the ci-metacoq script again in the artifact in
# fact installs the code, ideally without rebuilding it, which is
# necessary for the bug minimizer to be able to minimize metacoq
