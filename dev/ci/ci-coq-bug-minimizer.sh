#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

coq_bug_minimizer_CI_DIR=${CI_BUILD_DIR}/coq-bug-minimizer

# Setup coq-bug-minimizer

git_checkout ${coq_bug_minimizer_CI_BRANCH} ${coq_bug_minimizer_CI_GITURL} ${coq_bug_minimizer_CI_DIR}

( cd ${coq_bug_minimizer_CI_DIR} && make check CAT_ALL_LOGS=1 )
