#!/usr/bin/env bash

set -ex
# TODO figure out how to cleanly combine this with ci-common

eval $(opam config env)

ls -a
printenv

if [ -n "${GITLAB_CI}" ];
then
    source dev/ci/gitlab-exports.sh
elif [ -n "${TRAVIS}" ];
then
    source dev/ci/travis-exports.sh
else
    >&2 echo "Unknown CI kind."
    printenv
    exit 1
fi

export CI_INSTALL="$(pwd)/coq-install"
