#!/usr/bin/env bash

# setup common ci things

set -ex

if [ -n "${GITLAB_CI}" ];
then
    source dev/ci/gitlab-setup.sh
elif [ -n "${TRAVIS}" ];
then
    source dev/ci/travis-setup.sh
else
    >&2 echo "Unknown CI kind."
    printenv
    exit 1
fi

eval $(opam config env)

ls
printenv

opam config list

opam install -j ${NJOBS} -y camlp5.${CAMLP5_VER} ocamlfind ${EXTRA_OPAM}
rm -rf ~/.opam/log/

opam list
