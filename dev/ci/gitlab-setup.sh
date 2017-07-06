#!/usr/bin/env bash

# setup gitlab only things

set -ex

# travis uses the apt addon
# gitlab has a docker image with opam preloaded so doesn't always need to install things
if [ -n "${EXTRA_PACKAGES}" ];
then
    sudo apt-get update -qq
    sudo apt-get install -y -qq ${EXTRA_PACKAGES}
fi

# gitlab can only cache subdirectories
if [ ! "(" -f .opamcache/config ")" ];
then mv ~/.opam .opamcache
else mv ~/.opam ~/.opam-old # faster than [rm -rf] (?)
fi
ln -s $(readlink -f .opamcache) ~/.opam

# since opam comes with docker we con't start the same as travis
opam switch -j ${NJOBS} ${COMPILER}
