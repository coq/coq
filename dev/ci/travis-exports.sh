#!/usr/bin/env bash

if [ -f ~/.megarc ];
then
    HASMEGA=true
else
    HASMEGA=false
fi

function fold-start {
    echo -en "travis_fold:start:$2\\r"
    echo "$1"
}

function fold-end {
    echo -en "travis_fold:end:$2\\r"
    echo "$1"
}

# CONSIDER this is fast so maybe we should always do it instead of
# having it in the middle of the build
function setup-mega {
    fold-start "Installing megatools..." "mega.install"

    wget http://megatools.megous.com/builds/megatools-1.9.97.tar.gz
    zcat megatools-1.9.97.tar.gz > megatools-1.9.97.tar
    tar -xf megatools-1.9.97.tar
    pushd megatools-1.9.97
    ./configure
    make
    sudo make install
    popd

    fold-end "megatools installed." "mega.install"
}

function get-artifact-coq-with-fallback {
    if $HASMEGA;
    then
        setup-mega

        fold-start "Getting Coq from mega..." "mega.get"
        FILE="Coq-travis-${COMPILER}-${TRAVIS_BUILD_ID}.zip"
        megaget "/Root/$FILE"
        unzip "$FILE"
        fold-end "Coq received." "mega.get"
    else
        dev/ci/build.sh
    fi
}

function save-artifact-coq {
    if $HASMEGA;
    then
        setup-mega

        FILE="Coq-travis-${COMPILER}-${TRAVIS_BUILD_ID}.zip"

        # do not use "$CI_INSTALL" here, we need a relative path
        zip -r "$FILE" coq-install config/Makefile

        megaput "$FILE"
    fi
}
