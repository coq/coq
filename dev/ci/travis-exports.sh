#!/usr/bin/env bash

function fold-start {
    echo -en "travis_fold:start:$2\\r"
    echo "$1"
}

function fold-end {
    echo -en "travis_fold:end:$2\\r"
    echo "$1"
}

function get-artifact-coq-with-fallback {
    dev/ci/build.sh
}
