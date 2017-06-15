#!/usr/bin/env bash

# gitlab doesn't have folding
function fold-start {
    echo "$1"
    echo "start:$2"
}

function fold-end {
    echo "$1"
    echo "end:$2"
}

# dummy since gitlab always has artifacts
function get-artifact-coq-with-fallback {
    :
}
