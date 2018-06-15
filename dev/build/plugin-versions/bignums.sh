#!/bin/sh
case "$1" in
    git-master|/cygdrive*)
        # First get the SHA of master/HEAD and then download a zip of exactly this state
        BIGNUMS_SHA=$(git ls-remote 'https://github.com/coq/bignums' refs/heads/master | cut -f 1)

        echo https://github.com/coq/bignums/archive "$BIGNUMS_SHA" zip 1 "bignums-$BIGNUMS_SHA"
        ;;
    *)
        echo https://github.com/coq/bignums/archive V8.8.0 zip 1 bignums-V8.8+beta1
        ;;
esac
