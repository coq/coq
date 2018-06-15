#!/bin/sh
case "$1" in
    git-master|/cygdrive*)
        # First get the SHA of master/HEAD and then download a zip of exactly this state
        LTAC2_SHA=$(git ls-remote 'https://github.com/ppedrot/ltac2' refs/heads/master | cut -f 1)

        echo https://github.com/ppedrot/ltac2/archive "$LTAC2_SHA" zip 1 "ltac2-$LTAC2_SHA"
        ;;
    *)
        echo https://github.com/ppedrot/ltac2/archive v8.8 zip 1 ltac2-v8.8
        ;;
esac
