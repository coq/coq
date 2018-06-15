#!/bin/sh
case "$1" in
    git-master|/cygdrive*)
        # First get the SHA of master/HEAD and then download a zip of exactly this state
        EQUATIONS_SHA=$(git ls-remote 'https://github.com/mattam82/Coq-Equations' refs/heads/master | cut -f 1)

        echo https://github.com/mattam82/Coq-Equations/archive "$EQUATIONS_SHA" zip 1 "equations-$EQUATIONS_SHA"
        ;;
    *)
        echo https://github.com/mattam82/Coq-Equations/archive v1.1-8.8 zip 1 equations-v1.1-8.8
        ;;
esac
