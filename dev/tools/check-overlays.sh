#!/usr/bin/env bash

for f in $(git ls-files "dev/ci/user-overlays/")
do
    if ! ([[ "$f" = dev/ci/user-overlays/README.md ]] || [[ "$f" == *.sh ]])
    then
        >&2 echo "Bad overlay '$f'."
        >&2 echo "User overlays need to have extension .sh to be picked up!"
        exit 1
    fi
done
