#!/usr/bin/env bash

RED="\033[31m"
RESET="\033[0m"

function redprint
{
  if [ -t 1 ] && ! [ "$TERM" = dumb ]; then
    printf "$RED%s$RESET\n" "$1"
  else
    printf '%s\n' "$1"
  fi
}

for f in $(git ls-files "dev/ci/user-overlays/")
do
    if ! { [[ "$f" = dev/ci/user-overlays/README.md ]] || [[ "$f" == *.sh ]]; }
    then
        >&2 redprint "Bad overlay '$f'."
        >&2 echo "User overlays need to have extension .sh to be picked up!"
        exit 1
    fi
done
