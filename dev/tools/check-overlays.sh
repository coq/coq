#!/usr/bin/env bash

REDBOLD="\033[31;1m"
RESET="\033[0m"

function redprint
{
  if [ "$COQ_CI_COLOR" ]; then
    printf "$REDBOLD%s$RESET\n" "$1"
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
